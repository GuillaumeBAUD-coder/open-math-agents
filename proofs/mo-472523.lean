import OMAStatements.S_mo_472523

namespace OMA.S_mo_472523_Proof

open OMA.S_mo_472523

section Part1

private lemma pow_mul_sub_fact_le_two (k s : ℕ) (h : 2 * s ≤ k) :
    k ^ s * (k - s).factorial ≤ 2 ^ s * k.factorial := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hs : 2 * s ≤ k := by omega
    have hih := ih hs
    have hsub : k - s = (k - (s + 1)) + 1 := by omega
    have hfac : (k - s).factorial = (k - s) * (k - (s + 1)).factorial := by
      rw [hsub, Nat.factorial_succ]
    have hk2 : k ≤ 2 * (k - s) := by omega
    calc
      k ^ (s + 1) * (k - (s + 1)).factorial
          = k * (k ^ s * (k - (s + 1)).factorial) := by ring
      _ ≤ 2 * (k - s) * (k ^ s * (k - (s + 1)).factorial) :=
          Nat.mul_le_mul_right _ hk2
      _ = 2 * (k ^ s * ((k - s) * (k - (s + 1)).factorial)) := by ring
      _ = 2 * (k ^ s * (k - s).factorial) := by rw [← hfac]
      _ ≤ 2 * (2 ^ s * k.factorial) := Nat.mul_le_mul_left 2 hih
      _ = 2 ^ (s + 1) * k.factorial := by ring

private lemma pow_self_le_three_pow_mul_fact (s : ℕ) :
    s ^ s ≤ 3 ^ s * s.factorial := by
  have hsum : ∑ i ∈ Finset.range (s + 1), ((s : ℝ) ^ i / (i.factorial : ℝ)) ≤ Real.exp (s : ℝ) :=
    Real.sum_le_exp_of_nonneg (Nat.cast_nonneg s) (s + 1)
  have hmem : s ∈ Finset.range (s + 1) := Finset.mem_range.mpr (Nat.lt_succ_self s)
  have hsingle : (s : ℝ) ^ s / (s.factorial : ℝ) ≤
      ∑ i ∈ Finset.range (s + 1), ((s : ℝ) ^ i / (i.factorial : ℝ)) :=
    Finset.single_le_sum (f := fun i => (s : ℝ) ^ i / (i.factorial : ℝ))
      (fun i _ => by positivity) hmem
  have hexp1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hexps : Real.exp (s : ℝ) ≤ (3 : ℝ) ^ s := by
    have h1 : Real.exp (s : ℝ) = (Real.exp 1) ^ s := by
      rw [← Real.exp_nat_mul, mul_one]
    rw [h1]
    exact pow_le_pow_left₀ (Real.exp_nonneg 1) hexp1 s
  have hdiv : (s : ℝ) ^ s / (s.factorial : ℝ) ≤ (3 : ℝ) ^ s :=
    le_trans (le_trans hsingle hsum) hexps
  have hfac_pos : (0 : ℝ) < (s.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos s)
  have hreal : (s : ℝ) ^ s ≤ (3 : ℝ) ^ s * (s.factorial : ℝ) :=
    (div_le_iff₀ hfac_pos).mp hdiv
  exact_mod_cast hreal

private lemma pow_mul_sub_fact_le_six (k s : ℕ) (hs : s ≤ k) :
    k ^ s * (k - s).factorial ≤ 6 ^ s * k.factorial := by
  by_cases h : 2 * s ≤ k
  · calc
      k ^ s * (k - s).factorial ≤ 2 ^ s * k.factorial := pow_mul_sub_fact_le_two k s h
      _ ≤ 6 ^ s * k.factorial := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) s)
  · have hk2s : k ≤ 2 * s := by omega
    have hchoose : 1 ≤ Nat.choose k s := Nat.choose_pos hs
    have hfac : s.factorial * (k - s).factorial ≤ k.factorial := by
      have hmul := Nat.choose_mul_factorial_mul_factorial hs
      calc
        s.factorial * (k - s).factorial
            = 1 * (s.factorial * (k - s).factorial) := by ring
        _ ≤ Nat.choose k s * (s.factorial * (k - s).factorial) :=
            Nat.mul_le_mul_right _ hchoose
        _ = k.factorial := by linarith
    have hss := pow_self_le_three_pow_mul_fact s
    calc
      k ^ s * (k - s).factorial
          ≤ (2 * s) ^ s * (k - s).factorial :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hk2s s)
      _ = 2 ^ s * (s ^ s * (k - s).factorial) := by rw [mul_pow]; ring
      _ ≤ 2 ^ s * ((3 ^ s * s.factorial) * (k - s).factorial) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hss)
      _ = 6 ^ s * (s.factorial * (k - s).factorial) := by
          have h6 : (6 : ℕ) ^ s = 2 ^ s * 3 ^ s := by rw [← mul_pow] ; norm_num
          rw [h6]; ring
      _ ≤ 6 ^ s * k.factorial := Nat.mul_le_mul_left _ hfac

private lemma extensions_le_total {n k : ℕ} {E : Finset (Finset (Fin n))}
    (T : Finset E) (p : T → Fin k) :
    extensions T p ≤ total E k := by
  unfold extensions total
  refine Nat.card_le_card_of_injective
    (fun x : {f : E → Fin k // Proper f ∧ ∀ e : T, f e.val = p e} =>
      (⟨x.val, x.prop.1⟩ : {f : E → Fin k // Proper f})) ?_
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : {f : E → Fin k // Proper f} => z.val) hxy

private noncomputable def adjEdges {n : ℕ} (E : Finset (Finset (Fin n))) (e : E) :
    Finset (Finset (Fin n)) :=
  E.filter (fun e' => e' ≠ e.val ∧ ¬ Disjoint e.val e')

private lemma card_adj_inter_le_four {n : ℕ} {E : Finset (Finset (Fin n))}
    (hE : ∀ e ∈ E, e.card = 2) (e₁ e₂ : E) (hd : Disjoint e₁.val e₂.val) :
    (adjEdges E e₁ ∩ adjEdges E e₂).card ≤ 4 := by
  classical
  let img : Finset (Finset (Fin n)) :=
    (e₁.val ×ˢ e₂.val).image (fun q => ({q.1, q.2} : Finset (Fin n)))
  have hsub : adjEdges E e₁ ∩ adjEdges E e₂ ⊆ img := by
    intro e' he'
    simp only [Finset.mem_inter, adjEdges, Finset.mem_filter] at he'
    rcases he' with ⟨⟨he'E, _, hnd1⟩, ⟨_, _, hnd2⟩⟩
    obtain ⟨u, hu1, hu'⟩ := Finset.not_disjoint_iff.mp hnd1
    obtain ⟨v, hv2, hv'⟩ := Finset.not_disjoint_iff.mp hnd2
    have huv : u ≠ v := fun h => Finset.disjoint_left.mp hd hu1 (h ▸ hv2)
    have hpair_sub : ({u, v} : Finset (Fin n)) ⊆ e' := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl <;> assumption
    have hpair_card : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair huv
    have he'_card : e'.card = 2 := hE e' he'E
    have heq : ({u, v} : Finset (Fin n)) = e' :=
      Finset.eq_of_subset_of_card_le hpair_sub (by omega)
    exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨hu1, hv2⟩, heq⟩
  calc
    (adjEdges E e₁ ∩ adjEdges E e₂).card ≤ img.card := Finset.card_le_card hsub
    _ ≤ (e₁.val ×ˢ e₂.val).card := Finset.card_image_le
    _ = e₁.val.card * e₂.val.card := Finset.card_product _ _
    _ = 2 * 2 := by rw [hE e₁.val e₁.prop, hE e₂.val e₂.prop]
    _ = 4 := by norm_num

private lemma no_disjoint_of_high_adj {n k : ℕ} {E : Finset (Finset (Fin n))}
    (hE : ∀ e ∈ E, e.card = 2) (hmk : 6 * E.card ≤ 7 * k) (hk : 13 ≤ k)
    (e₁ e₂ : E) (hne : e₁ ≠ e₂)
    (h1 : 2 * k + 1 ≤ 3 * (adjEdges E e₁).card)
    (h2 : 2 * k + 1 ≤ 3 * (adjEdges E e₂).card) :
    ¬ Disjoint e₁.val e₂.val := by
  classical
  intro hd
  let pair : Finset (Finset (Fin n)) := {e₁.val, e₂.val}
  let U : Finset (Finset (Fin n)) := adjEdges E e₁ ∪ adjEdges E e₂
  have hsub : pair ∪ U ⊆ E := by
    intro x hx
    simp only [pair, U, adjEdges, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_filter] at hx
    rcases hx with (rfl | rfl) | (⟨hxE, _⟩ | ⟨hxE, _⟩)
    · exact e₁.prop
    · exact e₂.prop
    · exact hxE
    · exact hxE
  have hdisj : Disjoint pair U := by
    rw [Finset.disjoint_left]
    intro x hxp hxU
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hxp
    simp only [U, adjEdges, Finset.mem_union, Finset.mem_filter] at hxU
    rcases hxp with rfl | rfl
    · rcases hxU with ⟨_, hne1, _⟩ | ⟨_, _, hnd⟩
      · exact hne1 rfl
      · exact hnd hd.symm
    · rcases hxU with ⟨_, _, hnd⟩ | ⟨_, hne2, _⟩
      · exact hnd hd
      · exact hne2 rfl
  have hpair_card : pair.card = 2 := Finset.card_pair (fun h => hne (Subtype.ext h))
  have hleE : 2 + U.card ≤ E.card := by
    have h1' := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, hpair_card] at h1'
    exact h1'
  have hu_inter : U.card + (adjEdges E e₁ ∩ adjEdges E e₂).card =
      (adjEdges E e₁).card + (adjEdges E e₂).card :=
    Finset.card_union_add_card_inter _ _
  have hinter : (adjEdges E e₁ ∩ adjEdges E e₂).card ≤ 4 :=
    card_adj_inter_le_four hE e₁ e₂ hd
  omega

private lemma recolor_step {n k : ℕ} {E : Finset (Finset (Fin n))}
    (T : Finset E) (p : T → Fin k) (e : E) (he : e ∈ T) :
    (k - (adjEdges E e).card) * extensions T p ≤
      extensions (T.erase e) (fun x => p ⟨x.val, Finset.mem_of_mem_erase x.prop⟩) := by
  classical
  let T' : Finset E := T.erase e
  let p' : T' → Fin k := fun x => p ⟨x.val, Finset.mem_of_mem_erase x.prop⟩
  let A := {f : E → Fin k // Proper f ∧ ∀ x : T, f x.val = p x}
  let B := {g : E → Fin k // Proper g ∧ ∀ x : T', g x.val = p' x}
  let adjSub : Finset E := E.attach.filter (fun e' => e' ≠ e ∧ ¬ Disjoint e.val e'.val)
  have hadj_card : adjSub.card = (adjEdges E e).card := by
    have hbij : adjSub.image Subtype.val = adjEdges E e := by
      ext x
      simp only [adjSub, adjEdges, Finset.mem_image, Finset.mem_filter,
        Finset.mem_attach, true_and]
      constructor
      · rintro ⟨⟨y, hy⟩, ⟨hne, hnd⟩, rfl⟩
        exact ⟨hy, fun h => hne (Subtype.ext h), hnd⟩
      · rintro ⟨hxE, hne, hnd⟩
        exact ⟨⟨x, hxE⟩, ⟨fun h => hne (congrArg Subtype.val h), hnd⟩, rfl⟩
    rw [← hbij, Finset.card_image_of_injective _ Subtype.val_injective]
  let avail : A → Finset (Fin k) := fun f => Finset.univ \ (adjSub.image f.val)
  have havail_card : ∀ f : A, k - (adjEdges E e).card ≤ (avail f).card := by
    intro f
    have h1 : (avail f).card = k - (adjSub.image f.val).card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    have h2 : (adjSub.image f.val).card ≤ (adjEdges E e).card := by
      rw [← hadj_card]
      exact Finset.card_image_le
    omega
  let Φ : (Σ f : A, {a : Fin k // a ∈ avail f}) → B := fun ⟨f, a⟩ =>
    ⟨Function.update f.val e a.val, by
      constructor
      · intro e₁ e₂ hne hnd
        by_cases h1 : e₁ = e
        · subst h1
          have h2 : e₂ ≠ e₁ := hne.symm
          rw [Function.update_self, Function.update_of_ne h2]
          intro heq
          have hmem : e₂ ∈ adjSub := by
            simp only [adjSub, Finset.mem_filter, Finset.mem_attach, true_and]
            exact ⟨h2, hnd⟩
          have ha : a.val ∉ adjSub.image f.val := (Finset.mem_sdiff.mp a.prop).2
          exact ha (Finset.mem_image.mpr ⟨e₂, hmem, heq.symm⟩)
        · by_cases h2 : e₂ = e
          · subst h2
            rw [Function.update_self, Function.update_of_ne h1]
            intro heq
            have hmem : e₁ ∈ adjSub := by
              simp only [adjSub, Finset.mem_filter, Finset.mem_attach, true_and]
              exact ⟨h1, fun h => hnd h.symm⟩
            have ha : a.val ∉ adjSub.image f.val := (Finset.mem_sdiff.mp a.prop).2
            exact ha (Finset.mem_image.mpr ⟨e₁, hmem, heq⟩)
          · rw [Function.update_of_ne h1, Function.update_of_ne h2]
            exact f.prop.1 e₁ e₂ hne hnd
      · intro x
        have hxne : x.val ≠ e := (Finset.mem_erase.mp x.prop).1
        rw [Function.update_of_ne hxne]
        exact f.prop.2 ⟨x.val, Finset.mem_of_mem_erase x.prop⟩⟩
  have hΦ_inj : Function.Injective Φ := by
    rintro ⟨f₁, a₁⟩ ⟨f₂, a₂⟩ heq
    have hfun : Function.update f₁.val e a₁.val = Function.update f₂.val e a₂.val :=
      congrArg Subtype.val heq
    have ha : a₁.val = a₂.val := by
      have h := congrFun hfun e
      simpa using h
    have hf : f₁ = f₂ := by
      apply Subtype.ext
      funext x
      by_cases hx : x = e
      · subst hx
        rw [f₁.prop.2 ⟨x, he⟩, f₂.prop.2 ⟨x, he⟩]
      · have h := congrFun hfun x
        simpa [Function.update_of_ne hx] using h
    subst hf
    have ha' : a₁ = a₂ := Subtype.ext ha
    subst ha'
    rfl
  unfold extensions
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hle : Fintype.card (Σ f : A, {a : Fin k // a ∈ avail f}) ≤ Fintype.card B :=
    Fintype.card_le_of_injective Φ hΦ_inj
  rw [Fintype.card_sigma] at hle
  calc
    (k - (adjEdges E e).card) * Fintype.card A
        = ∑ _f : A, (k - (adjEdges E e).card) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    _ ≤ ∑ f : A, Fintype.card {a : Fin k // a ∈ avail f} := by
          apply Finset.sum_le_sum
          intro f _
          rw [Fintype.card_coe]
          exact havail_card f
    _ ≤ Fintype.card B := hle

private lemma perm_double_count {n k : ℕ} {E : Finset (Finset (Fin n))}
    (T : Finset E) (p : T → Fin k) (hp : Function.Injective p) :
    k.factorial * extensions T p ≤ (k - T.card).factorial * total E k := by
  classical
  let A := {f : E → Fin k // Proper f ∧ ∀ x : T, f x.val = p x}
  let B := {g : E → Fin k // Proper g}
  let C : Finset (Fin k) := Finset.univ.image p
  have hC_card : C.card = T.card := by
    rw [Finset.card_image_of_injective _ hp, Finset.card_univ, Fintype.card_coe]
  let Ψ : Equiv.Perm (Fin k) × A → B := fun ⟨σ, f⟩ =>
    ⟨fun e => σ (f.val e), by
      intro e₁ e₂ hne hnd heq
      exact f.prop.1 e₁ e₂ hne hnd (σ.injective heq)⟩
  have hfiber : ∀ g : B,
      (Finset.univ.filter (fun z : Equiv.Perm (Fin k) × A => Ψ z = g)).card ≤
        (k - T.card).factorial := by
    intro g
    let Fg := Finset.univ.filter (fun z : Equiv.Perm (Fin k) × A => Ψ z = g)
    change Fg.card ≤ (k - T.card).factorial
    by_cases hne : Fg.Nonempty
    · obtain ⟨⟨σ₀, f₀⟩, hmem₀⟩ := hne
      have hΨ₀ : Ψ (σ₀, f₀) = g := (Finset.mem_filter.mp hmem₀).2
      have hfix : ∀ (σ : Equiv.Perm (Fin k)) (f : A), Ψ (σ, f) = g →
          ∀ c ∈ C, (σ₀⁻¹ * σ) c = c := by
        intro σ f hΨ c hc
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc
        have h1 : σ (f.val x.val) = g.val x.val := congrFun (congrArg Subtype.val hΨ) x.val
        have h2 : σ₀ (f₀.val x.val) = g.val x.val := congrFun (congrArg Subtype.val hΨ₀) x.val
        rw [f.prop.2 x] at h1
        rw [f₀.prop.2 x] at h2
        rw [Equiv.Perm.mul_apply, h1, ← h2]
        exact σ₀.symm_apply_apply (p x)
      let restrictPerm : {z // z ∈ Fg} → Equiv.Perm {y : Fin k // y ∉ C} := fun ⟨⟨σ, f⟩, hz⟩ =>
        let τ : Equiv.Perm (Fin k) := σ₀⁻¹ * σ
        have hτ : ∀ c ∈ C, τ c = c := hfix σ f (Finset.mem_filter.mp hz).2
        have hτ_inv : ∀ c ∈ C, τ.symm c = c := by
          intro c hc
          apply τ.injective
          rw [τ.apply_symm_apply, hτ c hc]
        { toFun := fun ⟨y, hy⟩ => ⟨τ y, fun hmem => hy (by
            have h1 := hτ (τ y) hmem
            have heq := τ.injective h1
            rwa [heq] at hmem)⟩
          invFun := fun ⟨y, hy⟩ => ⟨τ.symm y, fun hmem => hy (by
            have h1 := hτ_inv (τ.symm y) hmem
            have heq := τ.symm.injective h1
            rwa [heq] at hmem)⟩
          left_inv := fun ⟨y, _⟩ => Subtype.ext (τ.symm_apply_apply y)
          right_inv := fun ⟨y, _⟩ => Subtype.ext (τ.apply_symm_apply y) }
      have hinj : Function.Injective restrictPerm := by
        rintro ⟨⟨σ₁, f₁⟩, hz₁⟩ ⟨⟨σ₂, f₂⟩, hz₂⟩ heq
        have hΨ₁ : Ψ (σ₁, f₁) = g := (Finset.mem_filter.mp hz₁).2
        have hΨ₂ : Ψ (σ₂, f₂) = g := (Finset.mem_filter.mp hz₂).2
        have hσ : σ₁ = σ₂ := by
          apply Equiv.ext
          intro y
          by_cases hy : y ∈ C
          · have h1 := hfix σ₁ f₁ hΨ₁ y hy
            have h2 := hfix σ₂ f₂ hΨ₂ y hy
            have h3 : (σ₀⁻¹ * σ₁) y = (σ₀⁻¹ * σ₂) y := h1.trans h2.symm
            exact σ₀.symm.injective h3
          · have h3 := congrArg (fun π => (π ⟨y, hy⟩).val) heq
            exact σ₀.symm.injective h3
        subst hσ
        have hf : f₁ = f₂ := by
          apply Subtype.ext
          funext e
          have h1 : σ₁ (f₁.val e) = g.val e := congrFun (congrArg Subtype.val hΨ₁) e
          have h2 : σ₁ (f₂.val e) = g.val e := congrFun (congrArg Subtype.val hΨ₂) e
          exact σ₁.injective (h1.trans h2.symm)
        subst hf
        rfl
      have hcard_le : Fg.card ≤ Fintype.card (Equiv.Perm {y : Fin k // y ∉ C}) := by
        rw [← Fintype.card_coe]
        exact Fintype.card_le_of_injective restrictPerm hinj
      rw [Fintype.card_perm] at hcard_le
      have hcompl : Fintype.card {y : Fin k // y ∉ C} = k - T.card := by
        have hc1 : Fintype.card {y : Fin k // y ∉ C} = (Finset.univ \ C).card := by
          rw [Fintype.card_subtype]
          congr 1
          ext y
          simp
        rw [hc1, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
          Fintype.card_fin, hC_card]
      rwa [hcompl] at hcard_le
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le _
  unfold extensions total
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hprod : k.factorial * Fintype.card A = Fintype.card (Equiv.Perm (Fin k) × A) := by
    rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
  rw [hprod]
  have hpart : Fintype.card (Equiv.Perm (Fin k) × A) =
      ∑ g : B, (Finset.univ.filter (fun z : Equiv.Perm (Fin k) × A => Ψ z = g)).card := by
    rw [← Finset.card_univ]
    have := Finset.card_eq_sum_card_fiberwise (f := Ψ)
      (s := (Finset.univ : Finset (Equiv.Perm (Fin k) × A)))
      (t := (Finset.univ : Finset B)) (fun _ _ => Finset.mem_univ _)
    exact this
  rw [hpart]
  calc
    ∑ g : B, (Finset.univ.filter (fun z => Ψ z = g)).card
        ≤ ∑ _g : B, (k - T.card).factorial := Finset.sum_le_sum (fun g _ => hfiber g)
    _ = (k - T.card).factorial * Fintype.card B := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

private lemma part1_core {n k : ℕ} {E : Finset (Finset (Fin n))}
    (hE : ∀ e ∈ E, e.card = 2) (hmk : 6 * E.card ≤ 7 * k) (hk : 13 ≤ k) :
    ∀ s : ℕ, ∀ (T : Finset E) (p : T → Fin k), T.card = s → 0 < extensions T p →
      ((1 / 12 : ℝ) * (k : ℝ)) ^ s * (extensions T p : ℝ) ≤ (total E k : ℝ) := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro T p hcard hpos
    by_cases hex : ∃ e ∈ T, 3 * (adjEdges E e).card ≤ 2 * k
    · rcases hex with ⟨e, heT, hadj⟩
      let T' : Finset E := T.erase e
      let p' : T' → Fin k := fun x => p ⟨x.val, Finset.mem_of_mem_erase x.prop⟩
      have hcard' : T'.card + 1 = s := by
        rw [← hcard]
        exact Finset.card_erase_add_one heT
      have hlt : T'.card < s := by omega
      have hstep := recolor_step T p e heT
      have hsub_le : k - (adjEdges E e).card ≥ 1 := by omega
      have hpos' : 0 < extensions T' p' := by
        have : 1 * extensions T p ≤ extensions T' p' :=
          le_trans (Nat.mul_le_mul_right _ hsub_le) hstep
        omega
      have hih := ih T'.card hlt T' p' rfl hpos'
      have hck_le : (1 / 12 : ℝ) * (k : ℝ) ≤ ((k - (adjEdges E e).card : ℕ) : ℝ) := by
        have hle_k : (adjEdges E e).card ≤ k := by omega
        rw [Nat.cast_sub hle_k]
        have hcast : (3 : ℝ) * ((adjEdges E e).card : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hadj
        linarith
      have hstepR : ((k - (adjEdges E e).card : ℕ) : ℝ) * (extensions T p : ℝ) ≤
          (extensions T' p' : ℝ) := by exact_mod_cast hstep
      have hmul : ((1 / 12 : ℝ) * (k : ℝ)) * (extensions T p : ℝ) ≤ (extensions T' p' : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_right hck_le (Nat.cast_nonneg _)) hstepR
      have hpow_nonneg : (0 : ℝ) ≤ ((1 / 12 : ℝ) * (k : ℝ)) ^ T'.card := by positivity
      calc
        ((1 / 12 : ℝ) * (k : ℝ)) ^ s * (extensions T p : ℝ)
            = ((1 / 12 : ℝ) * (k : ℝ)) ^ (T'.card + 1) * (extensions T p : ℝ) := by rw [hcard']
        _ = ((1 / 12 : ℝ) * (k : ℝ)) ^ T'.card *
              (((1 / 12 : ℝ) * (k : ℝ)) * (extensions T p : ℝ)) := by rw [pow_succ]; ring
        _ ≤ ((1 / 12 : ℝ) * (k : ℝ)) ^ T'.card * (extensions T' p' : ℝ) :=
            mul_le_mul_of_nonneg_left hmul hpow_nonneg
        _ ≤ (total E k : ℝ) := hih
    · push Not at hex
      have hnodisj : ∀ e₁ ∈ T, ∀ e₂ ∈ T, e₁ ≠ e₂ → ¬ Disjoint e₁.val e₂.val := by
        intro e₁ he₁ e₂ he₂ hne
        exact no_disjoint_of_high_adj hE hmk hk e₁ e₂ hne (hex e₁ he₁) (hex e₂ he₂)
      have hne_ext : Nonempty {f : E → Fin k // Proper f ∧ ∀ x : T, f x.val = p x} :=
        Nat.card_pos_iff.mp hpos |>.1
      obtain ⟨⟨f₀, hf₀_prop, hf₀_ext⟩⟩ := hne_ext
      have hp_inj : Function.Injective p := by
        intro x₁ x₂ heq
        by_contra hne
        have hval_ne : x₁.val ≠ x₂.val := fun h => hne (Subtype.ext h)
        have hnd := hnodisj x₁.val x₁.prop x₂.val x₂.prop hval_ne
        have hneq := hf₀_prop x₁.val x₂.val hval_ne hnd
        rw [hf₀_ext x₁, hf₀_ext x₂] at hneq
        exact hneq heq
      have hs_le_k : T.card ≤ k := by
        have h := Fintype.card_le_of_injective p hp_inj
        rwa [Fintype.card_coe, Fintype.card_fin] at h
      have hdc := perm_double_count T p hp_inj
      have hpow6 := pow_mul_sub_fact_le_six k T.card hs_le_k
      have hpow12 : k ^ T.card * (k - T.card).factorial ≤ 12 ^ T.card * k.factorial := by
        calc
          k ^ T.card * (k - T.card).factorial ≤ 6 ^ T.card * k.factorial := hpow6
          _ ≤ 12 ^ T.card * k.factorial :=
              Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) T.card)
      have hnat : k ^ T.card * extensions T p ≤ 12 ^ T.card * total E k := by
        have hfac_pos : 0 < (k - T.card).factorial := Nat.factorial_pos _
        have h1 : (k - T.card).factorial * (k ^ T.card * extensions T p) ≤
            (k - T.card).factorial * (12 ^ T.card * total E k) := by
          calc
            (k - T.card).factorial * (k ^ T.card * extensions T p)
                = (k ^ T.card * (k - T.card).factorial) * extensions T p := by ring
            _ ≤ (12 ^ T.card * k.factorial) * extensions T p :=
                Nat.mul_le_mul_right _ hpow12
            _ = 12 ^ T.card * (k.factorial * extensions T p) := by ring
            _ ≤ 12 ^ T.card * ((k - T.card).factorial * total E k) :=
                Nat.mul_le_mul_left _ hdc
            _ = (k - T.card).factorial * (12 ^ T.card * total E k) := by ring
        exact Nat.le_of_mul_le_mul_left h1 hfac_pos
      have hreal : ((k : ℝ) ^ T.card) * (extensions T p : ℝ) ≤
          ((12 : ℝ) ^ T.card) * (total E k : ℝ) := by exact_mod_cast hnat
      have h12_pos : (0 : ℝ) < (12 : ℝ) ^ T.card := by positivity
      rw [← hcard, mul_pow, one_div, inv_pow, mul_assoc]
      calc
        ((12 : ℝ) ^ T.card)⁻¹ * ((k : ℝ) ^ T.card * (extensions T p : ℝ))
            ≤ ((12 : ℝ) ^ T.card)⁻¹ * ((12 : ℝ) ^ T.card * (total E k : ℝ)) :=
            mul_le_mul_of_nonneg_left hreal (inv_nonneg.mpr h12_pos.le)
        _ = (total E k : ℝ) := inv_mul_cancel_left₀ h12_pos.ne' _

private lemma part1 : ∃ c : ℝ, 0 < c ∧ ExtensionBound c (fun m k => 6 * m ≤ 7 * k) := by
  refine ⟨1 / 12, by norm_num, ?_⟩
  intro n k E hE hmk T p hpos
  by_cases hk : 13 ≤ k
  · exact part1_core hE hmk hk T.card T p rfl hpos
  · have hk12 : k ≤ 12 := by omega
    have hck_le : (1 / 12 : ℝ) * (k : ℝ) ≤ 1 := by
      have : (k : ℝ) ≤ 12 := by exact_mod_cast hk12
      linarith
    have hpow_le : ((1 / 12 : ℝ) * (k : ℝ)) ^ T.card ≤ 1 :=
      pow_le_one₀ (by positivity) hck_le
    have hext_le : (extensions T p : ℝ) ≤ (total E k : ℝ) := by
      exact_mod_cast extensions_le_total T p
    calc
      ((1 / 12 : ℝ) * (k : ℝ)) ^ T.card * (extensions T p : ℝ)
          ≤ 1 * (extensions T p : ℝ) :=
          mul_le_mul_of_nonneg_right hpow_le (Nat.cast_nonneg _)
      _ = (extensions T p : ℝ) := one_mul _
      _ ≤ (total E k : ℝ) := hext_le

end Part1

section Part2

private lemma fin_add_one_ne_self {s : ℕ} [NeZero s] (hs : 2 ≤ s) (i : Fin s) : i + 1 ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  have h1 : (1 : Fin s).val = 1 := by
    show 1 % s = 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [Fin.val_add, h1] at hv
  have hi := i.isLt
  by_cases hlt : i.val + 1 < s
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : i.val + 1 = s := by omega
    rw [heq, Nat.mod_self] at hv
    omega

private lemma part2_counterexample (k s : ℕ) (hk : 2 ≤ k) (hs : 2 ≤ s) :
    ∃ (n : ℕ) (E : Finset (Finset (Fin n))) (T : Finset E) (p : T → Fin k),
      (∀ e ∈ E, e.card = 2) ∧ s ≤ E.card ∧ T.card = s ∧
      0 < extensions T p ∧ total E k ≤ k * extensions T p := by
  classical
  have : NeZero k := ⟨by omega⟩
  have : NeZero s := ⟨by omega⟩
  let V := Fin s × Bool × Fin k
  let n := Fintype.card V
  let eV : V ≃ Fin n := Fintype.equivFin V
  let v : Fin s → Bool → Fin k → Fin n := fun i b x => eV (i, b, x)
  have hv_inj : ∀ {i₁ i₂ b₁ b₂ x₁ x₂}, v i₁ b₁ x₁ = v i₂ b₂ x₂ →
      i₁ = i₂ ∧ b₁ = b₂ ∧ x₁ = x₂ := by
    intro i₁ i₂ b₁ b₂ x₁ x₂ h
    have := eV.injective h
    exact ⟨congrArg Prod.fst this, congrArg (fun t => t.2.1) this, congrArg (fun t => t.2.2) this⟩
  let intEdge : Fin s → Fin k → Fin k → Finset (Fin n) := fun i x y => {v i false x, v i true y}
  let brEdge : Fin s → Finset (Fin n) := fun i => {v i true 0, v (i + 1) false 0}
  have hint_card : ∀ i x y, (intEdge i x y).card = 2 := by
    intro i x y
    apply Finset.card_pair
    intro h
    exact Bool.false_ne_true (hv_inj h).2.1
  have hbr_card : ∀ i, (brEdge i).card = 2 := by
    intro i
    apply Finset.card_pair
    intro h
    exact Bool.false_ne_true (hv_inj h).2.1.symm
  have hint_inj : ∀ {i₁ i₂ x₁ x₂ y₁ y₂}, intEdge i₁ x₁ y₁ = intEdge i₂ x₂ y₂ →
      i₁ = i₂ ∧ x₁ = x₂ ∧ y₁ = y₂ := by
    intro i₁ i₂ x₁ x₂ y₁ y₂ h
    have hmem1 : v i₁ false x₁ ∈ intEdge i₂ x₂ y₂ := h ▸ Finset.mem_insert_self _ _
    have hmem2 : v i₁ true y₁ ∈ intEdge i₂ x₂ y₂ :=
      h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [intEdge, Finset.mem_insert, Finset.mem_singleton] at hmem1 hmem2
    rcases hmem1 with h1 | h1
    · rcases hv_inj h1 with ⟨hi, _, hx⟩
      rcases hmem2 with h2 | h2
      · exact False.elim (Bool.false_ne_true (hv_inj h2).2.1.symm)
      · exact ⟨hi, hx, (hv_inj h2).2.2⟩
    · exact False.elim (Bool.false_ne_true (hv_inj h1).2.1)
  have hbr_inj : Function.Injective brEdge := by
    intro i₁ i₂ h
    have hmem : v i₁ true 0 ∈ brEdge i₂ := h ▸ Finset.mem_insert_self _ _
    simp only [brEdge, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact (hv_inj h1).1
    · exact False.elim (Bool.false_ne_true (hv_inj h1).2.1.symm)
  have hint_ne_br : ∀ i x y j, intEdge i x y ≠ brEdge j := by
    intro i x y j h
    have hmem1 : v i false x ∈ brEdge j := h ▸ Finset.mem_insert_self _ _
    have hmem2 : v i true y ∈ brEdge j :=
      h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [brEdge, Finset.mem_insert, Finset.mem_singleton] at hmem1 hmem2
    rcases hmem1 with h1 | h1
    · exact Bool.false_ne_true (hv_inj h1).2.1
    · rcases hmem2 with h2 | h2
      · have hi1 : i = j + 1 := (hv_inj h1).1
        have hi2 : i = j := (hv_inj h2).1
        exact fin_add_one_ne_self hs j (hi1.symm.trans hi2)
      · exact Bool.false_ne_true (hv_inj h2).2.1.symm
  let E_int : Finset (Finset (Fin n)) :=
    (Finset.univ.filter (fun t : Fin s × Fin k × Fin k => ¬ (t.2.1 = 0 ∧ t.2.2 = 0))).image
      (fun t => intEdge t.1 t.2.1 t.2.2)
  let E_br : Finset (Finset (Fin n)) := Finset.univ.image brEdge
  let E : Finset (Finset (Fin n)) := E_int ∪ E_br
  have hE_card : ∀ e ∈ E, e.card = 2 := by
    intro e he
    rcases Finset.mem_union.mp he with he1 | he2
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp he1
      exact hint_card t.1 t.2.1 t.2.2
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he2
      exact hbr_card j
  have hbr_mem : ∀ j : Fin s, brEdge j ∈ E := fun j =>
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have hint_mem : ∀ (i : Fin s) (x y : Fin k), ¬ (x = 0 ∧ y = 0) → intEdge i x y ∈ E := by
    intro i x y hne
    exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨(i, x, y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, rfl⟩)
  have hEbr_card : E_br.card = s := by
    rw [Finset.card_image_of_injective _ hbr_inj, Finset.card_univ, Fintype.card_fin]
  have hs_le_E : s ≤ E.card := by
    rw [← hEbr_card]
    exact Finset.card_le_card Finset.subset_union_right
  let T : Finset E := E.attach.filter (fun e => e.val ∈ E_br)
  have hT_card : T.card = s := by
    have hbij : T.image Subtype.val = E_br := by
      ext x
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and]
      constructor
      · rintro ⟨⟨y, _⟩, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, Finset.mem_union_right _ hx⟩, hx, rfl⟩
    rw [← hEbr_card, ← hbij, Finset.card_image_of_injective _ Subtype.val_injective]
  let p : T → Fin k := fun _ => 0
  -- Construct witness proper colouring f0 extending p
  let f0 : E → Fin k := fun e =>
    if h : e.val ∈ E_br then 0
    else
      have he_int : e.val ∈ E_int := (Finset.mem_union.mp e.prop).resolve_right h
      let t := Classical.choose (Finset.mem_image.mp he_int)
      t.2.1 + t.2.2
  have hf0_br : ∀ j : Fin s, f0 ⟨brEdge j, hbr_mem j⟩ = 0 := by
    intro j
    have hmem : brEdge j ∈ E_br := Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    simp [f0, hmem]
  have hf0_int : ∀ (i : Fin s) (x y : Fin k) (hne : ¬ (x = 0 ∧ y = 0)),
      f0 ⟨intEdge i x y, hint_mem i x y hne⟩ = x + y := by
    intro i x y hne
    have hnotbr : intEdge i x y ∉ E_br := by
      intro hmem
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
      exact hint_ne_br i x y j hj.symm
    simp only [f0, dif_neg hnotbr]
    have hspec := Classical.choose_spec (Finset.mem_image.mp
      ((Finset.mem_union.mp (hint_mem i x y hne)).resolve_right hnotbr))
    rcases hint_inj hspec.2 with ⟨_, hx, hy⟩
    rw [hx, hy]
  have hf0_prop : Proper f0 := by
    intro e₁ e₂ hne hnd
    obtain ⟨w, hw1, hw2⟩ := Finset.not_disjoint_iff.mp hnd
    have hclass : ∀ e : E, (∃ j : Fin s, e.val = brEdge j) ∨
        (∃ i x y, ¬ (x = 0 ∧ y = 0) ∧ e.val = intEdge i x y) := by
      intro e
      rcases Finset.mem_union.mp e.prop with he1 | he2
      · obtain ⟨⟨i, x, y⟩, hfilt, heq⟩ := Finset.mem_image.mp he1
        exact Or.inr ⟨i, x, y, (Finset.mem_filter.mp hfilt).2, heq.symm⟩
      · obtain ⟨j, _, heq⟩ := Finset.mem_image.mp he2
        exact Or.inl ⟨j, heq.symm⟩
    rcases hclass e₁ with ⟨j₁, he₁⟩ | ⟨i₁, x₁, y₁, hne₁, he₁⟩ <;>
    rcases hclass e₂ with ⟨j₂, he₂⟩ | ⟨i₂, x₂, y₂, hne₂, he₂⟩
    · -- Both bridge edges: cannot share a vertex unless equal
      have hjne : j₁ ≠ j₂ := fun h => hne (Subtype.ext (by rw [he₁, he₂, h]))
      rw [he₁] at hw1
      rw [he₂] at hw2
      simp only [brEdge, Finset.mem_insert, Finset.mem_singleton] at hw1 hw2
      rcases hw1 with rfl | rfl <;> rcases hw2 with h | h
      · exact False.elim (hjne (hv_inj h).1)
      · exact False.elim (Bool.false_ne_true (hv_inj h).2.1.symm)
      · exact False.elim (Bool.false_ne_true (hv_inj h).2.1)
      · have hadd : j₁ + 1 = j₂ + 1 := (hv_inj h).1
        exact False.elim (hjne (add_right_cancel hadd))
    · -- e1 bridge, e2 internal
      have hf1 : f0 e₁ = 0 := by
        have : e₁ = ⟨brEdge j₁, hbr_mem j₁⟩ := Subtype.ext he₁
        rw [this, hf0_br]
      have hf2 : f0 e₂ = x₂ + y₂ := by
        have : e₂ = ⟨intEdge i₂ x₂ y₂, hint_mem i₂ x₂ y₂ hne₂⟩ := Subtype.ext he₂
        rw [this, hf0_int i₂ x₂ y₂ hne₂]
      rw [hf1, hf2]
      rw [he₁] at hw1
      rw [he₂] at hw2
      simp only [brEdge, intEdge, Finset.mem_insert, Finset.mem_singleton] at hw1 hw2
      rcases hw1 with rfl | rfl <;> rcases hw2 with h | h
      · exact False.elim (Bool.false_ne_true (hv_inj h).2.1.symm)
      · have hy : y₂ = 0 := (hv_inj h).2.2.symm
        have hx : x₂ ≠ 0 := fun hx0 => hne₂ ⟨hx0, hy⟩
        rw [hy, add_zero]
        exact hx.symm
      · have hx : x₂ = 0 := (hv_inj h).2.2.symm
        have hy : y₂ ≠ 0 := fun hy0 => hne₂ ⟨hx, hy0⟩
        rw [hx, zero_add]
        exact hy.symm
      · exact False.elim (Bool.false_ne_true (hv_inj h).2.1)
    · -- e1 internal, e2 bridge
      have hf1 : f0 e₁ = x₁ + y₁ := by
        have : e₁ = ⟨intEdge i₁ x₁ y₁, hint_mem i₁ x₁ y₁ hne₁⟩ := Subtype.ext he₁
        rw [this, hf0_int i₁ x₁ y₁ hne₁]
      have hf2 : f0 e₂ = 0 := by
        have : e₂ = ⟨brEdge j₂, hbr_mem j₂⟩ := Subtype.ext he₂
        rw [this, hf0_br]
      rw [hf1, hf2]
      rw [he₁] at hw1
      rw [he₂] at hw2
      simp only [brEdge, intEdge, Finset.mem_insert, Finset.mem_singleton] at hw1 hw2
      rcases hw1 with rfl | rfl <;> rcases hw2 with h | h
      · exact False.elim (Bool.false_ne_true (hv_inj h).2.1)
      · have hx : x₁ = 0 := (hv_inj h).2.2
        have hy : y₁ ≠ 0 := fun hy0 => hne₁ ⟨hx, hy0⟩
        rw [hx, zero_add]
        exact hy
      · have hy : y₁ = 0 := (hv_inj h).2.2
        have hx : x₁ ≠ 0 := fun hx0 => hne₁ ⟨hx0, hy⟩
        rw [hy, add_zero]
        exact hx
      · exact False.elim (Bool.false_ne_true (hv_inj h).2.1.symm)
    · -- Both internal
      have hf1 : f0 e₁ = x₁ + y₁ := by
        have : e₁ = ⟨intEdge i₁ x₁ y₁, hint_mem i₁ x₁ y₁ hne₁⟩ := Subtype.ext he₁
        rw [this, hf0_int i₁ x₁ y₁ hne₁]
      have hf2 : f0 e₂ = x₂ + y₂ := by
        have : e₂ = ⟨intEdge i₂ x₂ y₂, hint_mem i₂ x₂ y₂ hne₂⟩ := Subtype.ext he₂
        rw [this, hf0_int i₂ x₂ y₂ hne₂]
      rw [hf1, hf2]
      rw [he₁] at hw1
      rw [he₂] at hw2
      simp only [intEdge, Finset.mem_insert, Finset.mem_singleton] at hw1 hw2
      rcases hw1 with rfl | rfl <;> rcases hw2 with h | h
      · rcases hv_inj h with ⟨hi, _, hx⟩
        have hy : y₁ ≠ y₂ := fun hy => hne (Subtype.ext (by rw [he₁, he₂, hi, hx, hy]))
        intro hsum
        rw [hx] at hsum
        exact hy (add_left_cancel hsum)
      · exact False.elim (Bool.false_ne_true (hv_inj h).2.1)
      · exact False.elim (Bool.false_ne_true (hv_inj h).2.1.symm)
      · rcases hv_inj h with ⟨hi, _, hy⟩
        have hx : x₁ ≠ x₂ := fun hx => hne (Subtype.ext (by rw [he₁, he₂, hi, hx, hy]))
        intro hsum
        rw [hy] at hsum
        exact hx (add_right_cancel hsum)
  have hf0_ext : ∀ e : T, f0 e.val = p e := by
    intro e
    have hmem : e.val.val ∈ E_br := (Finset.mem_filter.mp e.prop).2
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
    have heq : e.val = ⟨brEdge j, hbr_mem j⟩ := Subtype.ext hj.symm
    rw [heq, hf0_br]
  have hpos : 0 < extensions T p := by
    unfold extensions
    exact Nat.card_pos_iff.mpr ⟨⟨⟨f0, hf0_prop, hf0_ext⟩⟩, Finite.of_fintype _⟩
  -- Forcing lemma: in any proper colouring f, all bridge edges have the same colour
  have hforce_step : ∀ (f : E → Fin k), Proper f → ∀ i : Fin s,
      f ⟨brEdge (i + 1), hbr_mem (i + 1)⟩ = f ⟨brEdge i, hbr_mem i⟩ := by
    intro f hf i
    let j : Fin s := i + 1
    let c₀ : Fin k := f ⟨brEdge i, hbr_mem i⟩
    -- 1. For every x != 0, some y has f(intEdge j x y) = c0
    have hleft_surj : ∀ (x : Fin k) (hx : x ≠ 0),
        ∃ y : Fin k, f ⟨intEdge j x y, hint_mem j x y (fun h => hx h.1)⟩ = c₀ := by
      intro x hx
      let gx : Fin k → Fin k := fun y => f ⟨intEdge j x y, hint_mem j x y (fun h => hx h.1)⟩
      have hgx_inj : Function.Injective gx := by
        intro y₁ y₂ heq
        by_contra hyne
        have hene : (⟨intEdge j x y₁, hint_mem j x y₁ (fun h => hx h.1)⟩ : E) ≠
            ⟨intEdge j x y₂, hint_mem j x y₂ (fun h => hx h.1)⟩ :=
          fun h => hyne (hint_inj (congrArg Subtype.val h)).2.2
        have hnd : ¬ Disjoint (intEdge j x y₁) (intEdge j x y₂) :=
          Finset.not_disjoint_iff.mpr ⟨v j false x, Finset.mem_insert_self _ _,
            Finset.mem_insert_self _ _⟩
        exact hf _ _ hene hnd heq
      exact (Finite.injective_iff_surjective.mp hgx_inj) c₀
    -- 2. For every y != 0, some x != 0 has f(intEdge j x y) = c0
    have hright_surj : ∀ (y : Fin k) (hy : y ≠ 0),
        ∃ (x : Fin k) (hx : x ≠ 0), f ⟨intEdge j x y, hint_mem j x y (fun h => hy h.2)⟩ = c₀ := by
      intro y hy
      let gy : Fin k → Fin k := fun x => f ⟨intEdge j x y, hint_mem j x y (fun h => hy h.2)⟩
      have hgy_inj : Function.Injective gy := by
        intro x₁ x₂ heq
        by_contra hxne
        have hene : (⟨intEdge j x₁ y, hint_mem j x₁ y (fun h => hy h.2)⟩ : E) ≠
            ⟨intEdge j x₂ y, hint_mem j x₂ y (fun h => hy h.2)⟩ :=
          fun h => hxne (hint_inj (congrArg Subtype.val h)).2.1
        have hnd : ¬ Disjoint (intEdge j x₁ y) (intEdge j x₂ y) :=
          Finset.not_disjoint_iff.mpr ⟨v j true y,
            Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
            Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
        exact hf _ _ hene hnd heq
      obtain ⟨x, hx_eq⟩ := (Finite.injective_iff_surjective.mp hgy_inj) c₀
      have hx0 : x ≠ 0 := by
        intro hxzero
        subst hxzero
        have hene : (⟨intEdge j 0 y, hint_mem j 0 y (fun h => hy h.2)⟩ : E) ≠
            ⟨brEdge i, hbr_mem i⟩ := fun h => hint_ne_br j 0 y i (congrArg Subtype.val h)
        have hnd : ¬ Disjoint (intEdge j 0 y) (brEdge i) :=
          Finset.not_disjoint_iff.mpr ⟨v j false 0,
            Finset.mem_insert_self _ _,
            Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
        exact hf _ _ hene hnd hx_eq
      exact ⟨x, hx0, hx_eq⟩
    -- 3. Define phi on Fin k \ {0} mapping x to the unique y with f(intEdge j x y) = c0
    let S : Finset (Fin k) := Finset.univ.erase 0
    let φ : Fin k → Fin k := fun x =>
      if hx : x ≠ 0 then Classical.choose (hleft_surj x hx) else 0
    have hφ_spec : ∀ (x : Fin k) (hx : x ≠ 0),
        f ⟨intEdge j x (φ x), hint_mem j x (φ x) (fun h => hx h.1)⟩ = c₀ := by
      intro x hx
      simp only [φ, dif_pos hx]
      exact Classical.choose_spec (hleft_surj x hx)
    have hφ_inj : Set.InjOn φ (S : Set (Fin k)) := by
      intro x₁ hx₁ x₂ hx₂ heq
      have hx₁0 : x₁ ≠ 0 := (Finset.mem_erase.mp hx₁).1
      have hx₂0 : x₂ ≠ 0 := (Finset.mem_erase.mp hx₂).1
      by_contra hxne
      have h1 := hφ_spec x₁ hx₁0
      have h2 := hφ_spec x₂ hx₂0
      have hene : (⟨intEdge j x₁ (φ x₁), hint_mem j x₁ (φ x₁) (fun h => hx₁0 h.1)⟩ : E) ≠
          ⟨intEdge j x₂ (φ x₂), hint_mem j x₂ (φ x₂) (fun h => hx₂0 h.1)⟩ :=
        fun h => hxne (hint_inj (congrArg Subtype.val h)).2.1
      have hnd : ¬ Disjoint (intEdge j x₁ (φ x₁)) (intEdge j x₂ (φ x₂)) :=
        Finset.not_disjoint_iff.mpr ⟨v j true (φ x₁),
          Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
          by rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
      exact hf _ _ hene hnd (h1.trans h2.symm)
    have hS_sub : S ⊆ S.image φ := by
      intro y hy
      have hy0 : y ≠ 0 := (Finset.mem_erase.mp hy).1
      obtain ⟨x, hx0, hxy⟩ := hright_surj y hy0
      have hφx : φ x = y := by
        by_contra hne_y
        have h1 := hφ_spec x hx0
        have hene : (⟨intEdge j x (φ x), hint_mem j x (φ x) (fun h => hx0 h.1)⟩ : E) ≠
            ⟨intEdge j x y, hint_mem j x y (fun h => hy0 h.2)⟩ :=
          fun h => hne_y (hint_inj (congrArg Subtype.val h)).2.2
        have hnd : ¬ Disjoint (intEdge j x (φ x)) (intEdge j x y) :=
          Finset.not_disjoint_iff.mpr ⟨v j false x, Finset.mem_insert_self _ _,
            Finset.mem_insert_self _ _⟩
        exact hf _ _ hene hnd (h1.trans hxy.symm)
      exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hx0, Finset.mem_univ x⟩, hφx⟩
    have hS_eq : S.image φ = S := by
      have hcard_img : (S.image φ).card = S.card := Finset.card_image_of_injOn hφ_inj
      exact (Finset.eq_of_subset_of_card_le hS_sub (le_of_eq hcard_img)).symm
    have hno_int_c0 : ∀ (x : Fin k) (hx : x ≠ 0),
        f ⟨intEdge j x 0, hint_mem j x 0 (fun h => hx h.1)⟩ ≠ c₀ := by
      intro x hx heq
      have hφ0 : φ x = 0 := by
        by_contra hne0
        have h1 := hφ_spec x hx
        have hene : (⟨intEdge j x (φ x), hint_mem j x (φ x) (fun h => hx h.1)⟩ : E) ≠
            ⟨intEdge j x 0, hint_mem j x 0 (fun h => hx h.1)⟩ :=
          fun h => hne0 (hint_inj (congrArg Subtype.val h)).2.2
        have hnd : ¬ Disjoint (intEdge j x (φ x)) (intEdge j x 0) :=
          Finset.not_disjoint_iff.mpr ⟨v j false x, Finset.mem_insert_self _ _,
            Finset.mem_insert_self _ _⟩
        exact hf _ _ hene hnd (h1.trans heq.symm)
      have h0mem : (0 : Fin k) ∈ S.image φ :=
        Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩, hφ0⟩
      rw [hS_eq] at h0mem
      exact (Finset.mem_erase.mp h0mem).1 rfl
    -- 4. Colour c0 must appear at vertex v j true 0, forcing f(brEdge j) = c0
    let g0 : Fin k → Fin k := fun x =>
      if hx : x = 0 then f ⟨brEdge j, hbr_mem j⟩
      else f ⟨intEdge j x 0, hint_mem j x 0 (fun h => hx h.1)⟩
    have hg0_inj : Function.Injective g0 := by
      intro x₁ x₂ heq
      by_contra hxne
      by_cases h1 : x₁ = 0
      · subst h1
        have h2 : x₂ ≠ 0 := fun h => hxne h.symm
        simp only [g0, dif_pos rfl, dif_neg h2] at heq
        have hene : (⟨brEdge j, hbr_mem j⟩ : E) ≠
            ⟨intEdge j x₂ 0, hint_mem j x₂ 0 (fun h => h2 h.1)⟩ :=
          fun h => hint_ne_br j x₂ 0 j (congrArg Subtype.val h).symm
        have hnd : ¬ Disjoint (brEdge j) (intEdge j x₂ 0) :=
          Finset.not_disjoint_iff.mpr ⟨v j true 0, Finset.mem_insert_self _ _,
            Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
        exact hf _ _ hene hnd heq
      · by_cases h2 : x₂ = 0
        · subst h2
          simp only [g0, dif_neg h1, dif_pos rfl] at heq
          have hene : (⟨intEdge j x₁ 0, hint_mem j x₁ 0 (fun h => h1 h.1)⟩ : E) ≠
              ⟨brEdge j, hbr_mem j⟩ :=
            fun h => hint_ne_br j x₁ 0 j (congrArg Subtype.val h)
          have hnd : ¬ Disjoint (intEdge j x₁ 0) (brEdge j) :=
            Finset.not_disjoint_iff.mpr ⟨v j true 0,
              Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
              Finset.mem_insert_self _ _⟩
          exact hf _ _ hene hnd heq
        · simp only [g0, dif_neg h1, dif_neg h2] at heq
          have hene : (⟨intEdge j x₁ 0, hint_mem j x₁ 0 (fun h => h1 h.1)⟩ : E) ≠
              ⟨intEdge j x₂ 0, hint_mem j x₂ 0 (fun h => h2 h.1)⟩ :=
            fun h => hxne (hint_inj (congrArg Subtype.val h)).2.1
          have hnd : ¬ Disjoint (intEdge j x₁ 0) (intEdge j x₂ 0) :=
            Finset.not_disjoint_iff.mpr ⟨v j true 0,
              Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
              Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
          exact hf _ _ hene hnd heq
    obtain ⟨x, hx_eq⟩ := (Finite.injective_iff_surjective.mp hg0_inj) c₀
    by_cases hx0 : x = 0
    · subst hx0
      simpa [g0] using hx_eq
    · simp only [g0, dif_neg hx0] at hx_eq
      exact False.elim (hno_int_c0 x hx0 hx_eq)
  have hforce_all : ∀ (f : E → Fin k), Proper f → ∀ j : Fin s,
      f ⟨brEdge j, hbr_mem j⟩ = f ⟨brEdge 0, hbr_mem 0⟩ := by
    intro f hf j
    have hofnat_succ : ∀ r : ℕ, Fin.ofNat s (r + 1) = Fin.ofNat s r + 1 := by
      intro r
      apply Fin.ext
      show (r + 1) % s = ((r % s) + (1 % s)) % s
      exact Nat.add_mod r 1 s
    have hnat : ∀ r : ℕ, f ⟨brEdge (Fin.ofNat s r), hbr_mem (Fin.ofNat s r)⟩ =
        f ⟨brEdge 0, hbr_mem 0⟩ := by
      intro r
      induction r with
      | zero => rfl
      | succ r ih =>
        rw [hofnat_succ r, hforce_step f hf (Fin.ofNat s r), ih]
    have hj : Fin.ofNat s j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
    simpa [hj] using hnat j.val
  -- Bound total E k <= k * extensions T p
  have htotal_le : total E k ≤ k * extensions T p := by
    let Θ : {f : E → Fin k // Proper f} →
        Fin k × {f : E → Fin k // Proper f ∧ ∀ e : T, f e.val = p e} := fun f =>
      let a : Fin k := f.val ⟨brEdge 0, hbr_mem 0⟩
      let σ : Equiv.Perm (Fin k) := Equiv.swap a 0
      (a, ⟨fun e => σ (f.val e), by
        constructor
        · intro e₁ e₂ hne hnd heq
          exact f.prop e₁ e₂ hne hnd (σ.injective heq)
        · intro e
          have hmem : e.val.val ∈ E_br := (Finset.mem_filter.mp e.prop).2
          obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
          have heq : e.val = ⟨brEdge j, hbr_mem j⟩ := Subtype.ext hj.symm
          dsimp only
          rw [heq, hforce_all f.val f.prop j]
          exact Equiv.swap_apply_left a 0⟩)
    have hΘ_inj : Function.Injective Θ := by
      intro f₁ f₂ heq
      have ha : f₁.val ⟨brEdge 0, hbr_mem 0⟩ = f₂.val ⟨brEdge 0, hbr_mem 0⟩ :=
        congrArg Prod.fst heq
      have hfun : (fun e => Equiv.swap (f₁.val ⟨brEdge 0, hbr_mem 0⟩) 0 (f₁.val e)) =
          (fun e => Equiv.swap (f₂.val ⟨brEdge 0, hbr_mem 0⟩) 0 (f₂.val e)) :=
        congrArg (fun z => z.2.val) heq
      apply Subtype.ext
      funext e
      have h1 := congrFun hfun e
      rw [← ha] at h1
      exact (Equiv.swap _ _).injective h1
    unfold total extensions
    have hle := Nat.card_le_card_of_injective Θ hΘ_inj
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin] at hle
    exact hle
  exact ⟨n, E, T, p, hE_card, hs_le_E, hT_card, hpos, htotal_le⟩

private lemma part2 : ¬ (∃ (c : ℝ) (m₀ : ℕ), 0 < c ∧ ExtensionBound c (fun m _ => m₀ ≤ m)) := by
  rintro ⟨c, m₀, hc, hEB⟩
  let k : ℕ := max 2 (Nat.ceil (2 / c))
  have hk2 : 2 ≤ k := le_max_left _ _
  have hck : (2 : ℝ) ≤ c * (k : ℝ) := by
    have h1 : 2 / c ≤ (Nat.ceil (2 / c) : ℝ) := Nat.le_ceil (2 / c)
    have h2 : (Nat.ceil (2 / c) : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_max_right 2 (Nat.ceil (2 / c))
    have h3 : 2 / c ≤ (k : ℝ) := le_trans h1 h2
    have h4 := (div_le_iff₀ hc).mp h3
    linarith
  let s : ℕ := max 2 (max m₀ k)
  have hs2 : 2 ≤ s := le_max_left _ _
  have hm0_le : m₀ ≤ s := le_trans (le_max_left m₀ k) (le_max_right 2 _)
  have hk_le : k ≤ s := le_trans (le_max_right m₀ k) (le_max_right 2 _)
  obtain ⟨n, E, T, p, hE, hsE, hTs, hpos, htot⟩ := part2_counterexample k s hk2 hs2
  have hbound := hEB n k E hE (le_trans hm0_le hsE) T p hpos
  rw [hTs] at hbound
  have hpow : (2 : ℝ) ^ s ≤ (c * (k : ℝ)) ^ s := pow_le_pow_left₀ (by norm_num) hck s
  have htotR : (total E k : ℝ) ≤ (k : ℝ) * (extensions T p : ℝ) := by exact_mod_cast htot
  have hposR : (0 : ℝ) < (extensions T p : ℝ) := Nat.cast_pos.mpr hpos
  have hmul : (2 : ℝ) ^ s * (extensions T p : ℝ) ≤ (k : ℝ) * (extensions T p : ℝ) := by
    calc
      (2 : ℝ) ^ s * (extensions T p : ℝ)
          ≤ (c * (k : ℝ)) ^ s * (extensions T p : ℝ) :=
          mul_le_mul_of_nonneg_right hpow hposR.le
      _ ≤ (total E k : ℝ) := hbound
      _ ≤ (k : ℝ) * (extensions T p : ℝ) := htotR
  have h2kR : (2 : ℝ) ^ s ≤ (k : ℝ) := le_of_mul_le_mul_right hmul hposR
  have h2k : 2 ^ s ≤ k := by exact_mod_cast h2kR
  have hlt : k < 2 ^ s := lt_of_le_of_lt hk_le Nat.lt_two_pow_self
  omega

end Part2

end OMA.S_mo_472523_Proof

theorem OMA.solution : type_of% @OMA.S_mo_472523.main :=
  ⟨OMA.S_mo_472523_Proof.part1, OMA.S_mo_472523_Proof.part2⟩
