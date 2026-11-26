import FormalConjectures.Arxiv.«2605.12342».Conjecture1

-- Problem: Fernandes' conjecture on the 2-generation of even direct product permutation groups — rank 4 4
-- Upstream: formal-conjectures FormalConjectures/Arxiv/2605.12342/Conjecture1.lean:145 (declaration Arxiv.«2605.12342».conjecture_1.variants.rank_4_4)
-- Credit: @jlgmaarav (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Equiv Equiv.Perm

/-! `Γ_{3⊕3}` is the generalized dihedral group of `C₃ × C₃`: the (even, even) pairs form an
abelian group of exponent 3 and every (odd, odd) pair is an involution inverting it. Any two
elements therefore lie in a subgroup `{aᵏ, r aᵏ}` of order at most 6. -/

abbrev G3 := Perm (Fin 3) × Perm (Fin 3)

def IsEv (x : G3) : Prop := sign x.1 = 1 ∧ sign x.2 = 1
def IsOd (x : G3) : Prop := sign x.1 = -1 ∧ sign x.2 = -1
instance : DecidablePred IsEv := fun x => by unfold IsEv; infer_instance
instance : DecidablePred IsOd := fun x => by unfold IsOd; infer_instance

lemma od_sq : ∀ x : G3, IsOd x → x * x = 1 := by decide
lemma od_conj : ∀ r n : G3, IsOd r → IsEv n → r * n * r = n⁻¹ := by decide
lemma ev_cube : ∀ n : G3, IsEv n → n * n * n = 1 := by decide
lemma ev_avoid : ∀ a : G3, IsEv a → ∃ b : G3, IsEv b ∧ b ≠ 1 ∧ b ≠ a ∧ b ≠ a * a := by decide
lemma exists_od : ∃ x : G3, IsOd x := by decide

lemma units_cases (u : ℤˣ) : u = 1 ∨ u = -1 := Int.units_eq_one_or u

lemma ev_one : IsEv 1 := by simp [IsEv]
lemma ev_mul {x y : G3} (hx : IsEv x) (hy : IsEv y) : IsEv (x * y) := by
  simp [IsEv, Equiv.Perm.sign_mul, hx.1, hx.2, hy.1, hy.2]
lemma od_mul_ev {x y : G3} (hx : IsOd x) (hy : IsEv y) : IsOd (x * y) := by
  simp [IsOd, Equiv.Perm.sign_mul, hx.1, hx.2, hy.1, hy.2]
lemma ev_mul_od {x y : G3} (hx : IsEv x) (hy : IsOd y) : IsOd (x * y) := by
  simp [IsOd, Equiv.Perm.sign_mul, hx.1, hx.2, hy.1, hy.2]
lemma od_mul_od {x y : G3} (hx : IsOd x) (hy : IsOd y) : IsEv (x * y) := by
  simp [IsEv, Equiv.Perm.sign_mul, hx.1, hx.2, hy.1, hy.2]
lemma ev_inv {x : G3} (hx : IsEv x) : IsEv x⁻¹ := by
  simp [IsEv, hx.1, hx.2]
lemma not_ev_od {x : G3} (he : IsEv x) (ho : IsOd x) : False := by
  have := he.1.symm.trans ho.1
  exact absurd this (by decide)

lemma mem_gamma {x : G3} : x ∈ Arxiv.«2605.12342».gammaSubgroup 3 3 ↔ sign x.1 = sign x.2 := by
  simp only [Arxiv.«2605.12342».gammaSubgroup, Arxiv.«2605.12342».signDiffHom, MonoidHom.mem_ker,
    MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd,
    MonoidHom.inv_apply, mul_inv_eq_one]

lemma ev_or_od {x : G3} (hx : x ∈ Arxiv.«2605.12342».gammaSubgroup 3 3) : IsEv x ∨ IsOd x := by
  rw [mem_gamma] at hx
  rcases units_cases (sign x.1) with h | h
  · exact Or.inl ⟨h, hx ▸ h⟩
  · exact Or.inr ⟨h, hx ▸ h⟩

/-- The set `{1, a, a²}` for an even `a` (closed under products and inverses since `a³ = 1`). -/
def S (a : G3) : Set G3 := {x | x = 1 ∨ x = a ∨ x = a * a}

lemma S_mul {a x y : G3} (ha : a * a * a = 1) (hx : x ∈ S a) (hy : y ∈ S a) : x * y ∈ S a := by
  have h4 : a * a * a * a = a := by rw [ha, one_mul]
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    simp only [S, Set.mem_setOf_eq, one_mul, mul_one, ← mul_assoc, ha, h4] <;> simp

lemma S_inv {a x : G3} (ha : a * a * a = 1) (hx : x ∈ S a) : x⁻¹ ∈ S a := by
  rcases hx with rfl | rfl | rfl
  · left; simp
  · right; right; exact inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ha])
  · right; left; exact inv_eq_of_mul_eq_one_right ha

lemma S_ev {a x : G3} (ha : IsEv a) (hx : x ∈ S a) : IsEv x := by
  rcases hx with rfl | rfl | rfl
  · exact ev_one
  · exact ha
  · exact ev_mul ha ha

/-- The dihedral subgroup `{aᵏ} ∪ r {aᵏ}`. -/
def K (r a : G3) (hr : IsOd r) (ha : IsEv a) : Subgroup G3 where
  carrier := {x | (IsEv x ∧ x ∈ S a) ∨ (IsOd x ∧ r * x ∈ S a)}
  one_mem' := Or.inl ⟨ev_one, Or.inl rfl⟩
  mul_mem' := by
    have h3 := ev_cube a ha
    have hrr := od_sq r hr
    intro x y hx hy
    rcases hx with ⟨hxe, hxs⟩ | ⟨hxo, hxs⟩ <;> rcases hy with ⟨hye, hys⟩ | ⟨hyo, hys⟩
    · exact Or.inl ⟨ev_mul hxe hye, S_mul h3 hxs hys⟩
    · refine Or.inr ⟨ev_mul_od hxe hyo, ?_⟩
      have : r * (x * y) = (r * x * r) * (r * y) := by
        calc r * (x * y) = r * x * (r * r) * y := by rw [hrr, mul_one, mul_assoc]
          _ = (r * x * r) * (r * y) := by simp only [mul_assoc]
      rw [this, od_conj r x hr hxe]
      exact S_mul h3 (S_inv h3 hxs) hys
    · refine Or.inr ⟨od_mul_ev hxo hye, ?_⟩
      rw [← mul_assoc]; exact S_mul h3 hxs hys
    · refine Or.inl ⟨od_mul_od hxo hyo, ?_⟩
      have hx' : x = r * (r * x) := by rw [← mul_assoc, hrr, one_mul]
      have hy' : y = r * (r * y) := by rw [← mul_assoc, hrr, one_mul]
      have : x * y = (r * (r * x) * r) * (r * y) := by
        conv_lhs => rw [hx', hy']
        simp only [mul_assoc]
      rw [this, od_conj r (r * x) hr (S_ev ha hxs)]
      exact S_mul h3 (S_inv h3 hxs) hys
  inv_mem' := by
    have h3 := ev_cube a ha
    intro x hx
    rcases hx with ⟨hxe, hxs⟩ | ⟨hxo, hxs⟩
    · exact Or.inl ⟨ev_inv hxe, S_inv h3 hxs⟩
    · have : x⁻¹ = x := inv_eq_of_mul_eq_one_right (od_sq x hxo)
      rw [this]; exact Or.inr ⟨hxo, hxs⟩

/-- The (even, even) subgroup. -/
def Nsub : Subgroup G3 where
  carrier := {x | IsEv x}
  one_mem' := ev_one
  mul_mem' := ev_mul
  inv_mem' := ev_inv

lemma closure_ne_top_of (L : Subgroup G3) (h₁ h₂ : Arxiv.«2605.12342».gammaSubgroup 3 3)
    (hk1 : h₁.1 ∈ L) (hk2 : h₂.1 ∈ L) (b : G3) (hb : b ∈ Arxiv.«2605.12342».gammaSubgroup 3 3)
    (hbL : b ∉ L) : Subgroup.closure {h₁, h₂} ≠ ⊤ := by
  intro htop
  have hmem : (⟨b, hb⟩ : Arxiv.«2605.12342».gammaSubgroup 3 3) ∈ Subgroup.closure {h₁, h₂} :=
    htop ▸ Subgroup.mem_top _
  have hle : Subgroup.closure {h₁, h₂} ≤ L.comap (Arxiv.«2605.12342».gammaSubgroup 3 3).subtype := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hk1
    · exact hk2
  exact hbL (hle hmem)

lemma dihedral_case (r a : G3) (hr : IsOd r) (ha : IsEv a)
    (h₁ h₂ : Arxiv.«2605.12342».gammaSubgroup 3 3)
    (hk1 : h₁.1 ∈ K r a hr ha) (hk2 : h₂.1 ∈ K r a hr ha) : Subgroup.closure {h₁, h₂} ≠ ⊤ := by
  obtain ⟨b, hbe, hb1, hba, hbaa⟩ := ev_avoid a ha
  refine closure_ne_top_of (K r a hr ha) h₁ h₂ hk1 hk2 b (mem_gamma.mpr (hbe.1.trans hbe.2.symm)) ?_
  rintro (⟨-, hbs⟩ | ⟨hbo, -⟩)
  · rcases hbs with h | h | h <;> contradiction
  · exact not_ev_od hbe hbo

lemma rank33 : ∀ h₁ h₂ : Arxiv.«2605.12342».gammaSubgroup 3 3, Subgroup.closure {h₁, h₂} ≠ ⊤ := by
  intro h₁ h₂
  rcases ev_or_od h₁.2 with he1 | ho1 <;> rcases ev_or_od h₂.2 with he2 | ho2
  · -- both even: they lie in the proper subgroup of (even, even) pairs
    obtain ⟨b, hb⟩ := exists_od
    refine closure_ne_top_of Nsub h₁ h₂ he1 he2 b (mem_gamma.mpr (hb.1.trans hb.2.symm)) ?_
    exact fun hbe => not_ev_od hbe hb
  · exact dihedral_case h₂.1 h₁.1 ho2 he1 h₁ h₂ (Or.inl ⟨he1, Or.inr (Or.inl rfl)⟩)
      (Or.inr ⟨ho2, Or.inl (od_sq _ ho2)⟩)
  · exact dihedral_case h₁.1 h₂.1 ho1 he2 h₁ h₂ (Or.inr ⟨ho1, Or.inl (od_sq _ ho1)⟩)
      (Or.inl ⟨he2, Or.inr (Or.inl rfl)⟩)
  · exact dihedral_case h₁.1 (h₁.1 * h₂.1) ho1 (od_mul_od ho1 ho2) h₁ h₂
      (Or.inr ⟨ho1, Or.inl (od_sq _ ho1)⟩) (Or.inr ⟨ho2, Or.inr (Or.inl rfl)⟩)

/-! The epimorphism `S₄ → S₃` given by the action on the three pairings of `{0,1,2,3}`
(`{01|23}`, `{02|13}`, `{03|12}`, indexed by the partner of `0` minus one). It preserves signs. -/

/-- Index of the pairing containing the pair `{a, b}`: `a xor b - 1`. -/
def pairIdx (a b : Fin 4) : Fin 3 := ⟨((a.val ^^^ b.val) + 2) % 3, Nat.mod_lt _ (by norm_num)⟩

def phiFun (σ : Perm (Fin 4)) (i : Fin 3) : Fin 3 :=
  pairIdx (σ 0) (σ ⟨(i.val + 1) % 4, Nat.mod_lt _ (by norm_num)⟩)

lemma phiFun_left : ∀ σ : Perm (Fin 4), ∀ i, phiFun σ⁻¹ (phiFun σ i) = i := by decide
lemma phiFun_right : ∀ σ : Perm (Fin 4), ∀ i, phiFun σ (phiFun σ⁻¹ i) = i := by decide

def phiPerm (σ : Perm (Fin 4)) : Perm (Fin 3) :=
  ⟨phiFun σ, phiFun σ⁻¹, phiFun_left σ, phiFun_right σ⟩

lemma phiFun_mul : ∀ σ τ : Perm (Fin 4), ∀ i, phiFun (σ * τ) i = phiFun σ (phiFun τ i) := by
  decide

def phi : Perm (Fin 4) →* Perm (Fin 3) where
  toFun := phiPerm
  map_one' := by ext i; revert i; decide
  map_mul' σ τ := by ext i; exact congrArg Fin.val (phiFun_mul σ τ i)

lemma phi_sign : ∀ σ : Perm (Fin 4), sign (phiPerm σ) = sign σ := by decide

lemma phi_surj : ∀ π : Perm (Fin 3), ∃ σ : Perm (Fin 4), phiPerm σ = π := by decide

lemma mem_gamma_gen {m n : ℕ} {x : Perm (Fin m) × Perm (Fin n)} :
    x ∈ Arxiv.«2605.12342».gammaSubgroup m n ↔ sign x.1 = sign x.2 := by
  simp only [Arxiv.«2605.12342».gammaSubgroup, Arxiv.«2605.12342».signDiffHom, MonoidHom.mem_ker,
    MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd,
    MonoidHom.inv_apply, mul_inv_eq_one]

/-- If a surjective homomorphism maps `Γ` onto `Γ_{3⊕3}`, then `Γ` is not 2-generated either. -/
lemma transfer {H : Type*} [Group H] (f : H →* Arxiv.«2605.12342».gammaSubgroup 3 3)
    (hf : Function.Surjective f) (h₁ h₂ : H) : Subgroup.closure {h₁, h₂} ≠ ⊤ := by
  intro htop
  apply rank33 (f h₁) (f h₂)
  have := congrArg (Subgroup.map f) htop
  rw [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top_of_surjective f hf] at this
  exact this

/-- `(σ, τ) ↦ (φ σ, φ τ)` maps `Γ_{4⊕4}` onto `Γ_{3⊕3}`. -/
noncomputable def psi : Arxiv.«2605.12342».gammaSubgroup 4 4 →* Arxiv.«2605.12342».gammaSubgroup 3 3 :=
  ((MonoidHom.prodMap phi phi).comp (Arxiv.«2605.12342».gammaSubgroup 4 4).subtype).codRestrict _
    (fun x => by
      have hx := mem_gamma_gen.mp x.2
      rw [mem_gamma_gen]
      simp only [MonoidHom.comp_apply, MonoidHom.prodMap, Prod.map_fst,
        Prod.map_snd, Subgroup.coe_subtype]
      show sign (phiPerm x.1.1) = sign (phiPerm x.1.2)
      rw [phi_sign, phi_sign]; exact hx)

lemma psi_surj : Function.Surjective psi := by
  rintro ⟨⟨π₁, π₂⟩, hπ⟩
  have hs := mem_gamma_gen.mp hπ
  obtain ⟨σ, hσ⟩ := phi_surj π₁
  obtain ⟨τ, hτ⟩ := phi_surj π₂
  refine ⟨⟨(σ, τ), mem_gamma_gen.mpr ?_⟩, ?_⟩
  · show sign σ = sign τ
    rw [← phi_sign, hσ, ← phi_sign τ, hτ]; exact hs
  · apply Subtype.ext
    show (phiPerm σ, phiPerm τ) = (π₁, π₂)
    rw [hσ, hτ]

theorem OMA.solution : type_of% @Arxiv.«2605.12342».conjecture_1.variants.rank_4_4 :=
  fun h₁ h₂ => transfer psi psi_surj h₁ h₂
