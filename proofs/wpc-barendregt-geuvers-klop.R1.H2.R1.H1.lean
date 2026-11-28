import OMAReductions.R_wpc_barendregt_geuvers_klop_R1_H2_R1
/- Adapted from OpenAI openai/math, commit 3344da59991ed94f9ba711217b29c1d760badfa6, lean/OAI/Computability/TypeSystem, Apache-2.0. -/

namespace OMA
namespace S_wpc_barendregt_geuvers_klop
universe u



namespace Expr

variable {S : Type u}

@[simp] theorem liftRen_zero (ρ : Nat → Nat) : liftRen ρ 0 = 0 := rfl
@[simp] theorem liftRen_succ (ρ : Nat → Nat) (n : Nat) :
    liftRen ρ (n + 1) = ρ n + 1 := rfl

@[simp] theorem liftRen_id : liftRen id = id := by
  funext n
  cases n <;> rfl

theorem liftRen_comp (ρ τ : Nat → Nat) : liftRen (ρ ∘ τ) = liftRen ρ ∘ liftRen τ := by
  funext n
  cases n <;> rfl

@[simp] theorem rename_id (M : Expr S) : rename id M = M := by
  induction M with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [rename, ihf, iha]
  | lam A b ihA ihb => simp [rename, ihA, ihb]
  | pi A B ihA ihB => simp [rename, ihA, ihB]

theorem rename_comp (M : Expr S) (ρ τ : Nat → Nat) :
    rename ρ (rename τ M) = rename (ρ ∘ τ) M := by
  induction M generalizing ρ τ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [rename, ihf, iha]
  | lam A b ihA ihb => simp only [rename, ihA, ihb, liftRen_comp]
  | pi A B ihA ihB => simp only [rename, ihA, ihB, liftRen_comp]

@[simp] theorem liftSub_zero (σ : Nat → Expr S) : liftSub σ 0 = var 0 := rfl
@[simp] theorem liftSub_succ (σ : Nat → Expr S) (n : Nat) :
    liftSub σ (n + 1) = rename Nat.succ (σ n) := rfl

@[simp] theorem liftSub_var : liftSub (var : Nat → Expr S) = var := by
  funext n
  cases n <;> rfl

@[simp] theorem subst_var (M : Expr S) : subst var M = M := by
  induction M with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [subst, ihf, iha]
  | lam A b ihA ihb => simp [subst, ihA, ihb]
  | pi A B ihA ihB => simp [subst, ihA, ihB]

theorem subst_rename (M : Expr S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    subst σ (rename ρ M) = subst (σ ∘ ρ) M := by
  have hlift : ∀ (σ : Nat → Expr S) (ρ : Nat → Nat),
      liftSub σ ∘ liftRen ρ = liftSub (σ ∘ ρ) := by
    intro σ ρ
    funext n
    cases n <;> rfl
  induction M generalizing σ ρ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [rename, subst, ihf, iha]
  | lam A b ihA ihb => simp only [rename, subst, ihA, ihb, hlift]
  | pi A B ihA ihB => simp only [rename, subst, ihA, ihB, hlift]

theorem rename_subst (M : Expr S) (ρ : Nat → Nat) (σ : Nat → Expr S) :
    rename ρ (subst σ M) = subst (fun n => rename ρ (σ n)) M := by
  have hlift : ∀ (ρ : Nat → Nat) (σ : Nat → Expr S),
      (fun n => rename (liftRen ρ) (liftSub σ n)) =
        liftSub (fun n => rename ρ (σ n)) := by
    intro ρ σ
    funext n
    cases n with
    | zero => rfl
    | succ n =>
        simp only [liftSub_succ, rename_comp]
        rfl
  induction M generalizing ρ σ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [subst, rename, ihf, iha]
  | lam A b ihA ihb => simp only [subst, rename, ihA, ihb, hlift]
  | pi A B ihA ihB => simp only [subst, rename, ihA, ihB, hlift]

theorem subst_subst (M : Expr S) (σ τ : Nat → Expr S) :
    subst σ (subst τ M) = subst (fun n => subst σ (τ n)) M := by
  have hlift : ∀ (σ τ : Nat → Expr S),
      (fun n => subst (liftSub σ) (liftSub τ n)) =
        liftSub (fun n => subst σ (τ n)) := by
    intro σ τ
    funext n
    cases n with
    | zero => rfl
    | succ n =>
        simp only [liftSub_succ, subst_rename, rename_subst]
        rfl
  induction M generalizing σ τ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [subst, ihf, iha]
  | lam A b ihA ihb => simp only [subst, ihA, ihb, hlift]
  | pi A B ihA ihB => simp only [subst, ihA, ihB, hlift]

theorem instantiate_rename (b a : Expr S) (ρ : Nat → Nat) :
    (b.rename (liftRen ρ)).instantiate (a.rename ρ) = (b.instantiate a).rename ρ := by
  simp only [instantiate, subst_rename, rename_subst]
  congr 1
  funext n
  cases n <;> rfl

theorem instantiate_subst (b a : Expr S) (σ : Nat → Expr S) :
    (b.subst (liftSub σ)).instantiate (a.subst σ) = (b.instantiate a).subst σ := by
  simp only [instantiate, subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [liftSub_succ, subst_rename]
      exact subst_var (σ n)

end Expr

namespace Beta

variable {S : Type u} {M N : Expr S}

theorem rename (h : Beta M N) (ρ : Nat → Nat) : Beta (M.rename ρ) (N.rename ρ) := by
  induction h generalizing ρ with
  | head A b a =>
      simpa only [Expr.rename, ← Expr.instantiate_rename] using
        (Beta.head (A.rename ρ) (b.rename (Expr.liftRen ρ)) (a.rename ρ))
  | app_left _ ih => exact .app_left (ih ρ)
  | app_right _ ih => exact .app_right (ih ρ)
  | lam_domain _ ih => exact .lam_domain (ih ρ)
  | lam_body _ ih => exact .lam_body (ih (Expr.liftRen ρ))
  | pi_domain _ ih => exact .pi_domain (ih ρ)
  | pi_body _ ih => exact .pi_body (ih (Expr.liftRen ρ))

theorem subst (h : Beta M N) (σ : Nat → Expr S) : Beta (M.subst σ) (N.subst σ) := by
  induction h generalizing σ with
  | head A b a =>
      simpa only [Expr.subst, ← Expr.instantiate_subst] using
        (Beta.head (A.subst σ) (b.subst (Expr.liftSub σ)) (a.subst σ))
  | app_left _ ih => exact .app_left (ih σ)
  | app_right _ ih => exact .app_right (ih σ)
  | lam_domain _ ih => exact .lam_domain (ih σ)
  | lam_body _ ih => exact .lam_body (ih (Expr.liftSub σ))
  | pi_domain _ ih => exact .pi_domain (ih σ)
  | pi_body _ ih => exact .pi_body (ih (Expr.liftSub σ))

end Beta

end S_wpc_barendregt_geuvers_klop

end OMA



namespace OMA

namespace S_wpc_barendregt_geuvers_klop

universe u

/-- Parallel reduction is used only to establish the beta metatheory. -/
inductive Parallel {S : Type u} : Expr S → Expr S → Prop
  | var (n) : Parallel (.var n) (.var n)
  | sort (s) : Parallel (.sort s) (.sort s)
  | app {f f' a a'} : Parallel f f' → Parallel a a' →
      Parallel (.app f a) (.app f' a')
  | lam {A A' b b'} : Parallel A A' → Parallel b b' →
      Parallel (.lam A b) (.lam A' b')
  | pi {A A' B B'} : Parallel A A' → Parallel B B' →
      Parallel (.pi A B) (.pi A' B')
  | head {b b' a a'} (A) : Parallel b b' → Parallel a a' →
      Parallel (.app (.lam A b) a) (b'.instantiate a')

namespace Parallel

variable {S : Type u} {M N : Expr S}

theorem refl (M : Expr S) : Parallel M M := by
  induction M with
  | var n => exact .var n
  | sort s => exact .sort s
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ ihA ihB => exact .pi ihA ihB

theorem of_beta (h : Beta M N) : Parallel M N := by
  induction h with
  | head A b a => exact .head A (refl b) (refl a)
  | app_left _ ih => exact .app ih (refl _)
  | app_right _ ih => exact .app (refl _) ih
  | lam_domain _ ih => exact .lam ih (refl _)
  | lam_body _ ih => exact .lam (refl _) ih
  | pi_domain _ ih => exact .pi ih (refl _)
  | pi_body _ ih => exact .pi (refl _) ih

theorem rename (h : Parallel M N) (ρ : Nat → Nat) :
    Parallel (M.rename ρ) (N.rename ρ) := by
  induction h generalizing ρ with
  | var n => exact .var _
  | sort s => exact .sort _
  | app _ _ ihf iha => exact .app (ihf ρ) (iha ρ)
  | lam _ _ ihA ihb => exact .lam (ihA ρ) (ihb (Expr.liftRen ρ))
  | pi _ _ ihA ihB => exact .pi (ihA ρ) (ihB (Expr.liftRen ρ))
  | head A _ _ ihb iha =>
      simpa only [Expr.rename, ← Expr.instantiate_rename] using
        (Parallel.head (A.rename ρ) (ihb (Expr.liftRen ρ)) (iha ρ))

theorem subst (h : Parallel M N) (σ τ : Nat → Expr S)
    (hστ : ∀ n, Parallel (σ n) (τ n)) : Parallel (M.subst σ) (N.subst τ) := by
  have hlift (σ τ : Nat → Expr S) (hστ : ∀ n, Parallel (σ n) (τ n)) :
      ∀ n, Parallel (Expr.liftSub σ n) (Expr.liftSub τ n) := by
    intro n
    cases n with
    | zero => exact .var 0
    | succ n => exact (hστ n).rename Nat.succ
  induction h generalizing σ τ with
  | var n => exact hστ n
  | sort s => exact .sort s
  | app _ _ ihf iha => exact .app (ihf σ τ hστ) (iha σ τ hστ)
  | lam _ _ ihA ihb => exact .lam (ihA σ τ hστ) (ihb _ _ (hlift σ τ hστ))
  | pi _ _ ihA ihB => exact .pi (ihA σ τ hστ) (ihB _ _ (hlift σ τ hστ))
  | head A _ _ ihb iha =>
      simpa only [Expr.subst, ← Expr.instantiate_subst] using
        (Parallel.head (A.subst σ) (ihb _ _ (hlift σ τ hστ)) (iha σ τ hστ))

theorem instantiate {b b' a a' : Expr S} (hb : Parallel b b') (ha : Parallel a a') :
    Parallel (b.instantiate a) (b'.instantiate a') := by
  apply hb.subst
  intro n
  cases n with
  | zero => exact ha
  | succ n => exact .var n

end Parallel

namespace Expr

variable {S : Type u}

/-- Takahashi's complete development, including type annotations. -/
def develop : Expr S → Expr S
  | var n => var n
  | sort s => sort s
  | app (lam _ b) a => (develop b).instantiate (develop a)
  | app f a => app (develop f) (develop a)
  | lam A b => lam (develop A) (develop b)
  | pi A B => pi (develop A) (develop B)

end Expr

namespace Parallel

variable {S : Type u} {M N : Expr S}

theorem triangle (h : Parallel M N) : Parallel N M.develop := by
  induction h with
  | var n => exact .var n
  | sort s => exact .sort s
  | @app f f' a a' hf ha ihf iha =>
      cases f with
      | var n => exact .app ihf iha
      | sort s => exact .app ihf iha
      | app f b => exact .app ihf iha
      | pi A B => exact .app ihf iha
      | lam A b =>
          cases hf with
          | lam hA hb =>
              cases ihf with
              | lam ihA ihb => exact .head _ ihb iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | head A _ _ ihb iha => exact ihb.instantiate iha

theorem diamond {a b c : Expr S} (hab : Parallel a b) (hac : Parallel a c) :
    ∃ d, Parallel b d ∧ Parallel c d := ⟨a.develop, hab.triangle, hac.triangle⟩

end Parallel

abbrev Reduces {S : Type u} := Relation.ReflTransGen (@Beta S)

namespace Reduces

variable {S : Type u} {f f' a a' A A' b b' : Expr S}

theorem app (hf : Reduces f f') (ha : Reduces a a') :
    Reduces (.app f a) (.app f' a') := by
  exact (hf.lift (fun x => Expr.app x a) (fun _ _ h => Beta.app_left h)).trans
    (ha.lift (fun x => Expr.app f' x) (fun _ _ h => Beta.app_right h))

theorem lam (hA : Reduces A A') (hb : Reduces b b') :
    Reduces (.lam A b) (.lam A' b') := by
  exact (hA.lift (fun x => Expr.lam x b) (fun _ _ h => Beta.lam_domain h)).trans
    (hb.lift (fun x => Expr.lam A' x) (fun _ _ h => Beta.lam_body h))

theorem pi (hA : Reduces A A') (hb : Reduces b b') :
    Reduces (.pi A b) (.pi A' b') := by
  exact (hA.lift (fun x => Expr.pi x b) (fun _ _ h => Beta.pi_domain h)).trans
    (hb.lift (fun x => Expr.pi A' x) (fun _ _ h => Beta.pi_body h))

theorem rename {M N : Expr S} (h : Reduces M N) (ρ : Nat → Nat) :
    Reduces (M.rename ρ) (N.rename ρ) := h.lift _ (fun _ _ h => h.rename ρ)

theorem subst {M N : Expr S} (h : Reduces M N) (σ : Nat → Expr S) :
    Reduces (M.subst σ) (N.subst σ) := h.lift _ (fun _ _ h => h.subst σ)

end Reduces

namespace Parallel

variable {S : Type u} {M N : Expr S}

theorem reduces (h : Parallel M N) : Reduces M N := by
  induction h with
  | var n => exact .refl
  | sort s => exact .refl
  | app _ _ ihf iha => exact Reduces.app ihf iha
  | lam _ _ ihA ihb => exact Reduces.lam ihA ihb
  | pi _ _ ihA ihB => exact Reduces.pi ihA ihB
  | head A _ _ ihb iha =>
      exact (Reduces.app (Reduces.lam .refl ihb) iha).tail (.head _ _ _)

theorem rtc_reduces {M N : Expr S} (h : Relation.ReflTransGen Parallel M N) :
    Reduces M N := Relation.reflTransGen_closed (fun _ _ h => h.reduces) _ _ h

end Parallel

namespace Reduces

variable {S : Type u} {M N : Expr S}

theorem parallel (h : Reduces M N) : Relation.ReflTransGen Parallel M N :=
  Relation.ReflTransGen.mono (fun _ _ h => Parallel.of_beta h) _ _ h

theorem confluent {a b c : Expr S} (hab : Reduces a b) (hac : Reduces a c) :
    Relation.Join Reduces b c := by
  have hd : ∀ a b c : Expr S, Parallel a b → Parallel a c →
      ∃ d, Relation.ReflGen Parallel b d ∧ Relation.ReflTransGen Parallel c d := by
    intro a b c hab hac
    obtain ⟨d, hb, hc⟩ := Parallel.diamond hab hac
    exact ⟨d, .single hb, .single hc⟩
  obtain ⟨d, hb, hc⟩ := Relation.church_rosser hd hab.parallel hac.parallel
  exact ⟨d, Parallel.rtc_reduces hb, Parallel.rtc_reduces hc⟩

end Reduces

namespace Converts

variable {S : Type u} {M N : Expr S}

theorem join (h : Converts M N) : Relation.Join Reduces M N := by
  induction h with
  | rel a b h => exact ⟨b, .single h, .refl⟩
  | refl a => exact ⟨a, .refl, .refl⟩
  | symm a b _ ih =>
      obtain ⟨c, ha, hb⟩ := ih
      exact ⟨c, hb, ha⟩
  | trans a b c _ _ ih₁ ih₂ =>
      obtain ⟨d, ha, hb⟩ := ih₁
      obtain ⟨e, hb', hc⟩ := ih₂
      obtain ⟨f, hd, he⟩ := Reduces.confluent hb hb'
      exact ⟨f, ha.trans hd, hc.trans he⟩

end Converts

namespace Normal

variable {S : Type u} {M N : Expr S}

theorem reduces_eq (hM : Normal M) (h : Reduces M N) : M = N := by
  induction h with
  | refl => rfl
  | @tail N N' _ h ih => exact False.elim (hM N' (ih ▸ h))

theorem eq_of_converts (hM : Normal M) (hN : Normal N) (h : Converts M N) : M = N := by
  obtain ⟨K, hMK, hNK⟩ := h.join
  exact (hM.reduces_eq hMK).trans (hN.reduces_eq hNK).symm

end Normal

namespace Reduces

variable {S : Type u} {A B N : Expr S}

theorem pi_inv (h : Reduces (.pi A B) N) :
    ∃ A' B', N = .pi A' B' ∧ Reduces A A' ∧ Reduces B B' := by
  induction h with
  | refl => exact ⟨A, B, rfl, .refl, .refl⟩
  | tail _ h ih =>
      obtain ⟨A', B', rfl, hA, hB⟩ := ih
      cases h with
      | pi_domain h => exact ⟨_, _, rfl, hA.tail h, hB⟩
      | pi_body h => exact ⟨_, _, rfl, hA, hB.tail h⟩

theorem converts {M N : Expr S} (h : Reduces M N) : Converts M N :=
  Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ h

end Reduces

namespace Converts

variable {S : Type u}

theorem product_compatibility {A B A' B' : Expr S}
    (h : Converts (.pi A B) (.pi A' B')) : Converts A A' ∧ Converts B B' := by
  obtain ⟨T, hT, hT'⟩ := h.join
  obtain ⟨D, E, hDE, hA, hB⟩ := hT.pi_inv
  obtain ⟨D', E', hDE', hA', hB'⟩ := hT'.pi_inv
  have heq := Expr.pi.inj (hDE.symm.trans hDE')
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨.trans _ _ _ hA.converts (.symm _ _ hA'.converts),
    .trans _ _ _ hB.converts (.symm _ _ hB'.converts)⟩

end Converts



namespace StronglyNormalizing

variable {S : Type u} {M N : Expr S}

theorem step (hM : StronglyNormalizing M) (h : Beta M N) : StronglyNormalizing N :=
  hM.inv h

theorem reduces (hM : StronglyNormalizing M) (h : Reduces M N) : StronglyNormalizing N := by
  induction h with
  | refl => exact hM
  | tail _ h ih => exact ih.step h

/-- SN of an image reflects along any map preserving individual reduction steps. -/
theorem of_map {f : Expr S → Expr S}
    (hf : ∀ {M N}, Beta M N → Beta (f M) (f N)) {M : Expr S}
    (h : StronglyNormalizing (f M)) : StronglyNormalizing M := by
  have aux : ∀ N, StronglyNormalizing N → ∀ M, f M = N → StronglyNormalizing M := by
    intro N hN
    induction hN with
    | intro N _ ih =>
        intro M heq
        apply Acc.intro
        intro M' hM
        exact ih (f M') (heq ▸ hf hM) M' rfl
  exact aux _ h M rfl

theorem app_left {f a : Expr S} (h : StronglyNormalizing (.app f a)) :
    StronglyNormalizing f := of_map (fun h => Beta.app_left h) h

theorem app_right {f a : Expr S} (h : StronglyNormalizing (.app f a)) :
    StronglyNormalizing a := of_map (fun h => Beta.app_right h) h

theorem lam_domain {A b : Expr S} (h : StronglyNormalizing (.lam A b)) :
    StronglyNormalizing A := of_map (fun h => Beta.lam_domain h) h

theorem lam_body {A b : Expr S} (h : StronglyNormalizing (.lam A b)) :
    StronglyNormalizing b := of_map (fun h => Beta.lam_body h) h

theorem pi_domain {A B : Expr S} (h : StronglyNormalizing (.pi A B)) :
    StronglyNormalizing A := of_map (fun h => Beta.pi_domain h) h

theorem pi_body {A B : Expr S} (h : StronglyNormalizing (.pi A B)) :
    StronglyNormalizing B := of_map (fun h => Beta.pi_body h) h

theorem of_subst (σ : Nat → Expr S) (h : StronglyNormalizing (M.subst σ)) :
    StronglyNormalizing M := of_map (fun h => h.subst σ) h

theorem of_rename (ρ : Nat → Nat) (h : StronglyNormalizing (M.rename ρ)) :
    StronglyNormalizing M := of_map (fun h => h.rename ρ) h

theorem lam {A b : Expr S} (hA : StronglyNormalizing A) (hb : StronglyNormalizing b) :
    StronglyNormalizing (.lam A b) := by
  induction hA generalizing b with
  | intro A hA ihA =>
      induction hb with
      | intro b hb ihb =>
          apply Acc.intro
          intro N hN
          cases hN with
          | lam_domain h => exact ihA _ h (Acc.intro _ hb)
          | lam_body h => exact ihb _ h

theorem pi {A B : Expr S} (hA : StronglyNormalizing A) (hB : StronglyNormalizing B) :
    StronglyNormalizing (.pi A B) := by
  induction hA generalizing B with
  | intro A hA ihA =>
      induction hB with
      | intro B hB ihB =>
          apply Acc.intro
          intro N hN
          cases hN with
          | pi_domain h => exact ihA _ h (Acc.intro _ hB)
          | pi_body h => exact ihB _ h

end StronglyNormalizing

namespace Expr

variable {S : Type u}

def apps (f : Expr S) : List (Expr S) → Expr S
  | [] => f
  | a :: as => apps (.app f a) as

@[simp] theorem apps_nil (f : Expr S) : apps f [] = f := rfl
@[simp] theorem apps_cons (f a : Expr S) (as : List (Expr S)) :
    apps f (a :: as) = apps (.app f a) as := rfl

theorem apps_append (f : Expr S) (as bs : List (Expr S)) :
    apps f (as ++ bs) = apps (apps f as) bs := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact ih (.app f a)

end Expr

/-- Exactly one reduction step in one term of an argument list. -/
inductive ArgsStep {S : Type u} : List (Expr S) → List (Expr S) → Prop
  | head {a a' as} : Beta a a' → ArgsStep (a :: as) (a' :: as)
  | tail {a as as'} : ArgsStep as as' → ArgsStep (a :: as) (a :: as')

def StronglyNormalizingArgs {S : Type u} (as : List (Expr S)) : Prop :=
  Acc (fun bs as => ArgsStep as bs) as

namespace Beta

variable {S : Type u} {f f' : Expr S}

theorem apps (h : Beta f f') (as : List (Expr S)) :
    Beta (f.apps as) (f'.apps as) := by
  induction as generalizing f f' with
  | nil => exact h
  | cons a as ih => exact ih (.app_left h)

/-- If the head is not a lambda, a spine step comes from its head or an argument. -/
theorem apps_inv {as : List (Expr S)} {N : Expr S}
    (hf : ∀ A b, f ≠ .lam A b) (h : Beta (f.apps as) N) :
    (∃ f', Beta f f' ∧ N = f'.apps as) ∨
    (∃ as', ArgsStep as as' ∧ N = f.apps as') := by
  induction as generalizing f N with
  | nil => exact .inl ⟨N, h, rfl⟩
  | cons a as ih =>
      obtain ⟨g, hg, rfl⟩ | ⟨as', has, rfl⟩ :=
        ih (f := .app f a) (by intro A b heq; cases heq) h
      · cases hg with
        | head A b a => exact False.elim (hf A b rfl)
        | app_left hg => exact .inl ⟨_, hg, rfl⟩
        | app_right hg => exact .inr ⟨_, .head hg, rfl⟩
      · exact .inr ⟨_, .tail has, rfl⟩

end Beta

namespace ArgsStep

variable {S : Type u} {as bs : List (Expr S)}

theorem apps (h : ArgsStep as bs) (f : Expr S) : Beta (f.apps as) (f.apps bs) := by
  induction h generalizing f with
  | head h => exact (Beta.app_right h).apps _
  | tail h ih => exact ih (.app f _)

end ArgsStep

namespace Reduces

variable {S : Type u} {f f' : Expr S}

theorem apps (h : Reduces f f') (as : List (Expr S)) :
    Reduces (f.apps as) (f'.apps as) := h.lift _ (fun _ _ h => h.apps as)

end Reduces

namespace StronglyNormalizingArgs

variable {S : Type u}

theorem nil : StronglyNormalizingArgs ([] : List (Expr S)) := by
  apply Acc.intro
  intro bs h
  cases h

theorem cons {a : Expr S} {as : List (Expr S)} (ha : StronglyNormalizing a)
    (has : StronglyNormalizingArgs as) : StronglyNormalizingArgs (a :: as) := by
  induction ha generalizing as with
  | intro a ha iha =>
      induction has with
      | intro as has ihas =>
          apply Acc.intro
          intro bs h
          cases h with
          | head h => exact iha _ h (Acc.intro _ has)
          | tail h => exact ihas _ h

theorem of_forall {as : List (Expr S)} (h : ∀ a ∈ as, StronglyNormalizing a) :
    StronglyNormalizingArgs as := by
  induction as with
  | nil => exact nil
  | cons a as ih =>
      exact cons (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

theorem head {a : Expr S} {as : List (Expr S)}
    (h : StronglyNormalizingArgs (a :: as)) : StronglyNormalizing a :=
  Subrelation.accessible (fun h => ArgsStep.head h)
    (InvImage.accessible (fun a => a :: as) h)

theorem tail {a : Expr S} {as : List (Expr S)}
    (h : StronglyNormalizingArgs (a :: as)) : StronglyNormalizingArgs as :=
  Subrelation.accessible (fun h => ArgsStep.tail h)
    (InvImage.accessible (fun as => a :: as) h)

theorem of_mem {a : Expr S} {as : List (Expr S)}
    (h : StronglyNormalizingArgs as) (ha : a ∈ as) : StronglyNormalizing a := by
  induction as with
  | nil => cases ha
  | cons b bs ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact h.head
      · exact ih h.tail ha

end StronglyNormalizingArgs

namespace StronglyNormalizing

variable {S : Type u}

theorem apps_head {f : Expr S} {as : List (Expr S)}
    (h : StronglyNormalizing (f.apps as)) : StronglyNormalizing f :=
  of_map (fun h => h.apps as) h

theorem var_apps (n : Nat) {as : List (Expr S)} (has : StronglyNormalizingArgs as) :
    StronglyNormalizing ((Expr.var n : Expr S).apps as) := by
  induction has with
  | intro as has ih =>
      apply Acc.intro
      intro N hN
      obtain ⟨f, hf, rfl⟩ | ⟨bs, hbs, rfl⟩ :=
        hN.apps_inv (by intro A b heq; cases heq)
      · cases hf
      · exact ih _ hbs

/-- The source's head-expansion lemma, with any finite argument spine.
The proof uses nested accessibility induction, not a raised recursion budget
or an assumed maximal reduction height. -/
theorem head_expansion {A b a : Expr S} {as : List (Expr S)}
    (hA : StronglyNormalizing A) (hb : StronglyNormalizing b)
    (ha : StronglyNormalizing a) (has : StronglyNormalizingArgs as)
    (hc : StronglyNormalizing ((b.instantiate a).apps as)) :
    StronglyNormalizing ((Expr.app (.lam A b) a).apps as) := by
  induction hA generalizing b a as with
  | intro A hA ihA =>
      induction hb generalizing a as with
      | intro b hb ihb =>
          induction ha generalizing as with
          | intro a ha iha =>
              induction has with
              | intro as has ihas =>
                  apply Acc.intro
                  intro N hN
                  obtain ⟨f, hf, rfl⟩ | ⟨bs, hbs, rfl⟩ :=
                    hN.apps_inv (by intro D c heq; cases heq)
                  · cases hf with
                    | head => exact hc
                    | app_left hf =>
                        cases hf with
                        | lam_domain h =>
                            exact ihA _ h (Acc.intro _ hb) (Acc.intro _ ha)
                              (Acc.intro _ has) hc
                        | lam_body h =>
                            exact ihb _ h (Acc.intro _ ha) (Acc.intro _ has)
                              (hc.step ((h.subst (Expr.single a)).apps as))
                    | app_right h =>
                        exact iha _ h (Acc.intro _ has)
                          (hc.reduces ((Parallel.instantiate (Parallel.refl b)
                            (Parallel.of_beta h)).reduces.apps as))
                  · exact ihas _ hbs (hc.step (hbs.apps _))

end StronglyNormalizing

namespace Expr
variable {S : Type u}
/-- Only literal syntax descent, including both annotations. -/
inductive Child : Expr S → Expr S → Prop
  | app_left (f a) : Child f (.app f a)
  | app_right (f a) : Child a (.app f a)
  | lam_domain (D m) : Child D (.lam D m)
  | lam_body (D m) : Child m (.lam D m)
  | pi_domain (D E) : Child D (.pi D E)
  | pi_body (D E) : Child E (.pi D E)

inductive Subterm : Expr S → Expr S → Prop
  | refl (M) : Subterm M M
  | tail {M N L} : Subterm M N → Child N L → Subterm M L

namespace Child
variable {M N M' : Expr S}
theorem beta_lift (h : Child M N) (hr : Beta M M') :
    ∃ N', Beta N N' ∧ Child M' N' := by
  cases h with
  | app_left f a => exact ⟨_,.app_left hr,.app_left _ _⟩
  | app_right f a => exact ⟨_,.app_right hr,.app_right _ _⟩
  | lam_domain D m => exact ⟨_,.lam_domain hr,.lam_domain _ _⟩
  | lam_body D m => exact ⟨_,.lam_body hr,.lam_body _ _⟩
  | pi_domain D E => exact ⟨_,.pi_domain hr,.pi_domain _ _⟩
  | pi_body D E => exact ⟨_,.pi_body hr,.pi_body _ _⟩

theorem sn (h : Child M N) (hs : StronglyNormalizing N) : StronglyNormalizing M := by
  cases h with
  | app_left => exact hs.app_left
  | app_right => exact hs.app_right
  | lam_domain => exact hs.lam_domain
  | lam_body => exact hs.lam_body
  | pi_domain => exact hs.pi_domain
  | pi_body => exact hs.pi_body
end Child

namespace Subterm
variable {M N L M' : Expr S}
theorem trans (h : Subterm M N) (h' : Subterm N L) : Subterm M L := by
  induction h' with
  | refl => exact h
  | tail _ hc ih => exact .tail ih hc

theorem of_child (h : Child M N) : Subterm M N := .tail (.refl M) h

theorem beta_lift (h : Subterm M N) (hr : Beta M M') :
    ∃ N', Beta N N' ∧ Subterm M' N' := by
  induction h with
  | refl => exact ⟨_,hr,.refl _⟩
  | tail h hc ih =>
    obtain ⟨N',hr',hs'⟩ := ih
    obtain ⟨L',hr'',hc'⟩ := hc.beta_lift hr'
    exact ⟨L',hr'',.tail hs' hc'⟩

theorem sn (h : Subterm M N) (hs : StronglyNormalizing N) : StronglyNormalizing M := by
  induction h with
  | refl => exact hs
  | tail h hc ih => exact ih (hc.sn hs)
end Subterm
end Expr

namespace StronglyNormalizing
variable {S : Type u}
/-- The manuscript's simultaneous reduction-height/syntax-size induction,
proved directly from accessibility, without choosing a height or raising limits. -/
theorem induction_subterms {Q : Expr S → Prop}
    (step : ∀ M, StronglyNormalizing M → (∀ N, Beta M N → Q N) →
      (∀ N, Expr.Child N M → Q N) → Q M)
    {M : Expr S} (hs : StronglyNormalizing M) : Q M := by
  have aux : ∀ M : Expr S, StronglyNormalizing M → ∀ N, Expr.Subterm N M → Q N := by
    intro M hs
    induction hs with
    | intro M hred ih =>
      intro N
      have hreds (N : Expr S) (hNM : Expr.Subterm N M) : ∀ L, Beta N L → Q L := by
        intro L hr
        obtain ⟨M',hr',hLM'⟩ := hNM.beta_lift hr
        exact ih M' hr' L hLM'
      induction N with
      | var n =>
        intro hn
        exact step _ (hn.sn (.intro M hred)) (hreds _ hn) (fun _ hc => by cases hc)
      | sort s =>
        intro hn
        exact step _ (hn.sn (.intro M hred)) (hreds _ hn) (fun _ hc => by cases hc)
      | app f a ihf iha =>
        intro hn
        apply step _ (hn.sn (.intro M hred)) (hreds _ hn)
        intro L hc
        cases hc with
        | app_left => exact ihf ((Expr.Subterm.of_child (.app_left f a)).trans hn)
        | app_right => exact iha ((Expr.Subterm.of_child (.app_right f a)).trans hn)
      | lam D m ihD ihm =>
        intro hn
        apply step _ (hn.sn (.intro M hred)) (hreds _ hn)
        intro L hc
        cases hc with
        | lam_domain => exact ihD ((Expr.Subterm.of_child (.lam_domain D m)).trans hn)
        | lam_body => exact ihm ((Expr.Subterm.of_child (.lam_body D m)).trans hn)
      | pi D E ihD ihE =>
        intro hn
        apply step _ (hn.sn (.intro M hred)) (hreds _ hn)
        intro L hc
        cases hc with
        | pi_domain => exact ihD ((Expr.Subterm.of_child (.pi_domain D E)).trans hn)
        | pi_body => exact ihE ((Expr.Subterm.of_child (.pi_body D E)).trans hn)
  exact aux M hs M (.refl M)
/-- The child hypothesis can equivalently cover every proper syntactic part. -/
theorem induction_descendants {Q : Expr S → Prop}
    (step : ∀ M, StronglyNormalizing M → (∀ N, Beta M N → Q N) →
      (∀ N, (∃ K, Expr.Child K M ∧ Expr.Subterm N K) → Q N) → Q M)
    {M : Expr S} (hs : StronglyNormalizing M) : Q M := by
  have h : Q M ∧ ∀ N, Expr.Subterm N M → Q N := by
    apply induction_subterms (Q := fun M => Q M ∧ ∀ N, Expr.Subterm N M → Q N) _ hs
    intro M hM hr hc
    have hq : Q M := step M hM (fun N h => (hr N h).1) (by
      rintro N ⟨K,hK,hN⟩
      exact (hc K hK).2 N hN)
    refine ⟨hq, ?_⟩
    intro N hN
    cases hN with
    | refl => exact hq
    | tail hN hK => exact (hc _ hK).2 _ hN
  exact h.1
end StronglyNormalizing
end S_wpc_barendregt_geuvers_klop

end OMA



namespace OMA

namespace S_wpc_barendregt_geuvers_klop

universe u

/-- A declaration's type viewed in the full newest-first context. -/
inductive Lookup {S : Type u} : List (Expr S) → Nat → Expr S → Prop
  | zero (A Γ) : Lookup (A :: Γ) 0 (A.rename Nat.succ)
  | succ {Γ n A} (B) : Lookup Γ n A → Lookup (B :: Γ) (n + 1) (A.rename Nat.succ)

namespace HasType

variable {S : Type u} {P : Specification S}

theorem sort_of_valid {Γ : List (Expr S)} (hΓ : ValidContext P Γ)
    {s t : S} (hst : P.sortAxioms s t) : HasType P Γ (.sort s) (.sort t) := by
  induction hΓ with
  | nil => exact .ax hst
  | cons _ hA ih => exact .weaken ih hA

/-- Domain generation alone precedes substitution and does not need
any exchange or context-substitution theorem. -/
theorem product_domain {Γ : List (Expr S)} {M T : Expr S} (h : HasType P Γ M T) :
    ∀ A B, M = .pi A B → ∃ s, HasType P Γ A (.sort s) := by
  induction h with
  | ax h => intro A B heq; cases heq
  | var h ih => intro A B heq; cases heq
  | @weaken Γ M T C s hM hC ihM ihC =>
      intro A B heq
      cases M with
      | var n => cases heq
      | sort t => cases heq
      | app f a => cases heq
      | lam D b => cases heq
      | pi D E =>
          obtain ⟨rfl, rfl⟩ := Expr.pi.inj heq
          obtain ⟨t, ht⟩ := ihM D E rfl
          exact ⟨t, .weaken ht hC⟩
  | product hA hB hr ihA ihB =>
      intro A B heq
      cases heq
      exact ⟨_, hA⟩
  | abstraction hb hT ihb ihT => intro A B heq; cases heq
  | application hf ha ihf iha => intro A B heq; cases heq
  | conversion hM hB hconv ihM ihB => exact ihM

end HasType

namespace Converts

variable {S : Type u} {M N : Expr S}

theorem subst (h : Converts M N) (σ : Nat → Expr S) :
    Converts (M.subst σ) (N.subst σ) := by
  induction h with
  | rel a b h => exact .rel _ _ (h.subst σ)
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem rename (h : Converts M N) (ρ : Nat → Nat) :
    Converts (M.rename ρ) (N.rename ρ) := by
  induction h with
  | rel a b h => exact .rel _ _ (h.rename ρ)
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end Converts

/-- A simultaneous substitution respects each declared variable's exact type.
This is a premise only of the substitution metatheorem, not of the main target. -/
def TypedSubstitution {S : Type u} (P : Specification S)
    (Γ Δ : List (Expr S)) (σ : Nat → Expr S) : Prop :=
  ∀ n A, Lookup Γ n A → HasType P Δ (σ n) (A.subst σ)

namespace TypedSubstitution

variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}
    {σ : Nat → Expr S}

theorem tail {A : Expr S} (hσ : TypedSubstitution P (A :: Γ) Δ σ) :
    TypedSubstitution P Γ Δ (σ ∘ Nat.succ) := by
  intro n B hB
  have h := hσ (n + 1) (B.rename Nat.succ) (.succ A hB)
  simpa only [Expr.subst_rename, Function.comp_def] using h

theorem lift {A : Expr S} {s : S} (hσ : TypedSubstitution P Γ Δ σ)
    (hA : HasType P Δ (A.subst σ) (.sort s)) :
    TypedSubstitution P (A :: Γ) (A.subst σ :: Δ) (Expr.liftSub σ) := by
  intro n B hn
  cases hn with
  | zero =>
      have ht := HasType.var hA
      simpa only [Expr.liftSub_zero, Expr.subst_rename, Expr.rename_subst,
        Expr.liftSub_succ, Function.comp_def] using ht
  | succ C hn =>
      have ht := HasType.weaken (hσ _ _ hn) hA
      simpa only [Expr.liftSub_succ, Expr.rename_subst, Expr.subst_rename,
        Function.comp_def] using ht

end TypedSubstitution

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

theorem subst (h : HasType P Γ M T) {Δ : List (Expr S)}
    (hΔ : ValidContext P Δ) (σ : Nat → Expr S) (hσ : TypedSubstitution P Γ Δ σ) :
    HasType P Δ (M.subst σ) (T.subst σ) := by
  induction h generalizing Δ σ with
  | ax h => exact sort_of_valid hΔ h
  | var h ih => exact hσ _ _ (.zero _ _)
  | weaken hM hA ihM ihA =>
      simpa only [Expr.subst_rename] using ihM hΔ (σ ∘ Nat.succ) hσ.tail
  | product hA hB hr ihA ihB =>
      have hA' := ihA hΔ σ hσ
      exact .product hA' (ihB (.cons hΔ hA') _ (hσ.lift hA')) hr
  | @abstraction Γ A b B s hb hprod ihb ihprod =>
      have hprod' := ihprod hΔ σ hσ
      obtain ⟨t, hA'⟩ := hprod'.product_domain _ _ rfl
      exact .abstraction (ihb (.cons hΔ hA') _ (hσ.lift hA')) hprod'
  | application hf ha ihf iha =>
      simpa only [Expr.subst, Expr.instantiate_subst] using
        (HasType.application (ihf hΔ σ hσ) (iha hΔ σ hσ))
  | conversion hM hB hconv ihM ihB =>
      exact .conversion (ihM hΔ σ hσ) (ihB hΔ σ hσ) (hconv.subst σ)

end HasType

namespace Expr

variable {S : Type u}

theorem subst_var_rename (M : Expr S) (ρ : Nat → Nat) :
    M.subst (var ∘ ρ) = M.rename ρ := by
  rw [← subst_rename, subst_var]

@[simp] theorem subst_lift_single (M a : Expr S) :
    (M.rename Nat.succ).subst (single a) = M := by
  rw [subst_rename]
  exact subst_var M

end Expr

namespace HasType

variable {S : Type u} {P : Specification S}

theorem lookup {Γ : List (Expr S)} (hΓ : ValidContext P Γ)
    {n : Nat} {A : Expr S} (hn : Lookup Γ n A) : HasType P Γ (.var n) A := by
  induction hΓ generalizing n A with
  | nil => cases hn
  | cons hΓ hB ih =>
      cases hn with
      | zero => exact .var hB
      | succ _ hn => exact .weaken (ih hn) hB

end HasType

namespace TypedSubstitution

variable {S : Type u} {P : Specification S}

theorem identity {Γ : List (Expr S)} (hΓ : ValidContext P Γ) :
    TypedSubstitution P Γ Γ Expr.var := by
  intro n A hn
  simpa only [Expr.subst_var] using HasType.lookup hΓ hn

theorem weaken {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) :
    TypedSubstitution P Γ (A :: Γ) (Expr.var ∘ Nat.succ) := by
  intro n B hn
  simpa only [Expr.subst_var_rename, Function.comp_apply, Expr.rename] using
    (HasType.weaken (HasType.lookup hA.valid hn) hA)

theorem single {Γ : List (Expr S)} {a A : Expr S} (ha : HasType P Γ a A) :
    TypedSubstitution P (A :: Γ) Γ (Expr.single a) := by
  intro n B hn
  cases hn with
  | zero => simpa only [Expr.single, Expr.subst_lift_single] using ha
  | succ _ hn =>
      simpa only [Expr.single, Expr.subst_lift_single] using HasType.lookup ha.valid hn

end TypedSubstitution

namespace HasType

section

variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}

theorem rename {M A : Expr S} (h : HasType P Γ M A)
    (hΔ : ValidContext P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasType P Δ (.var (ρ n)) (B.rename ρ)) :
    HasType P Δ (M.rename ρ) (A.rename ρ) := by
  have hσ : TypedSubstitution P Γ Δ (Expr.var ∘ ρ) := by
    intro n B hn
    simpa only [Expr.subst_var_rename, Function.comp_apply] using hρ n B hn
  simpa only [Expr.subst_var_rename] using h.subst hΔ (Expr.var ∘ ρ) hσ

theorem instantiate {A b B a : Expr S}
    (hb : HasType P (A :: Γ) b B) (ha : HasType P Γ a A) :
    HasType P Γ (b.instantiate a) (B.instantiate a) :=
  hb.subst ha.valid _ (TypedSubstitution.single ha)

theorem weaken_under {A D b B : Expr S} {s t : S}
    (hb : HasType P (A :: Γ) b B) (hA : HasType P Γ A (.sort s))
    (hD : HasType P Γ D (.sort t)) :
    HasType P (A.rename Nat.succ :: D :: Γ)
      (b.rename (Expr.liftRen Nat.succ)) (B.rename (Expr.liftRen Nat.succ)) := by
  have hA' : HasType P (D :: Γ) (A.subst (Expr.var ∘ Nat.succ)) (.sort s) := by
    simpa only [Expr.subst_var_rename, Expr.rename] using HasType.weaken hA hD
  have hσ := (TypedSubstitution.weaken hD).lift hA'
  have h := hb.subst (.cons (.cons hD.valid hD) hA') _ hσ
  have heq : Expr.liftSub (Expr.var ∘ Nat.succ : Nat → Expr S) =
      Expr.var ∘ Expr.liftRen Nat.succ := by
    funext n
    cases n <;> rfl
  simpa only [heq, Expr.subst_var_rename] using h

theorem context_head_conversion {A A' b B : Expr S} {s t : S}
    (hb : HasType P (A :: Γ) b B) (hA : HasType P Γ A (.sort s))
    (hA' : HasType P Γ A' (.sort t)) (hc : Converts A A') :
    HasType P (A' :: Γ) b B := by
  have hσ : TypedSubstitution P (A :: Γ) (A' :: Γ) Expr.var := by
    intro n D hn
    rw [Expr.subst_var]
    cases hn with
    | zero =>
        exact .conversion (.var hA') (.weaken hA hA')
          (.symm _ _ (hc.rename Nat.succ))
    | succ _ hn => exact .weaken (lookup hA.valid hn) hA'
  simpa only [Expr.subst_var] using hb.subst (.cons hA'.valid hA') _ hσ

end

variable {S : Type u} {P : Specification S}

/-- Generation is stated up to conversion, without any functionality premise. -/
def Generation (P : Specification S) (Γ : List (Expr S))
    (M T : Expr S) : Prop :=
  match M with
  | .var n => ∃ A, Lookup Γ n A ∧ Converts T A
  | .sort s => ∃ t, P.sortAxioms s t ∧ Converts T (.sort t)
  | .app f a => ∃ A B, HasType P Γ f (.pi A B) ∧ HasType P Γ a A ∧
      Converts T (B.instantiate a)
  | .lam A b => ∃ B s, HasType P (A :: Γ) b B ∧
      HasType P Γ (.pi A B) (.sort s) ∧ Converts T (.pi A B)
  | .pi A B => ∃ s₁ s₂ s₃, HasType P Γ A (.sort s₁) ∧
      HasType P (A :: Γ) B (.sort s₂) ∧ P.rule s₁ s₂ s₃ ∧
      Converts T (.sort s₃)

theorem generation {Γ : List (Expr S)} {M T : Expr S}
    (h : HasType P Γ M T) : Generation P Γ M T := by
  induction h with
  | ax h => exact ⟨_, h, .refl _⟩
  | var h ih => exact ⟨_, .zero _ _, .refl _⟩
  | @weaken Γ M T D s hM hD ihM ihD =>
      cases M with
      | var n =>
          obtain ⟨A, hA, hc⟩ := ihM
          exact ⟨_, .succ D hA, hc.rename Nat.succ⟩
      | sort t =>
          obtain ⟨t', ht, hc⟩ := ihM
          exact ⟨t', ht, hc.rename Nat.succ⟩
      | app f a =>
          obtain ⟨A, B, hf, ha, hc⟩ := ihM
          refine ⟨_, _, .weaken hf hD, .weaken ha hD, ?_⟩
          simpa only [Expr.instantiate_rename] using hc.rename Nat.succ
      | lam A b =>
          obtain ⟨B, t, hb, hPi, hc⟩ := ihM
          obtain ⟨r, hA⟩ := hPi.product_domain _ _ rfl
          exact ⟨_, t, hb.weaken_under hA hD, .weaken hPi hD,
            hc.rename Nat.succ⟩
      | pi A B =>
          obtain ⟨t₁, t₂, t₃, hA, hB, hr, hc⟩ := ihM
          exact ⟨t₁, t₂, t₃, .weaken hA hD, hB.weaken_under hA hD,
            hr, hc.rename Nat.succ⟩
  | product hA hB hr ihA ihB => exact ⟨_, _, _, hA, hB, hr, .refl _⟩
  | abstraction hb hPi ihb ihPi => exact ⟨_, _, hb, hPi, .refl _⟩
  | application hf ha ihf iha => exact ⟨_, _, hf, ha, .refl _⟩
  | @conversion Γ M A B s hM hB hc ihM ihB =>
      cases M with
      | var n =>
          obtain ⟨D, hD, hd⟩ := ihM
          exact ⟨D, hD, .trans _ _ _ (.symm _ _ hc) hd⟩
      | sort t =>
          obtain ⟨r, hr, hd⟩ := ihM
          exact ⟨r, hr, .trans _ _ _ (.symm _ _ hc) hd⟩
      | app f a =>
          obtain ⟨D, E, hf, ha, hd⟩ := ihM
          exact ⟨D, E, hf, ha, .trans _ _ _ (.symm _ _ hc) hd⟩
      | lam D b =>
          obtain ⟨E, r, hb, hPi, hd⟩ := ihM
          exact ⟨E, r, hb, hPi, .trans _ _ _ (.symm _ _ hc) hd⟩
      | pi D E =>
          obtain ⟨r₁, r₂, r₃, hD, hE, hr, hd⟩ := ihM
          exact ⟨r₁, r₂, r₃, hD, hE, hr, .trans _ _ _ (.symm _ _ hc) hd⟩

theorem generation_pi {Γ : List (Expr S)} {A B T : Expr S}
    (h : HasType P Γ (.pi A B) T) :
    ∃ s₁ s₂ s₃, HasType P Γ A (.sort s₁) ∧
      HasType P (A :: Γ) B (.sort s₂) ∧ P.rule s₁ s₂ s₃ ∧
      Converts T (.sort s₃) := h.generation

theorem generation_lam {Γ : List (Expr S)} {A b T : Expr S}
    (h : HasType P Γ (.lam A b) T) :
    ∃ B s, HasType P (A :: Γ) b B ∧ HasType P Γ (.pi A B) (.sort s) ∧
      Converts T (.pi A B) := h.generation

theorem generation_app {Γ : List (Expr S)} {f a T : Expr S}
    (h : HasType P Γ (.app f a) T) :
    ∃ A B, HasType P Γ f (.pi A B) ∧ HasType P Γ a A ∧
      Converts T (B.instantiate a) := h.generation

/-- Correctness of types, including the unsorted literal-sort alternative. -/
theorem regularity {Γ : List (Expr S)} {M A : Expr S} (h : HasType P Γ M A) :
    (∃ s, A = .sort s) ∨ (∃ s, HasType P Γ A (.sort s)) := by
  induction h with
  | ax h => exact .inl ⟨_, rfl⟩
  | var h ih => exact .inr ⟨_, .weaken h h⟩
  | weaken hM hD ihM ihD =>
      obtain ⟨s, rfl⟩ | ⟨s, hA⟩ := ihM
      · exact .inl ⟨s, rfl⟩
      · exact .inr ⟨s, .weaken hA hD⟩
  | product hA hB hr ihA ihB => exact .inl ⟨_, rfl⟩
  | abstraction hb hPi ihb ihPi => exact .inr ⟨_, hPi⟩
  | application hf ha ihf iha =>
      obtain ⟨s, heq⟩ | ⟨s, hPi⟩ := ihf
      · cases heq
      · obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := hPi.generation_pi
        exact .inr ⟨s₂, hB.instantiate ha⟩
  | conversion hM hA hc ihM ihA => exact .inr ⟨_, hA⟩

theorem product_type_sorted {Γ : List (Expr S)} {M A B : Expr S}
    (h : HasType P Γ M (.pi A B)) : ∃ s, HasType P Γ (.pi A B) (.sort s) := by
  obtain ⟨s, heq⟩ | hs := h.regularity
  · cases heq
  · exact hs

end HasType

namespace Converts

variable {S : Type u}

theorem pi {A A' B B' : Expr S} (hA : Converts A A') (hB : Converts B B') :
    Converts (.pi A B) (.pi A' B') := by
  obtain ⟨D, hD, hD'⟩ := hA.join
  obtain ⟨E, hE, hE'⟩ := hB.join
  exact .trans _ _ _ (hD.pi hE).converts (.symm _ _ (hD'.pi hE').converts)

theorem pi_not_sort {A B : Expr S} {s : S} : ¬ Converts (.pi A B) (.sort s) := by
  intro h
  obtain ⟨N, hN, hs⟩ := h.join
  have heq := (Normal.sort s).reduces_eq hs
  obtain ⟨D, E, hDE, _, _⟩ := hN.pi_inv
  cases heq.trans hDE

theorem sort_inj {s t : S} (h : Converts (Expr.sort s) (.sort t)) : s = t :=
  Expr.sort.inj ((Normal.sort s).eq_of_converts (Normal.sort t) h)

theorem instantiate_right {a a' : Expr S} (h : Converts a a') (B : Expr S) :
    Converts (B.instantiate a) (B.instantiate a') := by
  induction h with
  | rel a a' h =>
      exact (Parallel.instantiate (Parallel.refl B) (Parallel.of_beta h)).reduces.converts
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c hab hbc ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end Converts

namespace HasType

variable {S : Type u} {P : Specification S}

theorem application_type_sorted_aux {Γ : List (Expr S)} {M T : Expr S}
    (h : HasType P Γ M T) :
    ∀ f a, M = .app f a → ∃ s, HasType P Γ T (.sort s) := by
  induction h with
  | ax h => intro f a heq; cases heq
  | var h ih => intro f a heq; cases heq
  | @weaken Γ M T D s hM hD ihM ihD =>
      intro f a heq
      cases M with
      | var n => cases heq
      | sort t => cases heq
      | lam A b => cases heq
      | pi A B => cases heq
      | app g b =>
          obtain ⟨r, hr⟩ := ihM g b rfl
          exact ⟨r, .weaken hr hD⟩
  | product hA hB hr ihA ihB => intro f a heq; cases heq
  | abstraction hb hPi ihb ihPi => intro f a heq; cases heq
  | application hf ha ihf iha =>
      intro f a heq
      obtain ⟨s, hPi⟩ := hf.product_type_sorted
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := hPi.generation_pi
      exact ⟨s₂, hB.instantiate ha⟩
  | conversion hM hT hc ihM ihT => intro f a heq; exact ⟨_, hT⟩

theorem application_type_sorted {Γ : List (Expr S)} {f a T : Expr S}
    (h : HasType P Γ (.app f a) T) : ∃ s, HasType P Γ T (.sort s) :=
  h.application_type_sorted_aux f a rfl

theorem abstraction_type_sorted {Γ : List (Expr S)} {A b T : Expr S}
    (h : HasType P Γ (.lam A b) T) : ∃ s, HasType P Γ T (.sort s) := by
  obtain ⟨s, hT⟩ | hs := h.regularity
  · obtain ⟨B, t, hb, hPi, hc⟩ := h.generation_lam
    subst T
    exact False.elim (Converts.pi_not_sort (.symm _ _ hc))
  · exact hs

/-- Reconstructing a sorted expression at its original expected type does not
require a sorting of a terminal (unsorted) sort. -/
theorem conversion_from_sort {Γ : List (Expr S)} {M T : Expr S} {s : S}
    (h : HasType P Γ M (.sort s))
    (hT : (∃ t, T = .sort t) ∨ ∃ t, HasType P Γ T (.sort t))
    (hc : Converts T (.sort s)) : HasType P Γ M T := by
  obtain ⟨t, rfl⟩ | ⟨t, ht⟩ := hT
  · have heq := hc.sort_inj
    subst t
    exact h
  · exact .conversion h ht (.symm _ _ hc)

/-- Subject reduction at the exact original type, including binder annotations. -/
theorem subject_reduction {Γ : List (Expr S)} {M N T : Expr S}
    (h : HasType P Γ M T) (hr : Beta M N) : HasType P Γ N T := by
  induction hr generalizing Γ T with
  | head A b a =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨D, E, hf, ha, hc⟩ := h.generation_app
      obtain ⟨B, s, hb, hPi, hp⟩ := hf.generation_lam
      obtain ⟨hDA, hEB⟩ := hp.product_compatibility
      obtain ⟨t, hA⟩ := hPi.product_domain A B rfl
      have haA := HasType.conversion ha hA hDA
      have hresult := hb.instantiate haA
      exact .conversion hresult hT (.trans _ _ _
        (.symm _ _ (hEB.subst (Expr.single a))) (.symm _ _ hc))
  | app_left hr ih =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨A, B, hf, ha, hc⟩ := h.generation_app
      exact .conversion (.application (ih hf) ha) hT (.symm _ _ hc)
  | @app_right f a a' hr ih =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨A, B, hf, ha, hc⟩ := h.generation_app
      exact .conversion (.application hf (ih ha)) hT (.trans _ _ _
        (.symm _ _ ((show Converts a a' from .rel _ _ hr).instantiate_right B)) (.symm _ _ hc))
  | @lam_domain A A' b hr ih =>
      obtain ⟨r, hT⟩ := h.abstraction_type_sorted
      obtain ⟨B, s, hb, hPi, hc⟩ := h.generation_lam
      obtain ⟨s₁, s₂, s₃, hA, hB, hrule, hs⟩ := hPi.generation_pi
      have hA' := ih hA
      have heq : Converts A A' := .rel _ _ hr
      have hb' := hb.context_head_conversion hA hA' heq
      have hB' := hB.context_head_conversion hA hA' heq
      have hp' := HasType.product hA' hB' hrule
      exact .conversion (.abstraction hb' hp') hT (.trans _ _ _
        (.symm _ _ (heq.pi (.refl B))) (.symm _ _ hc))
  | lam_body hr ih =>
      obtain ⟨r, hT⟩ := h.abstraction_type_sorted
      obtain ⟨B, s, hb, hPi, hc⟩ := h.generation_lam
      exact .conversion (.abstraction (ih hb) hPi) hT (.symm _ _ hc)
  | pi_domain hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hrule, hc⟩ := h.generation_pi
      have hA' := ih hA
      have hB' := hB.context_head_conversion hA hA' (.rel _ _ hr)
      exact (HasType.product hA' hB' hrule).conversion_from_sort h.regularity hc
  | pi_body hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hrule, hc⟩ := h.generation_pi
      exact (HasType.product hA (ih hB) hrule).conversion_from_sort h.regularity hc

theorem subject_reduces {Γ : List (Expr S)} {M N T : Expr S}
    (h : HasType P Γ M T) (hr : Reduces M N) : HasType P Γ N T := by
  induction hr with
  | refl => exact h
  | tail _ hr ih => exact ih.subject_reduction hr

end HasType

namespace Normal

variable {S : Type u} {M : Expr S}

end Normal

namespace Expr

variable {S : Type u}

/-- Choice of the unique full beta normal form when it exists. The fallback
is irrelevant on legal syntax under the standing system-wide WN hypothesis. -/
noncomputable def normalForm (M : Expr S) : Expr S := by
  classical
  exact if h : WeaklyNormalizing M then Classical.choose h else M

theorem normalForm_spec {M : Expr S} (h : WeaklyNormalizing M) :
    Reduces M M.normalForm ∧ Normal M.normalForm := by
  rw [normalForm, dif_pos h]
  exact Classical.choose_spec h

theorem normalForm_eq {M N : Expr S} (hr : Reduces M N) (hn : Normal N) :
    M.normalForm = N := by
  have h : WeaklyNormalizing M := ⟨N, hr, hn⟩
  obtain ⟨hm, hnm⟩ := normalForm_spec h
  exact hnm.eq_of_converts hn (.trans _ _ _ (.symm _ _ hm.converts) hr.converts)

@[simp] theorem normalForm_of_normal {M : Expr S} (h : Normal M) : M.normalForm = M :=
  normalForm_eq .refl h

theorem normalForm_converts {M N : Expr S} (hM : WeaklyNormalizing M)
    (hN : WeaklyNormalizing N) (hc : Converts M N) : M.normalForm = N.normalForm := by
  obtain ⟨hm, hnm⟩ := normalForm_spec hM
  obtain ⟨hn, hnn⟩ := normalForm_spec hN
  exact hnm.eq_of_converts hnn (.trans _ _ _ (.symm _ _ hm.converts)
    (.trans _ _ _ hc hn.converts))

theorem normalForm_pi {A B : Expr S}
    (hA : WeaklyNormalizing A) (hB : WeaklyNormalizing B) :
    (Expr.pi A B).normalForm = .pi A.normalForm B.normalForm :=
  normalForm_eq ((normalForm_spec hA).1.pi (normalForm_spec hB).1)
    ((normalForm_spec hA).2.pi (normalForm_spec hB).2)

end Expr

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M A : Expr S}

theorem weaklyNormalizing (h : HasType P Γ M A) (hw : SystemWeaklyNormalizing P) :
    WeaklyNormalizing M := hw Γ h.valid M ⟨A, .inl h⟩

theorem type_weaklyNormalizing (h : HasType P Γ M A) (hw : SystemWeaklyNormalizing P) :
    WeaklyNormalizing A := hw Γ h.valid A ⟨M, .inr h⟩

theorem normalForm (h : HasType P Γ M A) (hw : SystemWeaklyNormalizing P) :
    HasType P Γ M.normalForm A :=
  h.subject_reduces (Expr.normalForm_spec (h.weaklyNormalizing hw)).1

theorem normalize_type (h : HasType P Γ M A) (hw : SystemWeaklyNormalizing P) :
    HasType P Γ M A.normalForm := by
  obtain ⟨s, rfl⟩ | ⟨s, hA⟩ := h.regularity
  · simpa only [Expr.normalForm_of_normal (Normal.sort s)] using h
  · exact .conversion h (hA.normalForm hw)
      (Expr.normalForm_spec (h.type_weaklyNormalizing hw)).1.converts

end HasType

/-- The variable-headed spines used by the manuscript. -/
inductive Neutral {S : Type u} : Expr S → Prop
  | var (n) : Neutral (.var n)
  | app {f a} : Neutral f → Neutral (.app f a)

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}

theorem sort_cannot_have_product_type {s : S} {A B : Expr S}
    (h : HasType P Γ (.sort s) (.pi A B)) : False := by
  obtain ⟨t, ht, hc⟩ := h.generation
  exact Converts.pi_not_sort hc

theorem product_cannot_have_product_type {A B D E : Expr S}
    (h : HasType P Γ (.pi A B) (.pi D E)) : False := by
  obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := h.generation_pi
  exact Converts.pi_not_sort hc

theorem lambda_cannot_have_sort_type {A b : Expr S} {s : S}
    (h : HasType P Γ (.lam A b) (.sort s)) : False := by
  obtain ⟨B, t, hb, hPi, hc⟩ := h.generation_lam
  exact Converts.pi_not_sort (.symm _ _ hc)

/-- No functionality is needed for neutral uniqueness: the declaration fixes
its head type, and product compatibility fixes every successive codomain. -/
theorem neutral_unique {M A B : Expr S} (hn : Neutral M)
    (hA : HasType P Γ M A) (hB : HasType P Γ M B) : Converts A B := by
  induction hn generalizing A B with
  | var n =>
      obtain ⟨D, hD, hcD⟩ := hA.generation
      obtain ⟨E, hE, hcE⟩ := hB.generation
      have heq : D = E := by
        clear hA hB hcD hcE
        induction hD generalizing E with
        | zero A Γ => cases hE; rfl
        | succ C hD ih =>
            cases hE with
            | succ _ hE => exact congrArg (Expr.rename Nat.succ) (ih _ hE)
      subst E
      exact .trans _ _ _ hcD (.symm _ _ hcE)
  | @app f a hn ih =>
      obtain ⟨D, E, hf, ha, hc⟩ := hA.generation_app
      obtain ⟨D', E', hf', ha', hc'⟩ := hB.generation_app
      have he := (ih hf hf').product_compatibility.2
      exact .trans _ _ _ hc (.trans _ _ _ (he.subst (Expr.single a)) (.symm _ _ hc'))

theorem normal_shape {M T : Expr S} (h : HasType P Γ M T) (hn : Normal M) :
    (∃ s, M = .sort s) ∨ Neutral M ∨ (∃ A B, M = .pi A B) ∨
      (∃ A b, M = .lam A b) := by
  induction M generalizing T with
  | var n => exact .inr (.inl (.var n))
  | sort s => exact .inl ⟨s, rfl⟩
  | lam A b ihA ihb => exact .inr (.inr (.inr ⟨A, b, rfl⟩))
  | pi A B ihA ihB => exact .inr (.inr (.inl ⟨A, B, rfl⟩))
  | app f a ihf iha =>
      obtain ⟨D, E, hf, ha, hc⟩ := h.generation_app
      obtain ⟨s, rfl⟩ | hnf | ⟨A, B, rfl⟩ | ⟨A, b, rfl⟩ := ihf hf hn.app_left
      · exact False.elim hf.sort_cannot_have_product_type
      · exact .inr (.inl (.app hnf))
      · exact False.elim hf.product_cannot_have_product_type
      · exact False.elim (hn _ (.head A b a))

theorem sorted_normal_shape {M : Expr S} {s : S}
    (h : HasType P Γ M (.sort s)) (hn : Normal M) :
    (∃ t, M = .sort t) ∨ Neutral M ∨ (∃ A B, M = .pi A B) := by
  obtain h | h | h | ⟨A, b, rfl⟩ := h.normal_shape hn
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr h)
  · exact False.elim h.lambda_cannot_have_sort_type

end HasType

/-! Finite syntax-directed typing trees, with all generation witnesses
retained; no functionality or unique sort choices are imposed. -/

inductive TypingTree {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Type u
  | var {Γ n A T} (typing : HasType P Γ (.var n) T)
      (declaration : Lookup Γ n A) (convert : Converts T A) : TypingTree P Γ (.var n) T
  | sort {Γ s t T} (typing : HasType P Γ (.sort s) T)
      (sortAxioms : P.sortAxioms s t) (convert : Converts T (.sort t)) : TypingTree P Γ (.sort s) T
  | product {Γ A B a b c T} (typing : HasType P Γ (.pi A B) T)
      (domain : TypingTree P Γ A (.sort a)) (body : TypingTree P (A :: Γ) B (.sort b))
      (rule : P.rule a b c) (convert : Converts T (.sort c)) : TypingTree P Γ (.pi A B) T
  | abstraction {Γ A b B a s T} (typing : HasType P Γ (.lam A b) T)
      (annotation : TypingTree P Γ A (.sort a)) (body : TypingTree P (A :: Γ) b B)
      (product : HasType P Γ (.pi A B) (.sort s)) (convert : Converts T (.pi A B)) :
      TypingTree P Γ (.lam A b) T
  | application {Γ f a A B T} (typing : HasType P Γ (.app f a) T)
      (function : TypingTree P Γ f (.pi A B)) (argument : TypingTree P Γ a A)
      (convert : Converts T (B.instantiate a)) : TypingTree P Γ (.app f a) T

namespace TypingTree
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

/-- Root expected judgment, including the potentially unsorted final sort. -/
theorem typing (t : TypingTree P Γ M T) : HasType P Γ M T := by
  cases t with
  | var h _ _ => exact h
  | sort h _ _ => exact h
  | product h _ _ _ _ => exact h
  | abstraction h _ _ _ _ => exact h
  | application h _ _ _ => exact h

/-- Retarget only the root; all core data and all children are unchanged. -/
def retarget {T' : Expr S} (t : TypingTree P Γ M T)
    (ht : HasType P Γ M T') (hc : Converts T' T) : TypingTree P Γ M T' := by
  cases t with
  | var _ hd he => exact .var ht hd (.trans _ _ _ hc he)
  | sort _ ha he => exact .sort ht ha (.trans _ _ _ hc he)
  | product _ d b hr he => exact .product ht d b hr (.trans _ _ _ hc he)
  | abstraction _ d b hp he => exact .abstraction ht d b hp (.trans _ _ _ hc he)
  | application _ f a he => exact .application ht f a (.trans _ _ _ hc he)

/-- Generation proves existence of finite stored trees without eliminating a
Prop-valued typing derivation into data or assuming unique formation triples. -/
theorem nonempty (h : HasType P Γ M T) : Nonempty (TypingTree P Γ M T) := by
  induction M generalizing Γ T with
  | var n =>
      obtain ⟨A, hd, hc⟩ := h.generation
      exact ⟨.var h hd hc⟩
  | sort s =>
      obtain ⟨t, ha, hc⟩ := h.generation
      exact ⟨.sort h ha hc⟩
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, hr, hc⟩ := h.generation_pi
      exact ⟨.product h (ihA hA).some (ihB hB).some hr hc⟩
  | lam A b ihA ihb =>
      obtain ⟨B, s, hb, hp, hc⟩ := h.generation_lam
      obtain ⟨a, a', c, hA, _, _, _⟩ := hp.generation_pi
      exact ⟨.abstraction h (ihA hA).some (ihb hb).some hp hc⟩
  | app f a ihf iha =>
      obtain ⟨A, B, hf, ha, hc⟩ := h.generation_app
      exact ⟨.application h (ihf hf).some (iha ha).some hc⟩

noncomputable def ofTyping (h : HasType P Γ M T) : TypingTree P Γ M T := (nonempty h).some

/-- A genuine variable renaming sends declarations to declarations, rather
than merely to terms that happen to have convertible types. -/
def DeclRenaming (Γ Δ : List (Expr S)) (ρ : Nat → Nat) : Prop :=
  ∀ n A, Lookup Γ n A → Lookup Δ (ρ n) (A.rename ρ)

namespace DeclRenaming
variable {Δ : List (Expr S)} {ρ : Nat → Nat}
theorem typed (h : DeclRenaming Γ Δ ρ) (hΔ : ValidContext P Δ) :
    ∀ n A, Lookup Γ n A → HasType P Δ (.var (ρ n)) (A.rename ρ) :=
  fun n A hn => HasType.lookup hΔ (h n A hn)

theorem lift (h : DeclRenaming Γ Δ ρ) (A : Expr S) :
    DeclRenaming (A :: Γ) (A.rename ρ :: Δ) (Expr.liftRen ρ) := by
  intro n B hn
  cases hn with
  | zero =>
      simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def] using Lookup.zero (A.rename ρ) Δ
  | succ _ hn =>
      have hh := Lookup.succ (A.rename ρ) (h _ _ hn)
      simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def] using hh
end DeclRenaming

/-- Thinning/reindexing transports every stored witness and preserves the
whole tree shape. Binder annotations are transported too. -/
noncomputable def rename (t : TypingTree P Γ M T) {Δ : List (Expr S)} (hΔ : ValidContext P Δ)
    (ρ : Nat → Nat) (hρ : DeclRenaming Γ Δ ρ) :
    TypingTree P Δ (M.rename ρ) (T.rename ρ) := by
  induction t generalizing Δ ρ with
  | var h hd hc => exact .var (h.rename hΔ ρ (hρ.typed hΔ)) (hρ _ _ hd) (hc.rename ρ)
  | sort h ha hc => exact .sort (h.rename hΔ ρ (hρ.typed hΔ)) ha (hc.rename ρ)
  | @product Γ A B a b c T h d e hr hc ihd ihe =>
      have hA : HasType P Δ (A.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      exact .product (h.rename hΔ ρ (hρ.typed hΔ)) (ihd hΔ ρ hρ)
        (ihe (.cons hΔ hA) _ (hρ.lift A)) hr (hc.rename ρ)
  | @abstraction Γ A b B a s T h d e hp hc ihd ihe =>
      have hA : HasType P Δ (A.rename ρ) (.sort a) := d.typing.rename hΔ ρ (hρ.typed hΔ)
      exact .abstraction (h.rename hΔ ρ (hρ.typed hΔ)) (ihd hΔ ρ hρ)
        (ihe (.cons hΔ hA) _ (hρ.lift A)) (hp.rename hΔ ρ (hρ.typed hΔ)) (hc.rename ρ)
  | application h f a hc ihf iha =>
      apply TypingTree.application (h.rename hΔ ρ (hρ.typed hΔ)) (ihf hΔ ρ hρ) (iha hΔ ρ hρ)
      simpa only [Expr.instantiate_rename] using hc.rename ρ

namespace DeclRenaming
variable {Δ : List (Expr S)}
theorem weaken (A : Expr S) : DeclRenaming Γ (A :: Γ) Nat.succ :=
  fun _ _ h => .succ A h
end DeclRenaming

/-- Substitution carries stored trees at all declaration occurrences. -/
abbrev StoredSubstitution (P : Specification S) (Γ Δ : List (Expr S))
    (σ : Nat → Expr S) : Type u :=
  ∀ n A, Lookup Γ n A → TypingTree P Δ (σ n) (A.subst σ)

namespace StoredSubstitution
variable {Δ : List (Expr S)} {σ : Nat → Expr S}
theorem typed (ts : StoredSubstitution P Γ Δ σ) : TypedSubstitution P Γ Δ σ :=
  fun n A hn => (ts n A hn).typing

noncomputable def lift (ts : StoredSubstitution P Γ Δ σ) {A : Expr S} {s : S}
    (hA : HasType P Δ (A.subst σ) (.sort s)) :
    StoredSubstitution P (A :: Γ) (A.subst σ :: Δ) (Expr.liftSub σ) :=
  fun n => match n with
  | 0 => fun B hn => by
      have he : B = A.rename Nat.succ := by cases hn; rfl
      have he' : B.subst (Expr.liftSub σ) = (A.subst σ).rename Nat.succ := by
        rw [he,Expr.subst_rename,Expr.rename_subst]
        rfl
      exact .var (he'.symm ▸ HasType.var hA) (.zero _ _) (by rw [he']; exact .refl _)
  | n+1 => fun B hn => by
      let hex : ∃ B', Lookup Γ n B' ∧ B = B'.rename Nat.succ := by
        cases hn with
        | succ _ h => exact ⟨_, h, rfl⟩
      let tt := (ts _ _ hex.choose_spec.1).rename (.cons hA.valid hA) Nat.succ (DeclRenaming.weaken _)
      have he : B.subst (Expr.liftSub σ) = (hex.choose.subst σ).rename Nat.succ := by
        calc
          B.subst (Expr.liftSub σ) = (hex.choose.rename Nat.succ).subst (Expr.liftSub σ) :=
            congrArg (Expr.subst (Expr.liftSub σ)) hex.choose_spec.2
          _ = (hex.choose.subst σ).rename Nat.succ := by
            rw [Expr.subst_rename,Expr.rename_subst]
            rfl
      exact tt.retarget (he.symm ▸ tt.typing) (by rw [he]; exact .refl _)

end StoredSubstitution

/-- Capture-avoiding substitution grafts the given trees at variables. It
retains core choices and recurses through the annotation at each binder. -/
noncomputable def subst (t : TypingTree P Γ M T) {Δ : List (Expr S)}
    (hΔ : ValidContext P Δ) (σ : Nat → Expr S) (ts : StoredSubstitution P Γ Δ σ) :
    TypingTree P Δ (M.subst σ) (T.subst σ) := by
  induction t generalizing Δ σ with
  | var h hd hc => exact (ts _ _ hd).retarget (h.subst hΔ σ ts.typed) (hc.subst σ)
  | sort h ha hc => exact .sort (h.subst hΔ σ ts.typed) ha (hc.subst σ)
  | @product Γ A B a b c T h d e hr hc ihd ihe =>
      have hA : HasType P Δ (A.subst σ) (.sort a) := d.typing.subst hΔ σ ts.typed
      exact .product (h.subst hΔ σ ts.typed) (ihd hΔ σ ts)
        (ihe (.cons hΔ hA) _ (ts.lift hA)) hr (hc.subst σ)
  | @abstraction Γ A b B a s T h d e hp hc ihd ihe =>
      have hA : HasType P Δ (A.subst σ) (.sort a) := d.typing.subst hΔ σ ts.typed
      exact .abstraction (h.subst hΔ σ ts.typed) (ihd hΔ σ ts)
        (ihe (.cons hΔ hA) _ (ts.lift hA)) (hp.subst hΔ σ ts.typed) (hc.subst σ)
  | application h f a hc ihf iha =>
      apply TypingTree.application (h.subst hΔ σ ts.typed) (ihf hΔ σ ts) (iha hΔ σ ts)
      simpa only [Expr.instantiate_subst] using hc.subst σ

end TypingTree

namespace Expr
variable {S : Type u}
def ProperPart (N M : Expr S) : Prop := ∃ K, Child K M ∧ Subterm N K
namespace ProperPart
variable {N M L : Expr S}
theorem child (h : Child N M) : ProperPart N M := ⟨N,h,.refl N⟩
theorem subterm (h : ProperPart N M) : Subterm N M := by
  obtain ⟨K,hK,hN⟩ := h
  exact .tail hN hK
theorem trans_right (h : ProperPart N M) (hML : Subterm M L) : ProperPart N L := by
  induction hML with
  | refl => exact h
  | tail hML hL ih => exact ⟨_,hL,h.subterm.trans hML⟩
theorem trans_left (hNM : Subterm N M) (h : ProperPart M L) : ProperPart N L := by
  obtain ⟨K,hK,hM⟩ := h
  exact ⟨K,hK,hNM.trans hM⟩
end ProperPart
namespace Subterm
variable {M : Expr S}
theorem apps_head (ns : List (Expr S)) : Subterm M (M.apps ns) := by
  induction ns generalizing M with
  | nil => exact .refl M
  | cons n ns ih => exact (of_child (.app_left M n)).trans (ih (M := .app M n))
end Subterm
namespace ProperPart
variable {M n : Expr S} {ns : List (Expr S)}
theorem apps_arg (hn : n ∈ ns) : ProperPart n (M.apps ns) := by
  induction ns generalizing M with
  | nil => cases hn
  | cons a ns ih =>
    rcases List.mem_cons.mp hn with rfl | hn
    · exact (child (.app_right M n)).trans_right (Subterm.apps_head ns)
    · exact ih hn
end ProperPart
@[simp] theorem subst_apps (M : Expr S) (ns : List (Expr S)) (σ : Nat → Expr S) :
    (M.apps ns).subst σ = (M.subst σ).apps (ns.map (Expr.subst σ)) := by
  induction ns generalizing M with
  | nil => rfl
  | cons n ns ih => exact ih (.app M n)
end Expr

namespace HasType
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}
theorem spine_shape {M T : Expr S} (h : HasType P Γ M T) :
    (∃ s, M = .sort s) ∨ Neutral M ∨ (∃ A B, M = .pi A B) ∨
      (∃ A b ns, M = (Expr.lam A b).apps ns) := by
  induction M generalizing T with
  | var n => exact .inr (.inl (.var n))
  | sort s => exact .inl ⟨s,rfl⟩
  | lam A b => exact .inr (.inr (.inr ⟨A,b,[],rfl⟩))
  | pi A B => exact .inr (.inr (.inl ⟨A,B,rfl⟩))
  | app f a ihf iha =>
    obtain ⟨D,E,hf,_,_⟩ := h.generation_app
    rcases ihf hf with ⟨s,rfl⟩ | hn | ⟨A,B,rfl⟩ | ⟨A,b,ns,rfl⟩
    · exact False.elim hf.sort_cannot_have_product_type
    · exact .inr (.inl (.app hn))
    · exact False.elim hf.product_cannot_have_product_type
    · exact .inr (.inr (.inr ⟨A,b,ns ++ [a],by simp only [Expr.apps_append,Expr.apps]⟩))

theorem app_spine {f a T : Expr S} (h : HasType P Γ (.app f a) T) :
    Neutral f ∨ ∃ D b n ns, Expr.app f a = (Expr.app (.lam D b) n).apps ns := by
  obtain ⟨D,E,hf,_,_⟩ := h.generation_app
  rcases hf.spine_shape with ⟨s,rfl⟩ | hn | ⟨A,B,rfl⟩ | ⟨A,b,ns,rfl⟩
  · exact False.elim hf.sort_cannot_have_product_type
  · exact .inl hn
  · exact False.elim hf.product_cannot_have_product_type
  · right
    cases ns with
    | nil => exact ⟨A,b,a,[],rfl⟩
    | cons n ns => exact ⟨A,b,n,ns ++ [a],by simp only [Expr.apps_append,Expr.apps]⟩

theorem apps_head {M T : Expr S} {ns : List (Expr S)} (h : HasType P Γ (M.apps ns) T) :
    ∃ A, HasType P Γ M A := by
  induction ns generalizing M T with
  | nil => exact ⟨T,h⟩
  | cons n ns ih =>
    obtain ⟨A,hA⟩ := ih h
    obtain ⟨D,E,hf,_,_⟩ := hA.generation_app
    exact ⟨_,hf⟩

theorem apps_arg {M T n : Expr S} {ns : List (Expr S)}
    (h : HasType P Γ (M.apps ns) T) (hn : n ∈ ns) : ∃ A, HasType P Γ n A := by
  induction ns generalizing M T with
  | nil => cases hn
  | cons a ns ih =>
    rcases List.mem_cons.mp hn with rfl | hn
    · obtain ⟨T,hT⟩ := h.apps_head (M := .app M n) (ns := ns)
      obtain ⟨D,E,_,ha,_⟩ := hT.generation_app
      exact ⟨D,ha⟩
    · exact ih h hn
end HasType

/-- The syntactic application principle implying strong normalization.
This principle is proved from candidate interfaces, not assumed
on the PTS normalization theorem. -/
theorem stronglyNormalizing_of_application
    {S : Type u} {P : Specification S}
    (applySN : ∀ {Γ f a D E}, HasType P Γ f (.pi D E) → HasType P Γ a D →
      StronglyNormalizing f → StronglyNormalizing a → StronglyNormalizing (.app f a)) :
    SystemStronglyNormalizing P := by
  have typed : ∀ M : Expr S, ∀ {Γ A}, HasType P Γ M A → StronglyNormalizing M := by
    intro M
    induction M with
    | var n => intro Γ A h; exact (Normal.var n).stronglyNormalizing
    | sort s => intro Γ A h; exact (Normal.sort s).stronglyNormalizing
    | app f a ihf iha =>
        intro Γ A h
        obtain ⟨D, E, hf, ha, _⟩ := h.generation_app
        exact applySN hf ha (ihf hf) (iha ha)
    | lam D b ihD ihb =>
        intro Γ A h
        obtain ⟨E, s, hb, hpi, _⟩ := h.generation_lam
        obtain ⟨s₁, s₂, s₃, hD, _, _, _⟩ := hpi.generation_pi
        exact (ihD hD).lam (ihb hb)
    | pi D E ihD ihE =>
        intro Γ A h
        obtain ⟨s₁, s₂, s₃, hD, hE, _, _⟩ := h.generation_pi
        exact (ihD hD).pi (ihE hE)
  intro Γ _ M h
  obtain ⟨A, h | h⟩ := h
  · exact typed M h
  · obtain ⟨s, rfl⟩ | ⟨s, hs⟩ := h.regularity
    · exact (Normal.sort s).stronglyNormalizing
    · exact typed M hs

/-- A failed full-normalization theorem has an exact, well-typed application
counterexample whose two children are already strongly normalizing. -/
theorem exists_bad_application {S : Type u} {P : Specification S}
    (h : ¬ SystemStronglyNormalizing P) :
    ∃ Γ f a D E, HasType P Γ f (.pi D E) ∧ HasType P Γ a D ∧
      StronglyNormalizing f ∧ StronglyNormalizing a ∧ ¬ StronglyNormalizing (.app f a) := by
  classical
  by_contra hn
  apply h
  apply stronglyNormalizing_of_application
  intro Γ f a D E hf ha hfs has
  by_contra hb
  exact hn ⟨Γ, f, a, D, E, hf, ha, hfs, has, hb⟩

namespace Normal

variable {S : Type u}

theorem rename {M : Expr S} (h : Normal M) (ρ : Nat → Nat) :
    Normal (M.rename ρ) := by
  induction M generalizing ρ with
  | var n => exact Normal.var _
  | sort s => exact Normal.sort _
  | pi A B ihA ihB => exact (ihA h.pi_domain ρ).pi (ihB h.pi_body _)
  | lam A b ihA ihb => exact (ihA h.lam_domain ρ).lam (ihb h.lam_body _)
  | app f a ihf iha =>
      have hf := ihf h.app_left ρ
      have ha := iha h.app_right ρ
      cases f with
      | lam D b => exact False.elim (h _ (.head D b a))
      | var n | sort s | app f b | pi D B =>
          intro N hN
          cases hN with
          | app_left hr => exact hf _ hr
          | app_right hr => exact ha _ hr

end Normal

end S_wpc_barendregt_geuvers_klop

end OMA



namespace OMA

namespace S_wpc_barendregt_geuvers_klop

universe u

deriving instance Countable for Expr

namespace Expr

variable {S : Type u}

/-- Every free index is below the context length. -/
def Scoped : Nat → Expr S → Prop
  | n, .var i => i < n
  | _, .sort _ => True
  | n, .app M N => Scoped n M ∧ Scoped n N
  | n, .lam A b => Scoped n A ∧ Scoped (n+1) b
  | n, .pi A B => Scoped n A ∧ Scoped (n+1) B

namespace Scoped

variable {n m : Nat} {M : Expr S}

theorem rename (h : Scoped n M) (ρ : Nat → Nat)
    (hρ : ∀ i, i < n → ρ i < m) : Scoped m (M.rename ρ) := by
  induction M generalizing n m ρ with
  | var i => exact hρ i h
  | sort _ => trivial
  | app M N ihM ihN => exact ⟨ihM h.1 _ hρ, ihN h.2 _ hρ⟩
  | lam A b ihA ihb | pi A b ihA ihb =>
      refine ⟨ihA h.1 _ hρ, ihb h.2 _ ?_⟩
      intro i hi
      cases i with
      | zero => exact Nat.zero_lt_succ _
      | succ i => exact Nat.succ_lt_succ (hρ i (Nat.lt_of_succ_lt_succ hi))

theorem mono (h : Scoped n M) (hnm : n ≤ m) : Scoped m M := by
  simpa only [rename_id] using h.rename id (fun _ hi => lt_of_lt_of_le hi hnm)

theorem rename_congr (h : Scoped n M) {ρ τ : Nat → Nat}
    (he : ∀ i, i < n → ρ i = τ i) : M.rename ρ = M.rename τ := by
  induction M generalizing n ρ τ with
  | var i => exact congrArg Expr.var (he i h)
  | sort _ => rfl
  | app M N ihM ihN => exact congrArg₂ Expr.app (ihM h.1 he) (ihN h.2 he)
  | lam A b ihA ihb | pi A b ihA ihb =>
      have hl : ∀ i, i < n+1 → liftRen ρ i = liftRen τ i := by
        intro i hi
        cases i with
        | zero => rfl
        | succ i => exact congrArg Nat.succ (he i (Nat.lt_of_succ_lt_succ hi))
      simp only [Expr.rename, ihA h.1 he, ihb h.2 hl]

theorem subst (h : Scoped n M) (σ : Nat → Expr S)
    (hσ : ∀ i, i < n → Scoped m (σ i)) : Scoped m (M.subst σ) := by
  induction M generalizing n m σ with
  | var i => exact hσ i h
  | sort _ => trivial
  | app M N ihM ihN => exact ⟨ihM h.1 _ hσ, ihN h.2 _ hσ⟩
  | lam A b ihA ihb | pi A b ihA ihb =>
      refine ⟨ihA h.1 _ hσ, ihb h.2 _ ?_⟩
      intro i hi
      cases i with
      | zero => exact Nat.zero_lt_succ _
      | succ i =>
          exact (hσ i (Nat.lt_of_succ_lt_succ hi)).rename Nat.succ
            (fun _ hi => Nat.succ_lt_succ hi)

theorem instantiate {b a : Expr S} (hb : Scoped (n+1) b) (ha : Scoped n a) :
    Scoped n (b.instantiate a) := by
  apply hb.subst
  intro i hi
  cases i with
  | zero => exact ha
  | succ i => exact Nat.lt_of_succ_lt_succ hi

end Scoped

/-- Reversal identifies de Bruijn indices in a finite context with fixed levels.
Outside that context it is the identity. -/
def reverseIndex (n i : Nat) : Nat := if i < n then n - 1 - i else i

theorem reverseIndex_lt {n i : Nat} (hi : i < n) : reverseIndex n i < n := by
  simp only [reverseIndex, if_pos hi]
  omega

theorem reverseIndex_involutive (n : Nat) : Function.Involutive (reverseIndex n) := by
  intro i
  unfold reverseIndex
  split_ifs <;> omega

@[simp] theorem reverseIndex_twice (n : Nat) (M : Expr S) :
    (M.rename (reverseIndex n)).rename (reverseIndex n) = M := by
  rw [rename_comp]
  have he : reverseIndex n ∘ reverseIndex n = id := funext (reverseIndex_involutive n)
  rw [he, rename_id]

theorem Scoped.reverseIndex {n : Nat} {M : Expr S} (h : Scoped n M) :
    Scoped n (M.rename (reverseIndex n)) :=
  h.rename _ (fun _ hi => reverseIndex_lt hi)

theorem Scoped.reverseIndex_succ {n : Nat} {M : Expr S} (h : Scoped n M) :
    M.rename (Expr.reverseIndex (n+1)) = (M.rename (Expr.reverseIndex n)).rename Nat.succ := by
  rw [rename_comp]
  apply h.rename_congr
  intro i hi
  simp only [Function.comp_apply, Expr.reverseIndex, if_pos hi]
  rw [if_pos (Nat.lt_succ_of_lt hi)]
  omega

end Expr

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M A : Expr S}

theorem scope (h : HasType P Γ M A) : M.Scoped Γ.length ∧ A.Scoped Γ.length := by
  induction h with
  | ax _ => exact ⟨True.intro, True.intro⟩
  | var _ ih =>
      exact ⟨Nat.zero_lt_succ _, ih.1.rename Nat.succ (fun _ hi => Nat.succ_lt_succ hi)⟩
  | weaken _ _ ih _ =>
      exact ⟨ih.1.rename Nat.succ (fun _ hi => Nat.succ_lt_succ hi),
        ih.2.rename Nat.succ (fun _ hi => Nat.succ_lt_succ hi)⟩
  | product _ _ _ ihA ihB => exact ⟨⟨ihA.1, ihB.1⟩, True.intro⟩
  | abstraction _ _ ihb ihPi => exact ⟨⟨ihPi.1.1, ihb.1⟩, ihPi.1⟩
  | application _ _ ihf iha => exact ⟨⟨ihf.1, iha.1⟩, ihf.2.2.instantiate iha.1⟩
  | conversion _ _ _ ihM ihB => exact ⟨ihM.1, ihB.1⟩

end HasType

namespace Beta

variable {S : Type u} {M N : Expr S}

theorem scope (h : Beta M N) {n : Nat} (hM : M.Scoped n) : N.Scoped n := by
  induction h generalizing n with
  | head _ _ _ => exact hM.1.2.instantiate hM.2
  | app_left _ ih => exact ⟨ih hM.1, hM.2⟩
  | app_right _ ih => exact ⟨hM.1, ih hM.2⟩
  | lam_domain _ ih | pi_domain _ ih => exact ⟨ih hM.1, hM.2⟩
  | lam_body _ ih | pi_body _ ih => exact ⟨hM.1, ih hM.2⟩

end Beta

namespace Reduces

variable {S : Type u} {M N : Expr S}

theorem scope (h : Reduces M N) {n : Nat} (hM : M.Scoped n) : N.Scoped n := by
  induction h with
  | refl => exact hM
  | tail _ h ih => exact h.scope ih

end Reduces

namespace WeaklyNormalizing

variable {S : Type u} {M : Expr S}

theorem rename (h : WeaklyNormalizing M) (ρ : Nat → Nat) :
    WeaklyNormalizing (M.rename ρ) := by
  obtain ⟨N, hr, hn⟩ := h
  exact ⟨N.rename ρ, Reduces.rename hr ρ, hn.rename ρ⟩

theorem reverseIndex_iff (n : Nat) :
    WeaklyNormalizing (M.rename (Expr.reverseIndex n)) ↔ WeaklyNormalizing M := by
  constructor
  · intro h
    simpa only [Expr.reverseIndex_twice] using h.rename (Expr.reverseIndex n)
  · intro h
    exact h.rename _

end WeaklyNormalizing

/-- Finite prefixes of a common context, using fixed-level names when viewed
outside a prefix. Every sortable fixed-level expression is declared arbitrarily
late. Bound variables remain de Bruijn indices and are never declared here. -/
structure ContextTower {S : Type u} (P : Specification S) where
  context : Nat → List (Expr S)
  valid : ∀ n, ValidContext P (context n)
  length : ∀ n, (context n).length = n
  step : ∀ n, ∃ A s, HasType P (context n) A (.sort s) ∧ context (n+1) = A :: context n
  saturated : ∀ (n : Nat) (A : Expr S) (s : S), HasType P (context n) (A.rename (Expr.reverseIndex n)) (.sort s) →
    ∀ lower, ∃ m, n ≤ m ∧ lower ≤ m ∧
      context (m+1) = A.rename (Expr.reverseIndex m) :: context m

namespace ContextTowerConstruction

variable {S : Type u} (P : Specification S)

structure Stage (n : Nat) where
  context : List (Expr S)
  valid : ValidContext P context
  length : context.length = n

variable [Countable S]

noncomputable def enumeration : Nat → Expr S := by
  letI : Nonempty (Expr S) := ⟨.var 0⟩
  exact (exists_surjective_nat (Expr S)).choose

theorem enumeration_surjective : Function.Surjective (enumeration (S := S)) := by
  let : Nonempty (Expr S) := ⟨.var 0⟩
  exact (exists_surjective_nat (Expr S)).choose_spec

noncomputable def scheduled (n : Nat) : Expr S := enumeration (Nat.unpair n).1

theorem scheduled_late (A : Expr S) (lower : Nat) :
    ∃ m, lower ≤ m ∧ scheduled m = A := by
  obtain ⟨k, hk⟩ := enumeration_surjective A
  exact ⟨Nat.pair k lower, Nat.right_le_pair _ _, by simpa only [scheduled, Nat.unpair_pair]⟩

variable {s₀ t₀ : S} (h₀ : P.sortAxioms s₀ t₀)

noncomputable def next {n : Nat} (Γ : Stage P n) :
    {A : Expr S // ∃ s, HasType P Γ.context A (.sort s)} := by
  classical
  let A : Expr S := (scheduled n).rename (Expr.reverseIndex n)
  exact if ht : ∃ s, HasType P Γ.context A (.sort s) then ⟨A, ht⟩
    else ⟨.sort s₀, t₀, HasType.sort_of_valid Γ.valid h₀⟩

noncomputable def stages : (n : Nat) → Stage P n
  | 0 => ⟨[], .nil, rfl⟩
  | n+1 =>
      let Γ := stages n
      let A := next P h₀ Γ
      ⟨A.val :: Γ.context, .cons Γ.valid A.property.choose_spec,
        by simp only [List.length_cons, Γ.length]⟩

noncomputable def contexts (n : Nat) : List (Expr S) := (stages P h₀ n).context

theorem valid (n : Nat) : ValidContext P (contexts P h₀ n) := (stages P h₀ n).valid

theorem length (n : Nat) : (contexts P h₀ n).length = n := (stages P h₀ n).length

theorem step (n : Nat) : ∃ A s, HasType P (contexts P h₀ n) A (.sort s) ∧
    contexts P h₀ (n+1) = A :: contexts P h₀ n :=
  ⟨(next P h₀ (stages P h₀ n)).val, _, (next P h₀ (stages P h₀ n)).property.choose_spec, rfl⟩

theorem rename_next {n : Nat} {M A : Expr S}
    (h : HasType P (contexts P h₀ n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n))) :
    HasType P (contexts P h₀ (n+1)) (M.rename (Expr.reverseIndex (n+1)))
      (A.rename (Expr.reverseIndex (n+1))) := by
  have hm : M.Scoped n := by
    have hh := h.scope.1.reverseIndex
    rw [length, Expr.reverseIndex_twice] at hh
    exact hh
  have ha : A.Scoped n := by
    have hh := h.scope.2.reverseIndex
    rw [length, Expr.reverseIndex_twice] at hh
    exact hh
  obtain ⟨D, s, ht, he⟩ := step P h₀ n
  rw [he, hm.reverseIndex_succ, ha.reverseIndex_succ]
  exact .weaken h ht

theorem rename_mono {n m : Nat} {M A : Expr S}
    (h : HasType P (contexts P h₀ n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n))) (hnm : n ≤ m) :
    HasType P (contexts P h₀ m) (M.rename (Expr.reverseIndex m))
      (A.rename (Expr.reverseIndex m)) := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact rename_next P h₀ ih

theorem at_scheduled {n : Nat} (s : S)
    (h : HasType P (contexts P h₀ n) ((scheduled n).rename (Expr.reverseIndex n)) (.sort s)) :
    contexts P h₀ (n+1) = (scheduled n).rename (Expr.reverseIndex n) :: contexts P h₀ n := by
  classical
  have ht : ∃ t, HasType P (stages P h₀ n).context
      ((scheduled n).rename (Expr.reverseIndex n)) (.sort t) := ⟨s,h⟩
  simp only [contexts, stages, next, dif_pos ht]

theorem saturated (n : Nat) (A : Expr S) (s : S)
    (h : HasType P (contexts P h₀ n) (A.rename (Expr.reverseIndex n)) (.sort s))
    (lower : Nat) : ∃ m, n ≤ m ∧ lower ≤ m ∧
      contexts P h₀ (m+1) = A.rename (Expr.reverseIndex m) :: contexts P h₀ m := by
  obtain ⟨m, hm, he⟩ := scheduled_late A (max n lower)
  have hnm : n ≤ m := (le_max_left _ _).trans hm
  have hlm : lower ≤ m := (le_max_right _ _).trans hm
  have ht : HasType P (contexts P h₀ m) (A.rename (Expr.reverseIndex m)) (.sort s) :=
    rename_mono P h₀ (A := .sort s) h hnm
  refine ⟨m, hnm, hlm, ?_⟩
  have hs : HasType P (contexts P h₀ m)
      ((scheduled m).rename (Expr.reverseIndex m)) (.sort s) := by
    rw [he]
    exact ht
  calc
    contexts P h₀ (m+1) = (scheduled m).rename (Expr.reverseIndex m) :: contexts P h₀ m :=
      at_scheduled P h₀ s hs
    _ = A.rename (Expr.reverseIndex m) :: contexts P h₀ m :=
      congrArg (fun B : Expr S => B.rename (Expr.reverseIndex m) :: contexts P h₀ m) he

noncomputable def tower : ContextTower P where
  context := contexts P h₀
  valid := valid P h₀
  length := length P h₀
  step := step P h₀
  saturated := saturated P h₀

end ContextTowerConstruction

namespace ContextTower

variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

/-- A global judgment is witnessed in a finite prefix of the tower. -/
def HasType (M A : Expr S) : Prop :=
  ∃ n, S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (M.rename (Expr.reverseIndex n))
    (A.rename (Expr.reverseIndex n))

theorem at_next {n : Nat} {M A : Expr S}
    (h : S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n))) :
    S_wpc_barendregt_geuvers_klop.HasType P (Ω.context (n+1)) (M.rename (Expr.reverseIndex (n+1)))
      (A.rename (Expr.reverseIndex (n+1))) := by
  have hm : M.Scoped n := by
    have hh := h.scope.1.reverseIndex
    rw [Ω.length, Expr.reverseIndex_twice] at hh
    exact hh
  have ha : A.Scoped n := by
    have hh := h.scope.2.reverseIndex
    rw [Ω.length, Expr.reverseIndex_twice] at hh
    exact hh
  obtain ⟨D, s, ht, he⟩ := Ω.step n
  rw [he, hm.reverseIndex_succ, ha.reverseIndex_succ]
  exact .weaken h ht

theorem at_mono {n m : Nat} {M A : Expr S}
    (h : S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n))) (hnm : n ≤ m) :
    S_wpc_barendregt_geuvers_klop.HasType P (Ω.context m) (M.rename (Expr.reverseIndex m))
      (A.rename (Expr.reverseIndex m)) := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact Ω.at_next ih

namespace HasType

variable {Ω : ContextTower P} {M A : Expr S}

theorem scope (h : Ω.HasType M A) : ∃ n, M.Scoped n ∧ A.Scoped n := by
  obtain ⟨n, ht⟩ := h
  refine ⟨n, ?_, ?_⟩
  · have hh := ht.scope.1.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at hh
  · have hh := ht.scope.2.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at hh

theorem weaklyNormalizing (h : Ω.HasType M A) (hw : SystemWeaklyNormalizing P) :
    WeaklyNormalizing M := by
  obtain ⟨n, ht⟩ := h
  exact (WeaklyNormalizing.reverseIndex_iff n).mp (hw _ ht.valid _ ⟨_, Or.inl ht⟩)

theorem type_weaklyNormalizing (h : Ω.HasType M A) (hw : SystemWeaklyNormalizing P) :
    WeaklyNormalizing A := by
  obtain ⟨n, ht⟩ := h
  exact (WeaklyNormalizing.reverseIndex_iff n).mp (hw _ ht.valid _ ⟨_, Or.inr ht⟩)

theorem common {N B : Expr S} (h : Ω.HasType M A) (k : Ω.HasType N B) :
    ∃ n, S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n)) ∧
      S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (N.rename (Expr.reverseIndex n))
      (B.rename (Expr.reverseIndex n)) := by
  obtain ⟨n, ht⟩ := h
  obtain ⟨m, kt⟩ := k
  exact ⟨max n m, Ω.at_mono ht (le_max_left _ _), Ω.at_mono kt (le_max_right _ _)⟩

end HasType

theorem fresh_variable {A : Expr S} {s : S} (h : Ω.HasType A (.sort s)) (lower : Nat) :
    ∃ i, lower ≤ i ∧ Ω.HasType (.var i) A := by
  obtain ⟨n, ht⟩ := h
  have hA : A.Scoped n := by
    have hh := ht.scope.1.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at hh
  obtain ⟨m, hnm, hlm, he⟩ := Ω.saturated n A s ht lower
  have hAm := hA.mono hnm
  have hm : S_wpc_barendregt_geuvers_klop.HasType P (Ω.context m) (A.rename (Expr.reverseIndex m)) (.sort s) :=
    Ω.at_mono (A := .sort s) ht hnm
  refine ⟨m, hlm, m+1, ?_⟩
  rw [he, hAm.reverseIndex_succ]
  have hv := S_wpc_barendregt_geuvers_klop.HasType.var hm
  simpa only [Expr.rename, Expr.reverseIndex, Nat.lt_succ_self, ite_true,
    Nat.add_sub_cancel, Nat.sub_self] using hv

end ContextTower

namespace ContextTower.HasType

variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {M N A B : Expr S}

theorem application (hf : Ω.HasType M (.pi A B)) (ha : Ω.HasType N A) :
    Ω.HasType (.app M N) (B.instantiate N) := by
  obtain ⟨n, hf, ha⟩ := hf.common ha
  refine ⟨n, ?_⟩
  simpa only [Expr.rename, Expr.instantiate_rename] using
    S_wpc_barendregt_geuvers_klop.HasType.application hf ha

theorem conversion {s : S} (hM : Ω.HasType M A) (hB : Ω.HasType B (.sort s))
    (hc : Converts A B) : Ω.HasType M B := by
  obtain ⟨n, hM, hB⟩ := hM.common hB
  exact ⟨n, .conversion hM hB (hc.rename _)⟩

theorem subject_reduces (h : Ω.HasType M A) (hr : Reduces M N) : Ω.HasType N A := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, h.subject_reduces (hr.rename _)⟩

theorem regularity (h : Ω.HasType M A) :
    (∃ s, A = .sort s) ∨ (∃ s, Ω.HasType A (.sort s)) := by
  obtain ⟨n, h⟩ := h
  obtain ⟨s, he⟩ | ⟨s, hs⟩ := h.regularity
  · left
    refine ⟨s, ?_⟩
    have he' := congrArg (Expr.rename (Expr.reverseIndex n)) he
    simpa only [Expr.reverseIndex_twice, Expr.rename] using he'
  · exact .inr ⟨s, n, hs⟩

theorem normalForm (h : Ω.HasType M A) (hw : SystemWeaklyNormalizing P) :
    Ω.HasType M.normalForm A :=
  h.subject_reduces (Expr.normalForm_spec (h.weaklyNormalizing hw)).1

theorem normalize_type (h : Ω.HasType M A) (hw : SystemWeaklyNormalizing P) :
    Ω.HasType M A.normalForm := by
  obtain ⟨s, rfl⟩ | ⟨s, hA⟩ := h.regularity
  · simpa only [Expr.normalForm_of_normal (Normal.sort s)] using h
  · exact .conversion h (hA.normalForm hw)
      (Expr.normalForm_spec (h.type_weaklyNormalizing hw)).1.converts

end ContextTower.HasType

/-! Finite generic contexts may have arbitrary raw actual images in the
saturated tower. Every such substitution is witnessed in one finite prefix;
no normalization or strong-normalization of the images is assumed. -/
namespace ContextTower
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

def TypedSubstitution (Γ : List (Expr S)) (σ : Nat → Expr S) : Prop :=
  ∀ n A, Lookup Γ n A → Ω.HasType (σ n) (A.subst σ)

namespace TypedSubstitution
variable {Ω} {Γ : List (Expr S)} {σ : Nat → Expr S}

theorem tail {A : Expr S} (h : Ω.TypedSubstitution (A :: Γ) σ) :
    Ω.TypedSubstitution Γ (σ ∘ Nat.succ) := by
  intro n B hn
  have hh := h (n+1) (B.rename Nat.succ) (.succ A hn)
  simpa only [Expr.subst_rename, Function.comp_apply] using hh

/-- One common stage suffices for every declaration image, despite the
substitution being presented as a total function on indices. -/
theorem common_stage (h : Ω.TypedSubstitution Γ σ) :
    ∃ k, ∀ n A, Lookup Γ n A →
      S_wpc_barendregt_geuvers_klop.HasType P (Ω.context k) ((σ n).rename (Expr.reverseIndex k))
        ((A.subst σ).rename (Expr.reverseIndex k)) := by
  induction Γ generalizing σ with
  | nil => exact ⟨0, fun _ _ hn => nomatch hn⟩
  | cons B Γ ih =>
      obtain ⟨k, hk⟩ := ih h.tail
      obtain ⟨m, hm⟩ := h 0 (B.rename Nat.succ) (.zero B Γ)
      refine ⟨max k m, ?_⟩
      intro n A hn
      cases hn with
      | zero => exact Ω.at_mono hm (le_max_right k m)
      | succ B hn =>
          have hh := Ω.at_mono (hk _ _ hn) (le_max_left k m)
          simpa only [Expr.subst_rename, Function.comp_apply] using hh

/-- Extension assigns a raw term to the fresh generic binder. -/
theorem cons {A a : Expr S} (h : Ω.TypedSubstitution Γ σ)
    (ha : Ω.HasType a (A.subst σ)) : Ω.TypedSubstitution (A :: Γ) (fun n => match n with
      | 0 => a | n+1 => σ n) := by
  intro n B hn
  cases hn with
  | zero => simpa only [Expr.subst_rename, Function.comp_def] using ha
  | succ A hn => simpa only [Expr.subst_rename, Function.comp_def] using h _ _ hn
end TypedSubstitution

namespace HasType
variable {Ω} {Γ : List (Expr S)} {M A : Expr S} {σ : Nat → Expr S}

/-- Arbitrary typed substitution from a finite generic context to the tower. -/
theorem subst (h : S_wpc_barendregt_geuvers_klop.HasType P Γ M A) (hσ : Ω.TypedSubstitution Γ σ) :
    Ω.HasType (M.subst σ) (A.subst σ) := by
  obtain ⟨k, hk⟩ := TypedSubstitution.common_stage hσ
  refine ⟨k, ?_⟩
  have hh := h.subst (Ω.valid k) (fun n => (σ n).rename (Expr.reverseIndex k)) (fun n B hn => by
    simpa only [← Expr.rename_subst] using hk n B hn)
  simpa only [← Expr.rename_subst] using hh
end HasType

namespace TypedSubstitution
variable {Ω} {Γ : List (Expr S)} {σ τ : Nat → Expr S}

theorem comp {Δ : List (Expr S)} (h : Ω.TypedSubstitution Δ τ)
    (hσ : S_wpc_barendregt_geuvers_klop.TypedSubstitution P Γ Δ σ) :
    Ω.TypedSubstitution Γ (fun n => (σ n).subst τ) := by
  intro n A hn
  simpa only [Expr.subst_subst] using HasType.subst (hσ n A hn) h

/-- The tower's finite-prefix identity environment uses global names. -/
theorem identity (n : Nat) : Ω.TypedSubstitution (Ω.context n) (.var ∘ Expr.reverseIndex n) := by
  intro i A hi
  have ht := S_wpc_barendregt_geuvers_klop.HasType.lookup (Ω.valid n) hi
  refine ⟨n, ?_⟩
  simpa only [Expr.subst_var_rename, Expr.rename, Function.comp_apply,
    Expr.reverseIndex_involutive n i, Expr.reverseIndex_twice] using ht
end TypedSubstitution

end ContextTower
end S_wpc_barendregt_geuvers_klop

end OMA



namespace OMA

namespace S_wpc_barendregt_geuvers_klop

universe u

namespace Candidates

variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

/-- Source actual types: a normal sorted expression, or a literal sort. -/
def ActualType (T : Expr S) : Prop :=
  (Normal T ∧ ∃ s, Ω.HasType T (.sort s)) ∨ ∃ s, T = .sort s

def Top (T : Expr S) : Set (Expr S) :=
  {M | Ω.HasType M T ∧ StronglyNormalizing M}

/-- Tests follow the exact normal successive types, not other typings. -/
inductive TestedStack : Expr S → List (Expr S) → Prop
  | nil (T) : TestedStack T []
  | cons {D E n ns} : n ∈ Top Ω D →
      TestedStack (E.instantiate n).normalForm ns → TestedStack (.pi D E) (n :: ns)

def Ground (T : Expr S) : Set (Expr S) :=
  {M | Ω.HasType M T ∧ ∀ ns, TestedStack Ω T ns → StronglyNormalizing (M.apps ns)}

namespace TestedStack

variable {Ω} {T : Expr S} {ns : List (Expr S)}

theorem sn (h : TestedStack Ω T ns) : StronglyNormalizingArgs ns := by
  induction h with
  | nil => exact .nil
  | cons hn _ ih => exact .cons hn.2 ih

theorem forall_sn (h : TestedStack Ω T ns) : ∀ n ∈ ns, StronglyNormalizing n := by
  induction h with
  | nil => simp
  | cons hn _ ih =>
      intro n hn'
      rcases List.mem_cons.mp hn' with rfl | hm
      · exact hn.2
      · exact ih n hm

end TestedStack

variable {Ω} {T M : Expr S}

theorem ground_le_top : Ground Ω T ⊆ Top Ω T := by
  intro M h
  exact ⟨h.1, h.2 [] (.nil T)⟩

theorem sort_ground_eq_top (s : S) : Ground Ω (.sort s) = Top Ω (.sort s) := by
  apply Set.Subset.antisymm ground_le_top
  intro M h
  refine ⟨h.1, ?_⟩
  intro ns hs
  cases hs
  exact h.2

theorem var_ground (n : Nat) (h : Ω.HasType (.var n) T) : .var n ∈ Ground Ω T :=
  ⟨h, fun _ hs => StronglyNormalizing.var_apps n hs.sn⟩

theorem ground_application (hw : SystemWeaklyNormalizing P) {D E n : Expr S}
    (h : M ∈ Ground Ω (.pi D E)) (hn : n ∈ Top Ω D) :
    .app M n ∈ Ground Ω (E.instantiate n).normalForm := by
  refine ⟨(h.1.application hn.1).normalize_type hw, ?_⟩
  intro ns hs
  exact h.2 (n :: ns) (.cons hn hs)

/-- Head expansion, with exact typing and SN of every annotation/spine component. -/
def ExpansionClosed (Ω : ContextTower P) (T : Expr S) (C : Set (Expr S)) : Prop :=
  ∀ (D b n : Expr S) (ns : List (Expr S)),
    Ω.HasType ((Expr.app (.lam D b) n).apps ns) T →
    StronglyNormalizing D → StronglyNormalizing b → StronglyNormalizing n →
    StronglyNormalizingArgs ns → (b.instantiate n).apps ns ∈ C →
    (Expr.app (.lam D b) n).apps ns ∈ C

structure IsCandidate (Ω : ContextTower P) (T : Expr S) (C : Set (Expr S)) : Prop where
  lower : Ground Ω T ⊆ C
  upper : C ⊆ Top Ω T
  expansion : ExpansionClosed Ω T C

theorem top_candidate : IsCandidate Ω T (Top Ω T) where
  lower := ground_le_top
  upper := Set.Subset.rfl
  expansion := fun _ _ _ _ ht hD hb hn hns hc =>
    ⟨ht, StronglyNormalizing.head_expansion hD hb hn hns hc.2⟩

/-- The bounded intersection makes the empty meet the typed top. -/
def Meet (Ω : ContextTower P) (T : Expr S) (Cs : Set (Set (Expr S))) : Set (Expr S) :=
  {M | M ∈ Top Ω T ∧ ∀ C ∈ Cs, M ∈ C}

theorem meet_candidate {Cs : Set (Set (Expr S))}
    (hCs : ∀ C ∈ Cs, IsCandidate Ω T C) : IsCandidate Ω T (Meet Ω T Cs) where
  lower := fun _ h => ⟨ground_le_top h, fun C hC => (hCs C hC).lower h⟩
  upper := fun _ h => h.1
  expansion := by
    intro D b n ns ht hD hb hn hns hc
    refine ⟨⟨ht, StronglyNormalizing.head_expansion hD hb hn hns hc.1.2⟩, ?_⟩
    intro C hC
    exact (hCs C hC).expansion D b n ns ht hD hb hn hns (hc.2 C hC)

def Bottom (Ω : ContextTower P) (T : Expr S) : Set (Expr S) :=
  Meet Ω T {C | IsCandidate Ω T C}

theorem bottom_candidate : IsCandidate Ω T (Bottom Ω T) :=
  meet_candidate (fun _ h => h)

theorem bottom_le {C : Set (Expr S)} (hC : IsCandidate Ω T C) : Bottom Ω T ⊆ C :=
  fun _ h => h.2 C hC

/-- Arbitrary indexed product tests. -/
def ProductTest (Ω : ContextTower P) (D E : Expr S) (A : Set (Expr S))
    (Cs : Expr S → Set (Set (Expr S))) : Set (Expr S) :=
  {M | M ∈ Top Ω (.pi D E) ∧ ∀ n ∈ A, ∀ C ∈ Cs n, Expr.app M n ∈ C}

theorem productTest_candidate (hw : SystemWeaklyNormalizing P)
    {D E : Expr S} {A : Set (Expr S)} {Cs : Expr S → Set (Set (Expr S))}
    (hA : A ⊆ Top Ω D)
    (hCs : ∀ n ∈ A, ∀ C ∈ Cs n, IsCandidate Ω (E.instantiate n).normalForm C) :
    IsCandidate Ω (.pi D E) (ProductTest Ω D E A Cs) where
  lower := by
    intro M h
    refine ⟨ground_le_top h, ?_⟩
    intro n hn C hC
    exact (hCs n hn C hC).lower (ground_application hw h (hA hn))
  upper := fun _ h => h.1
  expansion := by
    intro D' b a ns ht hD hb ha hns hc
    refine ⟨⟨ht, StronglyNormalizing.head_expansion hD hb ha hns hc.1.2⟩, ?_⟩
    intro n hn C hC
    have ht' := (ht.application (hA hn).1).normalize_type hw
    have hsn : StronglyNormalizingArgs (ns ++ [n]) := by
      apply StronglyNormalizingArgs.of_forall
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hns.of_mem hx
      · have he : x = n := List.mem_singleton.mp hx
        exact he.symm ▸ (hA hn).2
    have hc' := hc.2 n hn C hC
    have he : (Expr.app (.lam D' b) a).apps (ns ++ [n]) =
        .app ((Expr.app (.lam D' b) a).apps ns) n := by
      simp only [Expr.apps_append, Expr.apps]
    have he' : (b.instantiate a).apps (ns ++ [n]) = .app ((b.instantiate a).apps ns) n := by
      simp only [Expr.apps_append, Expr.apps]
    rw [← he] at ht'
    rw [← he'] at hc'
    rw [← he]
    exact (hCs n hn C hC).expansion D' b a (ns ++ [n]) ht' hD hb ha hsn hc'

end Candidates

end S_wpc_barendregt_geuvers_klop

namespace S_wpc_barendregt_geuvers_klop.Candidates
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (T : Expr S)

abbrev Candidate := {X : Set (Expr S) // IsCandidate Ω T X}

noncomputable instance : InfSet (Candidate Ω T) where
  sInf Cs := ⟨Meet Ω T (Subtype.val '' Cs), meet_candidate (by
    rintro X ⟨x,_,rfl⟩
    exact x.property)⟩

noncomputable instance : CompleteLattice (Candidate Ω T) := completeLatticeOfInf _ (by
  intro Cs
  constructor
  · intro x hx M hM
    exact hM.2 x.val ⟨x,hx,rfl⟩
  · intro x hx M hM
    refine ⟨x.property.upper hM,?_⟩
    rintro X ⟨y,hy,rfl⟩
    exact hx hy hM)

/-- Changing coordinate order changes no candidate sets. -/
def SignedCandidate (b : Bool) : Type u := if b then (Candidate Ω T)ᵒᵈ else Candidate Ω T

noncomputable instance (b : Bool) : CompleteLattice (SignedCandidate Ω T b) := by
  cases b with
  | false => exact inferInstanceAs (CompleteLattice (Candidate Ω T))
  | true => exact inferInstanceAs (CompleteLattice (Candidate Ω T)ᵒᵈ)

namespace SignedCandidate
variable {Ω T} {b : Bool}

def set (X : SignedCandidate Ω T b) : Set (Expr S) := by
  cases b <;> exact X.val

def wrap (X : Candidate Ω T) : SignedCandidate Ω T b := by
  cases b <;> exact X

@[simp] theorem set_wrap (X : Candidate Ω T) : (wrap (b := b) X).set = X.val := by
  cases b <;> rfl

theorem candidate (X : SignedCandidate Ω T b) : IsCandidate Ω T X.set := by
  cases b <;> exact X.property

theorem order (X Y : SignedCandidate Ω T b) :
    X ≤ Y ↔ if b then Y.set ⊆ X.set else X.set ⊆ Y.set := by
  cases b <;> rfl

theorem ext {X Y : SignedCandidate Ω T b} (h : X.set = Y.set) : X = Y := by
  cases b <;> exact Subtype.ext h
end SignedCandidate
end S_wpc_barendregt_geuvers_klop.Candidates

end OMA



namespace OMA

namespace S_wpc_barendregt_geuvers_klop

universe u

/-- Sorts assigned to the full normal form. -/
def Profile {S : Type u} (P : Specification S) (Γ : List (Expr S))
    (T : Expr S) : Set S := {s | HasType P Γ T.normalForm (.sort s)}

def AxProfile {S : Type u} (P : Specification S) (s : S) : Set S :=
  {t | P.sortAxioms s t}

def OutProfile {S : Type u} (P : Specification S) (I J : Set S) : Set S :=
  {c | ∃ a ∈ I, ∃ b ∈ J, P.rule a b c}

/-- Semantic feasible profiles. Normal witnesses are retained, rather than
assuming the manuscript's characterization of this finite set. -/
def FeasibleProfile {S : Type u} (P : Specification S) (I : Set S) : Prop :=
  I.Nonempty ∧ ∃ Γ T, ValidContext P Γ ∧ Normal T ∧ Profile P Γ T = I

structure ProfileTriple {S : Type u} (P : Specification S) (I J K : Set S) : Prop where
  domain : FeasibleProfile P I
  codomain : FeasibleProfile P J
  product : FeasibleProfile P K
  output : K = OutProfile P I J

/-- The sign is true for a domain edge and false for a positive edge. -/
inductive PrimaryEdge {S : Type u} (P : Specification S) :
    Set S → Set S → Bool → Prop
  | inclusion {I J} : FeasibleProfile P I → FeasibleProfile P J →
      J ⊂ I → PrimaryEdge P I J false
  | domain {I J K} : ProfileTriple P I J K → PrimaryEdge P I K true
  | codomain {I J K} : ProfileTriple P I J K → PrimaryEdge P J K false

/-- Finite directed walks, with repeated edges permitted and parity retained. -/
inductive SignedPath {V : Type*} (E : V → V → Bool → Prop) : V → V → Bool → Prop
  | nil (v) : SignedPath E v v false
  | cons {u v w p q} : E u v p → SignedPath E v w q →
      SignedPath E u w (Bool.xor p q)

def Reach {V : Type*} (E : V → V → Bool → Prop) (v w : V) : Prop :=
  ∃ b, SignedPath E v w b

def PositivePath {V : Type*} (E : V → V → Bool → Prop) : V → V → Prop :=
  Relation.ReflTransGen (fun v w => E v w false)

/-- A full strongly connected component, not merely a connected subset. -/
def IsComponent {V : Type*} (E : V → V → Bool → Prop) (C : Set V) : Prop :=
  ∃ r ∈ C, ∀ v, v ∈ C ↔ Reach E r v ∧ Reach E v r

namespace SignedPath

variable {V : Type*} {E : V → V → Bool → Prop}

theorem singleton {v w : V} {p : Bool} (h : E v w p) : SignedPath E v w p := by
  simpa only [Bool.xor_false] using SignedPath.cons h (.nil w)

theorem append {v w z : V} {p q : Bool}
    (h : SignedPath E v w p) (k : SignedPath E w z q) :
    SignedPath E v z (Bool.xor p q) := by
  induction h with
  | nil v => simpa using k
  | cons he ht ih => simpa only [Bool.xor_assoc] using SignedPath.cons he (ih k)

theorem parity_unique {v w : V} {p q : Bool}
    (h : SignedPath E v w p) (k : SignedPath E v w q)
    (hr : Reach E w v) (hodd : ¬ SignedPath E v v true) : p = q := by
  obtain ⟨r, hr⟩ := hr
  have hpr := h.append hr
  have hqr := k.append hr
  cases p <;> cases q <;> cases r <;> simp_all

end SignedPath

namespace Reach

variable {V : Type*} {E : V → V → Bool → Prop} {v w z : V}

theorem refl (v : V) : Reach E v v := ⟨false, .nil v⟩

theorem trans (h : Reach E v w) (k : Reach E w z) : Reach E v z := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := k
  exact ⟨_, hp.append hq⟩

theorem single {p : Bool} (h : E v w p) : Reach E v w := ⟨p, .singleton h⟩

end Reach

namespace PositivePath

variable {V : Type*} {E : V → V → Bool → Prop} {v w : V}

theorem parity (h : PositivePath E v w) : SignedPath E v w false := by
  induction h with
  | refl => exact .nil _
  | tail _ he ih => exact ih.append (.singleton he)

theorem reach (h : PositivePath E v w) : Reach E v w := ⟨false, h.parity⟩

end PositivePath

namespace IsComponent

variable {V : Type*} {E : V → V → Bool → Prop} {C : Set V} {v w z : V}

theorem connected (h : IsComponent E C) (hv : v ∈ C) (hw : w ∈ C) : Reach E v w := by
  obtain ⟨r, hr, hc⟩ := h
  exact ((hc v).1 hv).2.trans ((hc w).1 hw).1

theorem between (h : IsComponent E C) (hv : v ∈ C) (hw : w ∈ C)
    (hvz : Reach E v z) (hzw : Reach E z w) : z ∈ C := by
  obtain ⟨r, hr, hc⟩ := h
  exact (hc z).2 ⟨((hc v).1 hv).1.trans hvz, hzw.trans ((hc w).1 hw).2⟩

end IsComponent

/-- Positive closure of the sort-profile seeds. -/
def ObservationLayers {S : Type u} (P : Specification S) (C : Set (Set S)) :
    Set (Set S) := {I | ∃ s, {s} ∈ C ∧ (AxProfile P s).Nonempty ∧
      PositivePath (PrimaryEdge P) (AxProfile P s) I}

inductive SecondaryEdge {S : Type u} (P : Specification S) (C : Set (Set S)) :
    Set S → Set S → Bool → Prop
  | positive {I J} : I ∈ ObservationLayers P C → J ∈ ObservationLayers P C →
      PrimaryEdge P I J false → SecondaryEdge P C I J false
  | negative {I J K} : I ∈ ObservationLayers P C → J ∈ ObservationLayers P C →
      K ∈ ObservationLayers P C → ProfileTriple P I J K →
      SecondaryEdge P C I K true

def DirectLayer {S : Type u} (P : Specification S) (C : Set (Set S))
    (I : Set S) : Prop := I ∈ ObservationLayers P C ∧
      ∃ J ∈ C, ∃ K ∈ C, ProfileTriple P I J K

def ActiveLayer {S : Type u} (P : Specification S) (C : Set (Set S))
    (I : Set S) : Prop := ∃ D, DirectLayer P C D ∧ Reach (SecondaryEdge P C) I D

def PlainLayer {S : Type u} (P : Specification S) (C : Set (Set S))
    (I : Set S) : Prop :=
  (∃ D, DirectLayer P C D ∧ SignedPath (SecondaryEdge P C) I D false) ∧
  (∃ D, DirectLayer P C D ∧ SignedPath (SecondaryEdge P C) I D true)

def FreeLayer {S : Type u} (P : Specification S) (C : Set (Set S))
    (I : Set S) (sign : Bool) : Prop := ¬ PlainLayer P C I ∧
      ∃ D, DirectLayer P C D ∧ SignedPath (SecondaryEdge P C) I D sign

/-- The finite-graph obstruction excluded by system-wide weak normalization.
It is not an extra hypothesis on the normalization theorem. -/

def ForbiddenConfiguration {S : Type u} (P : Specification S) (C : Set (Set S)) : Prop :=
  ∃ D : Set (Set S), IsComponent (SecondaryEdge P C) D ∧
    (∀ I ∈ D, PlainLayer P C I) ∧
    (∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true) ∧
    ∃ I J K s, ProfileTriple P I J K ∧ J ∈ D ∧ K ∈ D ∧ {s} ∈ D ∧
      (AxProfile P s).Nonempty ∧ PositivePath (PrimaryEdge P) (AxProfile P s) I

namespace PlainLayer

variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I J : Set S}

theorem active (h : PlainLayer P C I) : ActiveLayer P C I := by
  obtain ⟨D, hD, hp⟩ := h.1
  exact ⟨D, hD, false, hp⟩

theorem predecessor {b : Bool} (h : PlainLayer P C J) (e : SecondaryEdge P C I J b) :
    PlainLayer P C I := by
  obtain ⟨⟨D, hD, hp⟩, ⟨D', hD', hp'⟩⟩ := h
  cases b with
  | false => exact ⟨⟨D, hD, .cons e hp⟩, ⟨D', hD', .cons e hp'⟩⟩
  | true => exact ⟨⟨D', hD', .cons e hp'⟩, ⟨D, hD, .cons e hp⟩⟩

end PlainLayer

namespace FreeLayer

variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I J : Set S}

theorem active {s : Bool} (h : FreeLayer P C I s) : ActiveLayer P C I := by
  obtain ⟨D, hD, hp⟩ := h.2
  exact ⟨D, hD, s, hp⟩

theorem sign_unique {s t : Bool} (h : FreeLayer P C I s) (k : FreeLayer P C I t) : s = t := by
  obtain ⟨hn, D, hD, hp⟩ := h
  obtain ⟨_, D', hD', hp'⟩ := k
  cases s <;> cases t
  · rfl
  · exact False.elim (hn ⟨⟨D, hD, hp⟩, ⟨D', hD', hp'⟩⟩)
  · exact False.elim (hn ⟨⟨D', hD', hp'⟩, ⟨D, hD, hp⟩⟩)
  · rfl

theorem edge_sign {s t b : Bool} (h : FreeLayer P C I s) (k : FreeLayer P C J t)
    (e : SecondaryEdge P C I J b) : s = Bool.xor b t := by
  obtain ⟨D, hD, hp⟩ := k.2
  exact h.sign_unique ⟨h.1, D, hD, .cons e hp⟩

theorem direct_sign {s : Bool} (h : FreeLayer P C I s) (hd : DirectLayer P C I) :
    s = false := h.sign_unique ⟨h.1, I, hd, .nil I⟩

end FreeLayer

namespace Expr

variable {S : Type u}

@[simp] theorem normalForm_idem (M : Expr S) : M.normalForm.normalForm = M.normalForm := by
  classical
  by_cases h : WeaklyNormalizing M
  · exact normalForm_of_normal (normalForm_spec h).2
  · simp only [normalForm, dif_neg h]

theorem normalForm_rename {M : Expr S} (h : WeaklyNormalizing M) (ρ : Nat → Nat) :
    (M.rename ρ).normalForm = M.normalForm.rename ρ :=
  normalForm_eq ((normalForm_spec h).1.rename ρ) ((normalForm_spec h).2.rename ρ)

end Expr

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}

theorem lookup_sorted (hΓ : ValidContext P Γ) {n : Nat} {A : Expr S}
    (hn : Lookup Γ n A) : ∃ s, HasType P Γ A (.sort s) := by
  induction hΓ generalizing n A with
  | nil => cases hn
  | cons hΓ hB ih =>
      cases hn with
      | zero => exact ⟨_, .weaken hB hB⟩
      | succ _ hn =>
          obtain ⟨s, hs⟩ := ih hn
          exact ⟨s, .weaken hs hB⟩

theorem neutral_type_sorted {M A : Expr S} (hn : Neutral M)
    (ht : HasType P Γ M A) : ∃ s, HasType P Γ A (.sort s) := by
  cases hn with
  | var n =>
      obtain ⟨D, hD, hc⟩ := ht.generation
      obtain ⟨s, hs⟩ := lookup_sorted ht.valid hD
      obtain ⟨t, rfl⟩ | hA := ht.regularity
      · obtain ⟨Q, hDQ, hsQ⟩ := (show Converts D (.sort t) from .symm _ _ hc).join
        have heq := (Normal.sort t).reduces_eq hsQ
        subst Q
        exact ⟨s, hs.subject_reduces hDQ⟩
      · exact hA
  | app _ => exact ht.application_type_sorted

end HasType

namespace Profile

variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}

@[simp] theorem normalForm (T : Expr S) : Profile P Γ T.normalForm = Profile P Γ T := by
  simp only [Profile, Expr.normalForm_idem]

theorem of_normal {T : Expr S} (hn : Normal T) :
    Profile P Γ T = {s | HasType P Γ T (.sort s)} := by
  simp only [Profile, Expr.normalForm_of_normal hn]

theorem sort (hΓ : ValidContext P Γ) (s : S) :
    Profile P Γ (.sort s) = AxProfile P s := by
  rw [of_normal (Normal.sort s)]
  ext t
  constructor
  · intro h
    obtain ⟨u, hu, hc⟩ := h.generation
    have he := hc.sort_inj
    subst u
    exact hu
  · exact HasType.sort_of_valid hΓ

theorem neutral {M : Expr S} {s : S} (hn : Normal M) (hne : Neutral M)
    (ht : HasType P Γ M (.sort s)) : Profile P Γ M = {s} := by
  rw [of_normal hn]
  ext t
  constructor
  · intro h
    exact (ht.neutral_unique hne h).sort_inj.symm
  · intro h
    have he : t = s := h
    subst t
    exact ht

theorem neutral_axiom {M : Expr S} {s : S} (hne : Neutral M)
    (ht : HasType P Γ M (.sort s)) : (AxProfile P s).Nonempty := by
  obtain ⟨t, ht⟩ := ht.neutral_type_sorted hne
  obtain ⟨u, hu, hc⟩ := ht.generation
  exact ⟨u, hu⟩

theorem pi {A B : Expr S} (hnA : Normal A) (hnB : Normal B) :
    Profile P Γ (.pi A B) = OutProfile P (Profile P Γ A) (Profile P (A :: Γ) B) := by
  rw [of_normal (hnA.pi hnB), of_normal hnA, of_normal hnB]
  ext s
  constructor
  · intro ht
    obtain ⟨a, b, c, hA, hB, hr, hc⟩ := ht.generation_pi
    have he := hc.sort_inj
    subst c
    exact ⟨a, hA, b, hB, hr⟩
  · rintro ⟨a, hA, b, hB, hr⟩
    exact .product hA hB hr

theorem converts {A B : Expr S} (hA : WeaklyNormalizing A) (hB : WeaklyNormalizing B)
    (hc : Converts A B) : Profile P Γ A = Profile P Γ B := by
  simp only [Profile, Expr.normalForm_converts hA hB hc]

theorem growth (hw : SystemWeaklyNormalizing P) {T : Expr S}
    (hT : WeaklyNormalizing T) (hΔ : ValidContext P Δ) (σ : Nat → Expr S)
    (hσ : TypedSubstitution P Γ Δ σ) : Profile P Γ T ⊆ Profile P Δ (T.subst σ) := by
  intro s hs
  have ht : HasType P Δ (T.normalForm.subst σ) (.sort s) :=
    hs.subst hΔ σ hσ
  have hr := (Expr.normalForm_spec hT).1.subst σ
  have hrn := (Expr.normalForm_spec (ht.weaklyNormalizing hw)).1
  have hn := (Expr.normalForm_spec (ht.weaklyNormalizing hw)).2
  have heq := Expr.normalForm_eq (hr.trans hrn) hn
  change HasType P Δ (T.subst σ).normalForm (.sort s)
  rw [heq]
  exact ht.normalForm hw

theorem feasible {T : Expr S} (hT : WeaklyNormalizing T)
    (hne : (Profile P Γ T).Nonempty) : FeasibleProfile P (Profile P Γ T) := by
  obtain ⟨s, hs⟩ := hne
  exact ⟨⟨s, hs⟩, Γ, T.normalForm, hs.valid, (Expr.normalForm_spec hT).2, normalForm T⟩

end Profile

/-! Finite component order for the exact signed graphs of the manuscript. -/
namespace Reach
variable {V : Type u} (E : V → V → Bool → Prop)

def component (v : V) : Set V := {w | Reach E v w ∧ Reach E w v}

theorem mem_component (v : V) : v ∈ component E v := ⟨.refl v, .refl v⟩

theorem component_isComponent (v : V) : IsComponent E (component E v) :=
  ⟨v, mem_component E v, fun _ => Iff.rfl⟩

theorem component_eq {v w : V} (h : Reach E v w) (k : Reach E w v) :
    component E v = component E w := by
  ext z
  exact ⟨fun hz => ⟨k.trans hz.1, hz.2.trans h⟩,
    fun hz => ⟨h.trans hz.1, hz.2.trans k⟩⟩

variable [Fintype V]
open Classical

noncomputable def predecessors (v : V) : Finset V := Finset.univ.filter fun w => Reach E w v
noncomputable def rank (v : V) : Nat := (predecessors E v).card

@[simp] theorem mem_predecessors {v w : V} : w ∈ predecessors E v ↔ Reach E w v := by
  simp [predecessors]

theorem rank_mono {v w : V} (h : Reach E v w) : rank E v ≤ rank E w := by
  apply Finset.card_le_card
  intro z hz
  exact (mem_predecessors E).mpr (((mem_predecessors E).mp hz).trans h)

theorem reverse_of_rank_eq {v w : V} (h : Reach E v w) (he : rank E v = rank E w) :
    Reach E w v := by
  have hs : predecessors E v ⊆ predecessors E w := by
    intro z hz
    exact (mem_predecessors E).mpr (((mem_predecessors E).mp hz).trans h)
  have he' := Finset.eq_of_subset_of_card_le hs (le_of_eq he.symm)
  apply (mem_predecessors E).mp
  rw [he']
  exact (mem_predecessors E).mpr (.refl _)

theorem component_eq_of_rank_eq {v w : V} (h : Reach E v w)
    (he : rank E v = rank E w) : component E v = component E w :=
  component_eq E h (reverse_of_rank_eq E h he)

end Reach

namespace PlainLayer
variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I J : Set S}

theorem predecessor_path (h : PlainLayer P C J) (hp : Reach (SecondaryEdge P C) I J) :
    PlainLayer P C I := by
  obtain ⟨b, hp⟩ := hp
  induction hp with
  | nil => exact h
  | cons he _ ih => exact (ih h).predecessor he

theorem component_plain (h : PlainLayer P C I) :
    ∀ J ∈ Reach.component (SecondaryEdge P C) I, PlainLayer P C J := by
  intro J hJ
  exact h.predecessor_path hJ.2
end PlainLayer

namespace IsComponent
variable {V : Type u} {E : V → V → Bool → Prop} {C : Set V}
open Classical

noncomputable def signing (hc : IsComponent E C) (v : V) : Bool :=
  if h : v ∈ C then (hc.connected hc.choose_spec.1 h).choose else false

theorem signing_path (hc : IsComponent E C) {v : V} (hv : v ∈ C) :
    SignedPath E hc.choose v (hc.signing v) := by
  unfold signing
  rw [dif_pos hv]
  exact (hc.connected hc.choose_spec.1 hv).choose_spec

theorem signing_cross (hc : IsComponent E C)
    (hn : ∀ v ∈ C, ¬ SignedPath E v v true)
    {v w : V} {p : Bool} (hv : v ∈ C) (hw : w ∈ C) (hp : SignedPath E v w p) :
    hc.signing w = Bool.xor (hc.signing v) p := by
  exact (hc.signing_path hw).parity_unique ((hc.signing_path hv).append hp)
    (hc.connected hw hc.choose_spec.1) (hn _ hc.choose_spec.1)
end IsComponent
end S_wpc_barendregt_geuvers_klop

end OMA




namespace OMA

/-! Profile paths and the no-expanding-neutral-leaf dependency. -/

namespace S_wpc_barendregt_geuvers_klop
universe u
namespace Profile
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}

theorem nonempty_of_sorted (hw : SystemWeaklyNormalizing P) {M : Expr S} {s : S}
    (h : HasType P Γ M (.sort s)) : (Profile P Γ M).Nonempty :=
  ⟨s, h.normalForm hw⟩

theorem context_head_conversion {A A' M : Expr S} {s t : S}
    (hA : HasType P Γ A (.sort s)) (hA' : HasType P Γ A' (.sort t))
    (hc : Converts A A') : Profile P (A :: Γ) M = Profile P (A' :: Γ) M := by
  ext r
  exact ⟨fun h => HasType.context_head_conversion h hA hA' hc,
    fun h => HasType.context_head_conversion h hA' hA (.symm _ _ hc)⟩

theorem inclusion_path {I J : Set S} (hI : FeasibleProfile P I)
    (hJ : FeasibleProfile P J) (h : J ⊆ I) : PositivePath (PrimaryEdge P) I J := by
  classical
  by_cases he : I = J
  · subst J; exact .refl
  · exact .single (.inclusion hI hJ (Set.ssubset_iff_subset_ne.mpr ⟨h, Ne.symm he⟩))

theorem triple (hw : SystemWeaklyNormalizing P) {D E : Expr S} {s : S}
    (h : HasType P Γ (.pi D E) (.sort s)) :
    ProfileTriple P (Profile P Γ D) (Profile P (D :: Γ) E) (Profile P Γ (.pi D E)) := by
  obtain ⟨a, b, c, hD, hE, _, _⟩ := h.generation_pi
  have wD := hD.weaklyNormalizing hw
  have wE := hE.weaklyNormalizing hw
  have hD' := hD.normalForm hw
  have he : Profile P (D.normalForm :: Γ) E = Profile P (D :: Γ) E :=
    (context_head_conversion hD hD' (Expr.normalForm_spec wD).1.converts).symm
  refine ⟨feasible wD (nonempty_of_sorted hw hD),
    feasible wE (nonempty_of_sorted hw hE),
    feasible (h.weaklyNormalizing hw) (nonempty_of_sorted hw h), ?_⟩
  calc
    Profile P Γ (.pi D E) = Profile P Γ (.pi D.normalForm E.normalForm) := by
      rw [← Expr.normalForm_pi wD wE, Profile.normalForm]
    _ = OutProfile P (Profile P Γ D.normalForm)
        (Profile P (D.normalForm :: Γ) E.normalForm) :=
      pi (Expr.normalForm_spec wD).2 (Expr.normalForm_spec wE).2
    _ = OutProfile P (Profile P Γ D) (Profile P (D :: Γ) E) := by
      rw [Profile.normalForm, Profile.normalForm, he]

/-- The exact positive ascent from an instantiated codomain to its product.
It uses all sortings rather than choosing a functional specification. -/
theorem instantiate_product_path (hw : SystemWeaklyNormalizing P)
    {D E n : Expr S} {s : S} (h : HasType P Γ (.pi D E) (.sort s))
    (hn : HasType P Γ n D) :
    PositivePath (PrimaryEdge P) (Profile P Γ (E.instantiate n))
      (Profile P Γ (.pi D E)) := by
  obtain ⟨a, b, c, hD, hE, _, _⟩ := h.generation_pi
  have hout := hE.instantiate hn
  have hg := growth hw (hE.weaklyNormalizing hw) hn.valid _ (TypedSubstitution.single hn)
  have hp := inclusion_path
    (feasible (hout.weaklyNormalizing hw) (nonempty_of_sorted hw hout))
    (feasible (hE.weaklyNormalizing hw) (nonempty_of_sorted hw hE)) hg
  exact hp.trans (.single (.codomain (triple hw h)))
end Profile

namespace Expr
variable {S : Type u}
def head : Expr S → Expr S
  | .app f _ => head f
  | M => M
@[simp] theorem head_apps (M : Expr S) (ns : List (Expr S)) : (M.apps ns).head = M.head := by
  induction ns generalizing M with
  | nil => rfl
  | cons n ns ih => exact ih (.app M n)
end Expr

namespace HasType
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}

/-- Reading a neutral spine backwards gives a positive path from the exact
result-type profile to the declaration-type profile of its head. -/
theorem neutral_profile_ascent (hw : SystemWeaklyNormalizing P)
    {M T : Expr S} (hn : Neutral M) (h : HasType P Γ M T) :
    ∃ n D, M.head = .var n ∧ Lookup Γ n D ∧
      PositivePath (PrimaryEdge P) (Profile P Γ T) (Profile P Γ D) := by
  induction hn generalizing T with
  | var n =>
      obtain ⟨D, hD, hc⟩ := h.generation
      refine ⟨n, D, rfl, hD, ?_⟩
      rw [Profile.converts (h.type_weaklyNormalizing hw)
        ((HasType.lookup h.valid hD).type_weaklyNormalizing hw) hc]
      exact .refl
  | @app f a hnf ih =>
      obtain ⟨D, E, hf, ha, hc⟩ := h.generation_app
      obtain ⟨s, hp⟩ := hf.product_type_sorted
      obtain ⟨n, A, hh, hl, hr⟩ := ih hf
      refine ⟨n, A, hh, hl, ?_⟩
      rw [Profile.converts (h.type_weaklyNormalizing hw)
        ((HasType.application hf ha).type_weaklyNormalizing hw) hc]
      exact (Profile.instantiate_product_path hw hp ha).trans hr

/-- This is the precise seed generated when a normal neutral type can be
changed at its head by substitution. The sort axiom is derived, not assumed. -/
theorem neutral_profile_seed (hw : SystemWeaklyNormalizing P)
    {M : Expr S} {s : S} (hn : Neutral M) (hM : Normal M)
    (h : HasType P Γ M (.sort s)) :
    Profile P Γ M = {s} ∧ (AxProfile P s).Nonempty ∧
      ∃ n D, M.head = .var n ∧ Lookup Γ n D ∧
        PositivePath (PrimaryEdge P) (AxProfile P s) (Profile P Γ D) := by
  refine ⟨Profile.neutral hM hn h, Profile.neutral_axiom hn h, ?_⟩
  simpa only [Profile.sort h.valid] using neutral_profile_ascent hw hn h
end HasType

namespace Neutral
variable {S : Type u} {M N : Expr S}

theorem rename (h : Neutral M) (ρ : Nat → Nat) : Neutral (M.rename ρ) := by
  induction h with
  | var n => exact .var _
  | app h ih => exact .app ih

theorem subst_of_head (h : Neutral M) (σ : Nat → Expr S)
    (hh : ∀ n, M.head = .var n → Neutral (σ n)) : Neutral (M.subst σ) := by
  induction h with
  | var n => exact hh n rfl
  | app h ih => exact .app (ih hh)

theorem beta (h : Neutral M) (hr : Beta M N) : Neutral N := by
  induction h generalizing N with
  | var n => cases hr
  | @app f a h ih =>
      cases hr with
      | app_left hr => exact .app (ih hr)
      | app_right _ => exact .app h
      | head => cases h

theorem reduces (h : Neutral M) (hr : Reduces M N) : Neutral N := by
  induction hr with
  | refl => exact h
  | tail _ hr ih => exact ih.beta hr

theorem normalForm (h : Neutral M) (hw : WeaklyNormalizing M) : Neutral M.normalForm :=
  h.reduces (Expr.normalForm_spec hw).1
end Neutral

/- A typed renaming preserves exact profiles of sorted types. The reverse
inclusion uses neutral uniqueness; it does not falsely assume functionality. -/
namespace Profile
variable {S : Type u} {P : Specification S}

theorem rename_normal {Γ Δ : List (Expr S)} {T : Expr S} {s : S}
    (hT : HasType P Γ T (.sort s)) (hn : Normal T)
    (hΔ : ValidContext P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasType P Δ (.var (ρ n)) (B.rename ρ)) :
    Profile P Δ (T.rename ρ) = Profile P Γ T := by
  induction T generalizing Γ Δ s ρ with
  | var n =>
      rw [neutral (hn.rename ρ) (.var _) (hT.rename hΔ ρ hρ), neutral hn (.var _) hT]
  | sort t =>
      exact (sort hΔ t).trans (sort hT.valid t).symm
  | app f a ihf iha =>
      have hneutral : Neutral (.app f a) := by
        obtain ⟨t, he⟩ | h | ⟨D, E, he⟩ := hT.sorted_normal_shape hn
        · cases he
        · exact h
        · cases he
      rw [neutral (hn.rename ρ) (hneutral.rename ρ) (hT.rename hΔ ρ hρ),
        neutral hn hneutral hT]
  | lam A b ihA ihb => exact False.elim hT.lambda_cannot_have_sort_type
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
      have hA' := hA.rename hΔ ρ hρ
      have hr : ∀ n D, Lookup (A :: Γ) n D →
          HasType P (A.rename ρ :: Δ) (.var (Expr.liftRen ρ n))
            (D.rename (Expr.liftRen ρ)) := by
        intro n D hD
        cases hD with
        | zero =>
            simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def] using HasType.var hA'
        | succ _ hD =>
            simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def, Expr.rename] using
              HasType.weaken (hρ _ _ hD) hA'
      rw [Expr.rename, pi (hn.pi_domain.rename ρ) (hn.pi_body.rename _), pi hn.pi_domain hn.pi_body,
        ihA hA hn.pi_domain hΔ ρ hρ,
        ihB hB hn.pi_body (.cons hΔ hA') _ hr]

theorem rename (hw : SystemWeaklyNormalizing P)
    {Γ Δ : List (Expr S)} {T : Expr S} {s : S}
    (hT : HasType P Γ T (.sort s)) (hΔ : ValidContext P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasType P Δ (.var (ρ n)) (B.rename ρ)) :
    Profile P Δ (T.rename ρ) = Profile P Γ T := by
  rw [← normalForm T, ← normalForm (T.rename ρ), Expr.normalForm_rename (hT.weaklyNormalizing hw) ρ]
  exact rename_normal (hT.normalForm hw) (Expr.normalForm_spec (hT.weaklyNormalizing hw)).2 hΔ ρ hρ

theorem weaken (hw : SystemWeaklyNormalizing P) {Γ : List (Expr S)}
    {T D : Expr S} {s t : S} (hT : HasType P Γ T (.sort s))
    (hD : HasType P Γ D (.sort t)) :
    Profile P (D :: Γ) (T.rename Nat.succ) = Profile P Γ T :=
  rename hw hT (.cons hD.valid hD) Nat.succ
    (fun _ _ hn => .weaken (HasType.lookup hD.valid hn) hD)
end Profile

/-- Every image which can replace a neutral head originates at the chosen
outer binder profile. Ordinary one-variable substitution, and every lifting
of it through additional binders, have this property. -/
def SingleSource {S : Type u} (P : Specification S) (Γ : List (Expr S))
    (σ : Nat → Expr S) (I : Set S) : Prop :=
  ∀ n D, Lookup Γ n D → ¬ Neutral (σ n) → Profile P Γ D = I

namespace SingleSource
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}
    {σ : Nat → Expr S} {I : Set S}

theorem single (hw : SystemWeaklyNormalizing P) {D q : Expr S} {s : S}
    (hD : HasType P Γ D (.sort s)) :
    SingleSource P (D :: Γ) (Expr.single q) (Profile P Γ D) := by
  intro n A hn hbad
  cases hn with
  | zero => exact Profile.weaken hw hD hD
  | succ _ _ => exact False.elim (hbad (.var _))

theorem lift (hw : SystemWeaklyNormalizing P) (h : SingleSource P Γ σ I)
    {D : Expr S} {s : S} (hD : HasType P Γ D (.sort s)) :
    SingleSource P (D :: Γ) (Expr.liftSub σ) I := by
  intro n A hn hbad
  cases hn with
  | zero => exact False.elim (hbad (.var 0))
  | succ _ hn =>
      obtain ⟨t, hA⟩ := HasType.lookup_sorted hD.valid hn
      rw [Profile.weaken hw hA hD]
      exact h _ _ hn (fun hh => hbad (hh.rename Nat.succ))
end SingleSource

namespace ForbiddenConfiguration
variable {S : Type u} {P : Specification S} {C D : Set (Set S)}

/-- The source's critical neutral-leaf argument. No beta-normal neutral leaf
in this component can become a product under substitution of the outer
binder: doing so would produce exactly the excluded graph configuration. -/
theorem of_neutral_expansion (hw : SystemWeaklyNormalizing P)
    (hD : IsComponent (SecondaryEdge P C) D) (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hneg : ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true)
    {I J K : Set S} (htr : ProfileTriple P I J K) (hJ : J ∈ D) (hK : K ∈ D)
    {Γ Δ : List (Expr S)} (hΔ : ValidContext P Δ) {σ : Nat → Expr S}
    (hσ : TypedSubstitution P Γ Δ σ) (hsrc : SingleSource P Γ σ I)
    {M A B : Expr S} {s : S} (h : HasType P Γ M (.sort s))
    (hn : Normal M) (hne : Neutral M) (hM : Profile P Γ M ∈ D)
    (he : (M.subst σ).normalForm = .pi A B) : ForbiddenConfiguration P C := by
  obtain ⟨hp, hax, n, F, hh, hf, hpath⟩ := h.neutral_profile_seed hw hne hn
  have hbad : ¬ Neutral (σ n) := by
    intro hs
    have hM' := hne.subst_of_head σ (by
      intro m hm
      have heq : m = n := by simpa only [hh, Expr.var.injEq] using hm.symm
      exact heq.symm ▸ hs)
    have hnorm := hM'.normalForm ((h.subst hΔ σ hσ).weaklyNormalizing hw)
    rw [he] at hnorm
    cases hnorm
  have hF := hsrc n F hf hbad
  rw [hF] at hpath
  exact ⟨D, hD, hplain, hneg, I, J, K, s, htr, hJ, hK, hp ▸ hM, hax, hpath⟩
end ForbiddenConfiguration

namespace ObservationLayers
variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I J : Set S}
theorem positive (h : I ∈ ObservationLayers P C) (hp : PositivePath (PrimaryEdge P) I J) :
    J ∈ ObservationLayers P C := by
  obtain ⟨s, hs, hax, hpath⟩ := h
  exact ⟨s, hs, hax, hpath.trans hp⟩

theorem secondary (h : I ∈ ObservationLayers P C) (hp : PositivePath (PrimaryEdge P) I J) :
    PositivePath (SecondaryEdge P C) I J := by
  induction hp with
  | refl => exact .refl
  | @tail J K hp he ih =>
      exact .tail ih (.positive (positive h hp) (positive h (.tail hp he)) he)
end ObservationLayers

namespace ActiveLayer
variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I J : Set S}

theorem layer (h : ActiveLayer P C I) : I ∈ ObservationLayers P C := by
  obtain ⟨D, hD, b, hp⟩ := h
  cases hp with
  | nil => exact hD.1
  | cons he _ => cases he with
    | positive hI _ _ => exact hI
    | negative hI _ _ _ => exact hI

theorem predecessor (h : ActiveLayer P C J) (hp : Reach (SecondaryEdge P C) I J) :
    ActiveLayer P C I := by
  obtain ⟨D, hD, hr⟩ := h
  exact ⟨D, hD, hp.trans hr⟩
end ActiveLayer

namespace IsComponent
variable {S : Type u} {P : Specification S} {C D : Set (Set S)}

/-- Interpolation of a counted post-substitution codomain through the
original product triple. -/
theorem codomain_interpolation (hD : IsComponent (SecondaryEdge P C) D)
    (hl : ∀ X ∈ D, X ∈ ObservationLayers P C)
    {I J K J' : Set S} (htr : ProfileTriple P I J K) (hK : K ∈ D) (hJ' : J' ∈ D)
    (hJJ' : PositivePath (PrimaryEdge P) J' J) : J ∈ D := by
  have hJH := ObservationLayers.positive (hl J' hJ') hJJ'
  exact hD.between hJ' hK (ObservationLayers.secondary (hl J' hJ') hJJ').reach
    (Reach.single (.positive hJH (hl K hK) (.codomain htr)))

/-- Domain interpolation also needs the post open codomain to be active;
this is exactly the side condition in the source potential, not a stronger
assumption that every domain dependency is retained. -/
theorem domain_interpolation (hD : IsComponent (SecondaryEdge P C) D)
    (hl : ∀ X ∈ D, X ∈ ObservationLayers P C)
    (ha : ∀ X ∈ D, ActiveLayer P C X)
    {I J K I' J' : Set S} (htr : ProfileTriple P I J K) (hK : K ∈ D)
    (hI' : I' ∈ D) (hJ' : ActiveLayer P C J')
    (hII' : PositivePath (PrimaryEdge P) I' I)
    (hJJ' : PositivePath (PrimaryEdge P) J' J) :
    I ∈ D ∧ ActiveLayer P C J := by
  have hIH := ObservationLayers.positive (hl I' hI') hII'
  have hJH := ObservationLayers.positive hJ'.layer hJJ'
  have hKH := hl K hK
  exact ⟨hD.between hI' hK (ObservationLayers.secondary (hl I' hI') hII').reach
    (Reach.single (.negative hIH hJH hKH htr)),
    (ha K hK).predecessor (Reach.single (.positive hJH hKH (.codomain htr)))⟩
end IsComponent

namespace Profile
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}
theorem growth_path (hw : SystemWeaklyNormalizing P) {T : Expr S} {s : S}
    (hT : HasType P Γ T (.sort s)) (hΔ : ValidContext P Δ) (σ : Nat → Expr S)
    (hσ : TypedSubstitution P Γ Δ σ) :
    PositivePath (PrimaryEdge P) (Profile P Δ (T.subst σ)) (Profile P Γ T) := by
  have ht := hT.subst hΔ σ hσ
  exact inclusion_path (feasible (ht.weaklyNormalizing hw) (nonempty_of_sorted hw ht))
    (feasible (hT.weaklyNormalizing hw) (nonempty_of_sorted hw hT))
    (growth hw (hT.weaklyNormalizing hw) hΔ σ hσ)
end Profile

/-- Context conversion as exact equality of all judgments on unchanged
syntax. Both contexts are required valid. This auxiliary relation carries
no semantic or normalization assumption. -/
structure ContextEquivalent {S : Type u} (P : Specification S)
    (Γ Δ : List (Expr S)) : Prop where
  valid_left : ValidContext P Γ
  valid_right : ValidContext P Δ
  typing : ∀ (M A : Expr S), HasType P Γ M A ↔ HasType P Δ M A

namespace ContextEquivalent
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}
theorem symm (h : ContextEquivalent P Γ Δ) : ContextEquivalent P Δ Γ :=
  ⟨h.valid_right, h.valid_left, fun _ _ => (h.typing _ _).symm⟩

theorem profile (h : ContextEquivalent P Γ Δ) (M : Expr S) :
    Profile P Γ M = Profile P Δ M := by
  ext s
  exact h.typing _ _

theorem cons (h : ContextEquivalent P Γ Δ) {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) : ContextEquivalent P (A :: Γ) (A :: Δ) := by
  have lift_dir {Γ Δ : List (Expr S)} (h : ContextEquivalent P Γ Δ)
      (hA : HasType P Γ A (.sort s)) :
      ∀ M B, HasType P (A :: Γ) M B → HasType P (A :: Δ) M B := by
    intro M B ht
    have hA' := (h.typing _ _).1 hA
    have hs : TypedSubstitution P (A :: Γ) (A :: Δ) Expr.var := by
      intro n D hn
      rw [Expr.subst_var]
      cases hn with
      | zero => exact .var hA'
      | succ _ hn => exact .weaken ((h.typing _ _).1 (HasType.lookup h.valid_left hn)) hA'
    simpa only [Expr.subst_var] using ht.subst (.cons h.valid_right hA') _ hs
  have hA' := (h.typing _ _).1 hA
  exact ⟨.cons h.valid_left hA, .cons h.valid_right hA',
    fun M B => ⟨lift_dir h hA M B, lift_dir h.symm hA' M B⟩⟩

theorem head_conversion {A B : Expr S} {s t : S}
    (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort t))
    (hc : Converts A B) : ContextEquivalent P (A :: Γ) (B :: Γ) :=
  ⟨.cons hA.valid hA, .cons hB.valid hB, fun _ _ =>
    ⟨fun h => h.context_head_conversion hA hB hc,
      fun h => h.context_head_conversion hB hA (.symm _ _ hc)⟩⟩
end ContextEquivalent

namespace PlainObservations
open Classical
variable {S : Type u}
/-- The exact source syntax-tree potential. Its recursive child conditions
retain the active-open-codomain guard on a counted domain. -/
noncomputable def potential (P : Specification S) (C D : Set (Set S))
    (Γ : List (Expr S)) : Expr S → Nat
  | .pi A B => by
      classical
      exact 1 +
      (if Profile P Γ A ∈ D ∧ ActiveLayer P C (Profile P (A :: Γ) B)
       then potential P C D Γ A else 0) +
      (if Profile P (A :: Γ) B ∈ D then potential P C D (A :: Γ) B else 0)
  | _ => 1

variable {P : Specification S} {C D : Set (Set S)}

theorem potential_context {Γ Δ : List (Expr S)} {T : Expr S} {s : S}
    (hT : HasType P Γ T (.sort s)) (h : ContextEquivalent P Γ Δ) :
    potential P C D Γ T = potential P C D Δ T := by
  induction T generalizing Γ Δ s with
  | var n | sort t | app f a | lam A b => rfl
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
      simp only [potential]
      rw [h.profile A, (h.cons hA).profile B, ihA hA h, ihB hB (h.cons hA)]

/-- Normalizing a product does not change the contexts in which its child
contributions are measured: raw and normalized annotations are context
convertible. This keeps the dependent codomain count honest. -/
theorem potential_normalized_pi (hw : SystemWeaklyNormalizing P)
    {Γ : List (Expr S)} {A B : Expr S} {s : S}
    (h : HasType P Γ (.pi A B) (.sort s)) :
    potential P C D Γ (Expr.pi A B).normalForm = 1 +
      (if Profile P Γ A ∈ D ∧ ActiveLayer P C (Profile P (A :: Γ) B)
       then potential P C D Γ A.normalForm else 0) +
      (if Profile P (A :: Γ) B ∈ D then potential P C D (A :: Γ) B.normalForm else 0) := by
  classical
  obtain ⟨a, b, c, hA, hB, _, _⟩ := h.generation_pi
  have wA := hA.weaklyNormalizing hw
  have wB := hB.weaklyNormalizing hw
  have hc := ContextEquivalent.head_conversion hA (hA.normalForm hw) (Expr.normalForm_spec wA).1.converts
  have hp := (potential_context (C := C) (D := D) (hB.normalForm hw) hc).symm
  rw [Expr.normalForm_pi wA wB, potential, ← hc.profile B.normalForm, hp,
    Profile.normalForm, Profile.normalForm]

/-- The full potential inequality. The outer triple and its codomain/product
vertices are fixed exactly as in the source legal-frame argument. SingleSource
is proved above for the actual one-variable substitution and all binder lifts. -/
theorem potential_subst_le (hw : SystemWeaklyNormalizing P)
    (hno : ¬ ForbiddenConfiguration P C)
    (hD : IsComponent (SecondaryEdge P C) D) (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hneg : ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true)
    {I J K : Set S} (htr : ProfileTriple P I J K) (hJ : J ∈ D) (hK : K ∈ D)
    {Γ Δ : List (Expr S)} (hΔ : ValidContext P Δ) {σ : Nat → Expr S}
    (hσ : TypedSubstitution P Γ Δ σ) (hsrc : SingleSource P Γ σ I)
    {T : Expr S} {s : S} (hT : HasType P Γ T (.sort s)) (hn : Normal T)
    (hTC : Profile P Γ T ∈ D) :
    potential P C D Δ (T.subst σ).normalForm ≤ potential P C D Γ T := by
  classical
  have ha : ∀ X ∈ D, ActiveLayer P C X := fun X hX => (hplain X hX).active
  have hl : ∀ X ∈ D, X ∈ ObservationLayers P C := fun X hX => (ha X hX).layer
  have leaf {Γ Δ : List (Expr S)} {σ : Nat → Expr S} {M : Expr S} {s : S}
      (hΔ : ValidContext P Δ) (hσ : TypedSubstitution P Γ Δ σ)
      (hsrc : SingleSource P Γ σ I) (hM : HasType P Γ M (.sort s))
      (hn : Normal M) (hne : Neutral M) (hMC : Profile P Γ M ∈ D) :
      potential P C D Δ (M.subst σ).normalForm = 1 := by
    cases he : (M.subst σ).normalForm with
    | pi A B =>
        exact False.elim (hno (ForbiddenConfiguration.of_neutral_expansion hw hD hplain hneg
          htr hJ hK hΔ hσ hsrc hM hn hne hMC he))
    | var n | sort t | app f a | lam A b => rfl
  induction T generalizing Γ Δ σ s with
  | var n => exact le_of_eq (leaf hΔ hσ hsrc hT hn (.var n) hTC)
  | sort t => simp only [Expr.subst, Expr.normalForm_of_normal (Normal.sort t), potential, le_refl]
  | lam A b => exact False.elim hT.lambda_cannot_have_sort_type
  | app f a ihf iha =>
      have hneutral : Neutral (.app f a) := by
        obtain ⟨t, he⟩ | h | ⟨A, B, he⟩ := hT.sorted_normal_shape hn
        · cases he
        · exact h
        · cases he
      exact le_of_eq (leaf hΔ hσ hsrc hT hn hneutral hTC)
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
      have hA' := hA.subst hΔ σ hσ
      have hΔ' : ValidContext P (A.subst σ :: Δ) := .cons hΔ hA'
      have hσ' := hσ.lift hA'
      have hB' := hB.subst hΔ' _ hσ'
      have htr' := Profile.triple hw hT
      have hAp := Profile.growth_path hw hA hΔ σ hσ
      have hBp := Profile.growth_path hw hB hΔ' _ hσ'
      rw [Expr.subst, potential_normalized_pi hw (hT.subst hΔ σ hσ), potential]
      apply Nat.add_le_add
      · apply Nat.add_le_add_left
        split_ifs with hc hc'
        · exact ihA hΔ hσ hsrc hA hn.pi_domain hc'.1
        · obtain ⟨hAC, hBa⟩ := hD.domain_interpolation hl ha htr' hTC hc.1 hc.2 hAp hBp
          exact False.elim (hc' ⟨hAC, hBa⟩)
        · exact Nat.zero_le _
        · exact le_rfl
      · split_ifs with hc hc'
        · exact ihB hΔ' hσ' (hsrc.lift hw hA) hB hn.pi_body hc'
        · exact False.elim (hc' (hD.codomain_interpolation hl htr' hTC hc hBp))
        · exact Nat.zero_le _
        · exact le_rfl

theorem potential_pos (Γ : List (Expr S)) (T : Expr S) : 0 < potential P C D Γ T := by
  cases T <;> simp only [potential] <;> omega

/-- Exact legal-frame potential drop in the negative plain component,
including the strict syntactic-child inequality. -/
theorem frame_potential_drop (hw : SystemWeaklyNormalizing P)
    (hno : ¬ ForbiddenConfiguration P C)
    (hD : IsComponent (SecondaryEdge P C) D) (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hneg : ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true)
    {Γ : List (Expr S)} {A B n : Expr S} {s : S}
    (hT : HasType P Γ (.pi A B) (.sort s)) (hnT : Normal (.pi A B))
    (hn : HasType P Γ n A) (hK : Profile P Γ (.pi A B) ∈ D)
    (hL : Profile P Γ (B.instantiate n) ∈ D) :
    potential P C D Γ (B.instantiate n).normalForm ≤ potential P C D (A :: Γ) B ∧
      potential P C D (A :: Γ) B < potential P C D Γ (.pi A B) := by
  have ha : ∀ X ∈ D, ActiveLayer P C X := fun X hX => (hplain X hX).active
  have hl : ∀ X ∈ D, X ∈ ObservationLayers P C := fun X hX => (ha X hX).layer
  obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
  have htr := Profile.triple hw hT
  have hp := Profile.growth_path hw hB hn.valid _ (TypedSubstitution.single hn)
  have hJ := hD.codomain_interpolation hl htr hK hL hp
  refine ⟨potential_subst_le hw hno hD hplain hneg htr hJ hK hn.valid
    (TypedSubstitution.single hn) (SingleSource.single hw hA) hB hnT.pi_body hJ, ?_⟩
  simp only [potential, if_pos hJ]
  omega

theorem frame_domain_drop (hplain : ∀ I ∈ D, PlainLayer P C I)
    {Γ : List (Expr S)} {A B : Expr S}
    (hI : Profile P Γ A ∈ D) (hJ : Profile P (A :: Γ) B ∈ D) :
    potential P C D Γ A < potential P C D Γ (.pi A B) := by
  have hc : Profile P Γ A ∈ D ∧ ActiveLayer P C (Profile P (A :: Γ) B) :=
    ⟨hI, (hplain _ hJ).active⟩
  simp only [potential, if_pos hc, if_pos hJ]
  omega

/-- The potential counts positions, so valid thinning does not change it.
The equality is exact also under every dependent binder. -/
theorem potential_rename (hw : SystemWeaklyNormalizing P)
    {Γ Δ : List (Expr S)} {T : Expr S} {s : S}
    (hT : HasType P Γ T (.sort s)) (hΔ : ValidContext P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasType P Δ (.var (ρ n)) (B.rename ρ)) :
    potential P C D Δ (T.rename ρ) = potential P C D Γ T := by
  induction T generalizing Γ Δ s ρ with
  | var n | sort t | app f a | lam A b => rfl
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
      have hA' := hA.rename hΔ ρ hρ
      have hr : ∀ n E, Lookup (A :: Γ) n E →
          HasType P (A.rename ρ :: Δ) (.var (Expr.liftRen ρ n))
            (E.rename (Expr.liftRen ρ)) := by
        intro n E hE
        cases hE with
        | zero =>
            simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def] using HasType.var hA'
        | succ _ hE =>
            simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def, Expr.rename] using
              HasType.weaken (hρ _ _ hE) hA'
      simp only [Expr.rename, potential]
      rw [Profile.rename hw hA hΔ ρ hρ,
        Profile.rename hw hB (.cons hΔ hA') _ hr,
        ihA hA hΔ ρ hρ, ihB hB (.cons hΔ hA') _ hr]

end PlainObservations

namespace ContextTower

section
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

/-- The source profile on syntax with fixed global variable names. -/
def profile (T : Expr S) : Set S := {s | Ω.HasType T.normalForm (.sort s)}

variable (hw : SystemWeaklyNormalizing P)
include hw

theorem profile_at_next {n : Nat} {T : Expr S} {s : S}
    (ht : S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)) :
    Profile P (Ω.context (n+1)) (T.rename (Expr.reverseIndex (n+1))) =
      Profile P (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  have hs : T.Scoped n := by
    have h := ht.scope.1.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at h
  obtain ⟨D, t, hD, he⟩ := Ω.step n
  rw [he, hs.reverseIndex_succ]
  exact Profile.weaken hw ht hD

theorem profile_at_mono {n m : Nat} {T : Expr S} {s : S}
    (ht : S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s))
    (h : n ≤ m) :
    Profile P (Ω.context m) (T.rename (Expr.reverseIndex m)) =
      Profile P (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  induction h with
  | refl => rfl
  | @step m h ih => exact (Ω.profile_at_next hw (Ω.at_mono (A := .sort s) ht h)).trans ih

/-- A single available sorting fixes the exact profile at every later
prefix. Extra sorting rules cannot appear merely by weakening. -/
theorem profile_at {n : Nat} {T : Expr S} {s : S}
    (ht : S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)) :
    Ω.profile T = Profile P (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  have w : WeaklyNormalizing T := (show Ω.HasType T (.sort s) from ⟨n, ht⟩).weaklyNormalizing hw
  ext t
  constructor
  · rintro ⟨m, hm⟩
    have hn := Ω.at_mono (A := .sort t) hm (le_max_left m n)
    change S_wpc_barendregt_geuvers_klop.HasType P (Ω.context (max m n))
      (T.normalForm.rename (Expr.reverseIndex (max m n))) (.sort t) at hn
    rw [← Expr.normalForm_rename w] at hn
    have he := Ω.profile_at_mono hw ht (le_max_right m n)
    exact he ▸ hn
  · intro hn
    refine ⟨n, ?_⟩
    change S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.normalForm.rename (Expr.reverseIndex n)) (.sort t)
    rw [← Expr.normalForm_rename w]
    exact hn

omit hw in
theorem profile_normalForm (T : Expr S) : Ω.profile T.normalForm = Ω.profile T := by
  simp only [profile, Expr.normalForm_idem]

theorem profile_nonempty {T : Expr S} {s : S} (ht : Ω.HasType T (.sort s)) :
    (Ω.profile T).Nonempty := ⟨s, ht.normalForm hw⟩

theorem profile_feasible {T : Expr S} {s : S} (ht : Ω.HasType T (.sort s)) :
    FeasibleProfile P (Ω.profile T) := by
  obtain ⟨n, hn⟩ := ht
  change S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s) at hn
  rw [Ω.profile_at hw hn]
  exact Profile.feasible (hn.weaklyNormalizing hw) (Profile.nonempty_of_sorted hw hn)

theorem potential_at_next (C D : Set (Set S)) {n : Nat} {T : Expr S} {s : S}
    (ht : S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)) :
    PlainObservations.potential P C D (Ω.context (n+1)) (T.rename (Expr.reverseIndex (n+1))) =
      PlainObservations.potential P C D (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  have hs : T.Scoped n := by
    have h := ht.scope.1.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at h
  obtain ⟨A, t, hA, he⟩ := Ω.step n
  rw [he, hs.reverseIndex_succ]
  exact PlainObservations.potential_rename hw ht (.cons hA.valid hA) Nat.succ
    (fun _ _ hn => .weaken (S_wpc_barendregt_geuvers_klop.HasType.lookup hA.valid hn) hA)

theorem potential_at_mono (C D : Set (Set S)) {n m : Nat} {T : Expr S} {s : S}
    (ht : S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s))
    (h : n ≤ m) :
    PlainObservations.potential P C D (Ω.context m) (T.rename (Expr.reverseIndex m)) =
      PlainObservations.potential P C D (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  induction h with
  | refl => rfl
  | @step m h ih =>
      exact (Ω.potential_at_next hw C D (Ω.at_mono (A := .sort s) ht h)).trans ih

noncomputable def potential (C D : Set (Set S)) (T : Expr S) : Nat :=
  if h : ∃ n s, S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)
  then PlainObservations.potential P C D (Ω.context h.choose) (T.rename (Expr.reverseIndex h.choose))
  else 1

theorem potential_at (C D : Set (Set S)) {n : Nat} {T : Expr S} {s : S}
    (ht : S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)) :
    Ω.potential C D T =
      PlainObservations.potential P C D (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  have h : ∃ m t, S_wpc_barendregt_geuvers_klop.HasType P (Ω.context m) (T.rename (Expr.reverseIndex m)) (.sort t) :=
    ⟨n, s, ht⟩
  rw [potential, dif_pos h]
  obtain ⟨t, hT⟩ := h.choose_spec
  exact (Ω.potential_at_mono hw C D hT (le_max_left h.choose n)).symm.trans
    (Ω.potential_at_mono hw C D ht (le_max_right h.choose n))

/-- Formation data for a global legal frame, retaining the open codomain
profile instead of imposing functionality. -/
theorem frame_profiles {A B q : Expr S} {s : S}
    (hT : Ω.HasType (.pi A B) (.sort s)) (hq : Ω.HasType q A) :
    ∃ J, ProfileTriple P (Ω.profile A) J (Ω.profile (.pi A B)) ∧
      PositivePath (PrimaryEdge P) (Ω.profile (B.instantiate q)) J := by
  obtain ⟨n, hT, hq⟩ := hT.common hq
  change S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n)
    (.pi (A.rename (Expr.reverseIndex n)) (B.rename (Expr.liftRen (Expr.reverseIndex n)))) (.sort s) at hT
  obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
  have hQ := hB.instantiate hq
  rw [Expr.instantiate_rename] at hQ
  have htr := Profile.triple hw hT
  have hp := Profile.growth_path hw hB hq.valid _ (TypedSubstitution.single hq)
  change PositivePath (PrimaryEdge P)
    (Profile P (Ω.context n) ((B.rename (Expr.liftRen (Expr.reverseIndex n))).instantiate
      (q.rename (Expr.reverseIndex n)))) _ at hp
  rw [Expr.instantiate_rename] at hp
  refine ⟨Profile P (A.rename (Expr.reverseIndex n) :: Ω.context n)
    (B.rename (Expr.liftRen (Expr.reverseIndex n))), ?_, ?_⟩
  · rw [Ω.profile_at hw hA, Ω.profile_at hw (T := .pi A B) hT]
    exact htr
  · rw [Ω.profile_at hw hQ]
    exact hp

omit hw in
theorem domain_sorted {A B : Expr S} {s : S}
    (hT : Ω.HasType (.pi A B) (.sort s)) : ∃ a, Ω.HasType A (.sort a) := by
  obtain ⟨n, hT⟩ := hT
  obtain ⟨a, b, c, hA, _, _, _⟩ := hT.generation_pi
  exact ⟨a, n, hA⟩

omit hw in
theorem frame_target_sorted {A B q : Expr S} {s : S}
    (hT : Ω.HasType (.pi A B) (.sort s)) (hq : Ω.HasType q A) :
    ∃ b, Ω.HasType (B.instantiate q) (.sort b) := by
  obtain ⟨n, hT, hq⟩ := hT.common hq
  obtain ⟨a, b, c, _, hB, _, _⟩ := hT.generation_pi
  refine ⟨b, n, ?_⟩
  have h := hB.instantiate hq
  change S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n)
    ((B.rename (Expr.liftRen (Expr.reverseIndex n))).instantiate (q.rename (Expr.reverseIndex n)))
    (.sort b) at h
  rw [Expr.instantiate_rename] at h
  exact h

/-- Global form of the source strict target-potential inequality. -/
theorem frame_target_drop {C D : Set (Set S)}
    (hno : ¬ ForbiddenConfiguration P C)
    (hD : IsComponent (SecondaryEdge P C) D) (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hneg : ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true)
    {A B q : Expr S} {s : S} (hT : Ω.HasType (.pi A B) (.sort s))
    (hN : Normal (.pi A B)) (hq : Ω.HasType q A)
    (hK : Ω.profile (.pi A B) ∈ D) (hL : Ω.profile (B.instantiate q) ∈ D) :
    Ω.potential C D (B.instantiate q).normalForm < Ω.potential C D (.pi A B) := by
  obtain ⟨n, hT, hq⟩ := hT.common hq
  change S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n)
    (.pi (A.rename (Expr.reverseIndex n)) (B.rename (Expr.liftRen (Expr.reverseIndex n)))) (.sort s) at hT
  obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
  have hQ := hB.instantiate hq
  rw [Expr.instantiate_rename] at hQ
  have wQ : WeaklyNormalizing (B.instantiate q) :=
    (show Ω.HasType (B.instantiate q) (.sort b) from ⟨n, hQ⟩).weaklyNormalizing hw
  have hQN := hQ.normalForm hw
  rw [Expr.normalForm_rename wQ] at hQN
  rw [Ω.potential_at hw C D hQN, Ω.potential_at hw C D (T := .pi A B) hT,
    ← Expr.normalForm_rename wQ, ← Expr.instantiate_rename]
  rw [Ω.profile_at hw (T := .pi A B) hT] at hK
  rw [Ω.profile_at hw hQ, ← Expr.instantiate_rename] at hL
  have hh := PlainObservations.frame_potential_drop hw hno hD hplain hneg hT
    (hN.rename _) hq hK hL
  exact lt_of_le_of_lt hh.1 hh.2

/-- Every active same-component domain is counted, even when a frame exits
its component. This is why the potential's guard is activity, not membership
of the open codomain in the component. -/
theorem frame_domain_drop {C D : Set (Set S)}
    {A B q : Expr S} {s : S} (hT : Ω.HasType (.pi A B) (.sort s)) (hq : Ω.HasType q A)
    (hK : ActiveLayer P C (Ω.profile (.pi A B)))
    (hL : ActiveLayer P C (Ω.profile (B.instantiate q)))
    (hI : Ω.profile A ∈ D) :
    Ω.potential C D A < Ω.potential C D (.pi A B) := by
  obtain ⟨n, hT, hq⟩ := hT.common hq
  change S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n)
    (.pi (A.rename (Expr.reverseIndex n)) (B.rename (Expr.liftRen (Expr.reverseIndex n)))) (.sort s) at hT
  obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
  have hQ := hB.instantiate hq
  rw [Expr.instantiate_rename] at hQ
  have hp := Profile.growth_path hw hB hq.valid _ (TypedSubstitution.single hq)
  change PositivePath (PrimaryEdge P)
    (Profile P (Ω.context n) ((B.rename (Expr.liftRen (Expr.reverseIndex n))).instantiate
      (q.rename (Expr.reverseIndex n)))) _ at hp
  rw [Expr.instantiate_rename, ← Ω.profile_at hw hQ] at hp
  have hJH := ObservationLayers.positive hL.layer hp
  have hJ := hK.predecessor (Reach.single (SecondaryEdge.positive hJH hK.layer
    (by rw [Ω.profile_at hw (T := .pi A B) hT]; exact .codomain (Profile.triple hw hT))))
  have hc : Profile P (Ω.context n) (A.rename (Expr.reverseIndex n)) ∈ D ∧
      ActiveLayer P C (Profile P (A.rename (Expr.reverseIndex n) :: Ω.context n)
        (B.rename (Expr.liftRen (Expr.reverseIndex n)))) := by
    exact ⟨Ω.profile_at hw hA ▸ hI, hJ⟩
  rw [Ω.potential_at hw C D hA, Ω.potential_at hw C D (T := .pi A B) hT]
  simp only [Expr.rename, PlainObservations.potential, if_pos hc]
  omega

end

variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

/-- Substitution of a typed normal generic expression can only grow its exact
profile. The common-stage reduction keeps nonfunctional sort choices. -/
theorem profile_subst_growth (hw : SystemWeaklyNormalizing P) {Γ : List (Expr S)}
    {T : Expr S} {s : S} {σ : Nat → Expr S} (ht : S_wpc_barendregt_geuvers_klop.HasType P Γ T (.sort s))
    (hσ : Ω.TypedSubstitution Γ σ) : Profile P Γ T ⊆ Ω.profile (T.subst σ) := by
  obtain ⟨k, hk⟩ := TypedSubstitution.common_stage hσ
  let σ' := fun n => (σ n).rename (Expr.reverseIndex k)
  have hs : S_wpc_barendregt_geuvers_klop.TypedSubstitution P Γ (Ω.context k) σ' := by
    intro n A hn
    simpa only [σ', ← Expr.rename_subst] using hk n A hn
  have hT := ht.subst (Ω.valid k) σ' hs
  have hp := Profile.growth hw (ht.weaklyNormalizing hw) (Ω.valid k) σ' hs
  have he : T.subst σ' = (T.subst σ).rename (Expr.reverseIndex k) := (Expr.rename_subst _ _ _).symm
  rw [he] at hT hp
  rwa [Ω.profile_at hw hT]

end ContextTower
end S_wpc_barendregt_geuvers_klop

end OMA




namespace OMA

/-! The exact local obligations used when advancing a primary component.
This is an internal interface, not a hypothesis of the main PTS theorem. -/
namespace S_wpc_barendregt_geuvers_klop
universe u v

/-- Expected types include unsorted literal sorts (the regularity alternative). -/
def Expected {S : Type u} (P : Specification S) (Γ : List (Expr S)) (A : Expr S) : Prop :=
  (∃ s, A = .sort s) ∨ ∃ s, HasType P Γ A (.sort s)
namespace Expected
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {A D : Expr S}
theorem of_type {M : Expr S} (h : HasType P Γ M A) : Expected P Γ A := h.regularity
theorem sorted {s : S} (h : HasType P Γ A (.sort s)) : Expected P Γ A := .inr ⟨s,h⟩
theorem wn (hw : SystemWeaklyNormalizing P) (h : Expected P Γ A) : WeaklyNormalizing A := by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact ⟨_,.refl,Normal.sort s⟩
  · exact h.weaklyNormalizing hw
theorem weaken {s : S} (h : Expected P Γ A) (hD : HasType P Γ D (.sort s)) :
    Expected P (D :: Γ) (A.rename Nat.succ) := by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact .inl ⟨s,rfl⟩
  · exact .inr ⟨s,.weaken h hD⟩
end Expected

namespace Expr
variable {S : Type u}
def extend (σ : Nat → Expr S) (n : Expr S) : Nat → Expr S
  | 0 => n
  | i+1 => σ i
@[simp] theorem extend_zero (σ : Nat → Expr S) (n : Expr S) : extend σ n 0 = n := rfl
@[simp] theorem extend_succ (σ : Nat → Expr S) (n : Expr S) (i : Nat) : extend σ n (i+1) = σ i := rfl
@[simp] theorem subst_raise_extend (M n : Expr S) (σ : Nat → Expr S) :
    (M.rename Nat.succ).subst (extend σ n) = M.subst σ := by
  rw [subst_rename]; rfl
@[simp] theorem instantiate_extended (M n : Expr S) (σ : Nat → Expr S) :
    (M.subst (liftSub σ)).instantiate n = M.subst (extend σ n) := by
  rw [instantiate,subst_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => exact subst_lift_single (σ i) n
end Expr

/-- Ground=top has already been proved on U; U is predecessor closed and
contains every strict predecessor of the component currently processed. -/
structure Processed {S : Type u} {P : Specification S} (Ω : ContextTower P)
    (U C : Set (Set S)) : Prop where
  disjoint : Disjoint U C
  closed : ∀ {I J}, J ∈ U → Reach (PrimaryEdge P) I J → I ∈ U
  before : ∀ {I J}, J ∈ C → Reach (PrimaryEdge P) I J → I ∈ U ∨ I ∈ C
  invariant : ∀ {T}, Candidates.ActualType Ω T → Ω.profile T ∈ U →
    Candidates.Ground Ω T = Candidates.Top Ω T

/-- Environments carry arbitrary typed raw images. Extension collections are
nonempty, and retain old parameters. Product tests range over all listed
extensions; specialization can select the normal argument's tested payload. -/
structure ComponentInterface {S : Type u} {P : Specification S} (Ω : ContextTower P)
    (hw : SystemWeaklyNormalizing P) (C : Set (Set S)) where
  Env : List (Expr S) → Type v
  images : {Γ : List (Expr S)} → Env Γ → Nat → Expr S
  typed : ∀ {Γ} (e : Env Γ), Ω.TypedSubstitution Γ (images e)
  inhabit : ∀ {Γ} (σ : Nat → Expr S), Ω.TypedSubstitution Γ σ →
    ∃ e : Env Γ, images e = σ
  Ext : {Γ : List (Expr S)} → {D : Expr S} → Env Γ → Env (D :: Γ) → Expr S → Prop
  ext_images : ∀ {Γ D} {e : Env Γ} {e' : Env (D :: Γ)} {n}, Ext e e' n →
    images e' = Expr.extend (images e) n
  extend : ∀ {Γ D s} (e : Env Γ), HasType P Γ D (.sort s) → ∀ n,
    Ω.HasType n (D.subst (images e)) → ∃ e' : Env (D :: Γ), Ext e e' n
  R : {Γ : List (Expr S)} → Expr S → Env Γ → Set (Expr S)
  candidate : ∀ {Γ A} (e : Env Γ), Expected P Γ A →
    Candidates.IsCandidate Ω (A.subst (images e)).normalForm (R A e)
  conversion : ∀ {Γ A B} (e : Env Γ), Expected P Γ A → Expected P Γ B →
    Converts A B → R A e = R B e
  outside : ∀ {Γ A} (e : Env Γ), Expected P Γ A →
    (Profile P Γ A ∉ C ∨ Ω.profile (A.subst (images e)) ∉ C) →
    R A e = Candidates.Top Ω (A.subst (images e)).normalForm
  weakening : ∀ {Γ D A s} {e : Env Γ} {e' : Env (D :: Γ)} {n},
    HasType P Γ D (.sort s) → Expected P Γ A → Ext e e' n →
    R (A.rename Nat.succ) e' = R A e
  product_intro : ∀ {Γ D E s} (e : Env Γ), HasType P Γ (.pi D E) (.sort s) →
    Profile P Γ (.pi D E) ∈ C → Ω.profile ((Expr.pi D E).subst (images e)) ∈ C →
    ∀ h, h ∈ Candidates.Top Ω ((Expr.pi D E).subst (images e)).normalForm →
    (∀ n, n ∈ R D e → ∀ e' : Env (D :: Γ), Ext e e' n → Expr.app h n ∈ R E e') →
    h ∈ R (.pi D E) e
  specialization : ∀ {Γ D E s N} (e : Env Γ), HasType P Γ (.pi D E) (.sort s) →
    HasType P Γ N D → Profile P Γ (.pi D E) ∈ C →
    Ω.profile ((Expr.pi D E).subst (images e)) ∈ C →
    ∀ h, h ∈ R (.pi D E) e → N.subst (images e) ∈ R D e →
    Expr.app h (N.subst (images e)) ∈ R (E.instantiate N) e

namespace ComponentInterface
open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

def Admissible {Γ : List (Expr S)} (e : J.Env Γ) : Prop :=
  ∀ i B, Lookup Γ i B →
    (Profile P Γ B ∈ C → J.images e i ∈ J.R B e) ∧
    (Profile P Γ B ∈ U → StronglyNormalizing (J.images e i)) ∧
    (Profile P Γ B ∉ U → Profile P Γ B ∉ C →
      J.images e i ∈ Ground Ω (B.subst (J.images e)).normalForm)

theorem admissible_extension {Γ : List (Expr S)} {D : Expr S} {s : S}
    {e : J.Env Γ} {e' : J.Env (D :: Γ)} {n : Expr S}
    (hD : HasType P Γ D (.sort s)) (he : J.Ext e e' n)
    (ha : J.Admissible (U := U) e)
    (hnC : Profile P Γ D ∈ C → n ∈ J.R D e)
    (hnU : Profile P Γ D ∈ U → StronglyNormalizing n)
    (hnG : Profile P Γ D ∉ U → Profile P Γ D ∉ C → n ∈ Ground Ω (D.subst (J.images e)).normalForm) :
    J.Admissible (U := U) e' := by
  intro i B hi
  cases hi with
  | zero =>
    have hp := Profile.weaken hw hD hD
    rw [hp,J.weakening hD (.sorted hD) he]
    simpa only [J.ext_images he,Expr.extend_zero,Expr.subst_raise_extend] using ⟨hnC,hnU,hnG⟩
  | succ D hi =>
    obtain ⟨t,hB⟩ := HasType.lookup_sorted hD.valid hi
    rw [Profile.weaken hw hB hD,J.weakening hD (.sorted hB) he]
    simpa only [J.ext_images he,Expr.extend_succ,Expr.subst_raise_extend] using ha _ _ hi

/-- Sending a binder to a fresh typed variable always preserves admissibility.
SN of that instance reflects back to the open substituted body by substitution
reflection, so no global renaming or reduction-height bound is needed. -/
theorem fresh_extension {Γ : List (Expr S)} {D : Expr S} {s : S}
    (e : J.Env Γ) (hD : HasType P Γ D (.sort s)) (ha : J.Admissible (U := U) e) :
    ∃ n, ∃ e' : J.Env (D :: Γ), J.Ext e e' (.var n) ∧ J.Admissible (U := U) e' := by
  have ht := ContextTower.HasType.subst hD (J.typed e)
  obtain ⟨n,_,hn⟩ := Ω.fresh_variable ht 0
  obtain ⟨e',he⟩ := J.extend e hD (.var n) hn
  have hng := var_ground n (hn.normalize_type hw)
  exact ⟨n,e',he,J.admissible_extension hD he ha
    (fun _ => (J.candidate e (.sorted hD)).lower hng)
    (fun _ => (Normal.var n).stronglyNormalizing) (fun _ _ => hng)⟩

end ComponentInterface

namespace Expected
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {Γ : List (Expr S)} {A : Expr S} {σ : Nat → Expr S}
theorem subst_wn (h : Expected P Γ A) (hw : SystemWeaklyNormalizing P)
    (hσ : Ω.TypedSubstitution Γ σ) : WeaklyNormalizing (A.subst σ) := by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact ⟨_,.refl,Normal.sort s⟩
  · exact (ContextTower.HasType.subst h hσ).weaklyNormalizing hw

theorem actual (h : Expected P Γ A) (hw : SystemWeaklyNormalizing P)
    (hσ : Ω.TypedSubstitution Γ σ) : Candidates.ActualType Ω (A.subst σ).normalForm := by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact .inr ⟨s,Expr.normalForm_of_normal (Normal.sort s)⟩
  · have ht := ContextTower.HasType.subst h hσ
    exact .inl ⟨(Expr.normalForm_spec (ht.weaklyNormalizing hw)).2, s, ht.normalForm hw⟩
end Expected

namespace ContextTower
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
variable (hw : SystemWeaklyNormalizing P)
include hw
theorem profile_subst_path {Γ : List (Expr S)} {T : Expr S} {s : S} {σ : Nat → Expr S}
    (ht : S_wpc_barendregt_geuvers_klop.HasType P Γ T (.sort s)) (hσ : Ω.TypedSubstitution Γ σ) :
    PositivePath (PrimaryEdge P) (Ω.profile (T.subst σ)) (Profile P Γ T) :=
  Profile.inclusion_path (Ω.profile_feasible hw (HasType.subst ht hσ))
    (Profile.feasible (ht.weaklyNormalizing hw) (Profile.nonempty_of_sorted hw ht))
    (Ω.profile_subst_growth hw ht hσ)

theorem profile_instantiate_product_path {D E n : Expr S} {s : S}
    (hp : Ω.HasType (.pi D E) (.sort s)) (hn : Ω.HasType n D) :
    PositivePath (PrimaryEdge P) (Ω.profile (E.instantiate n)) (Ω.profile (.pi D E)) := by
  obtain ⟨k,hp,hn⟩ := hp.common hn
  obtain ⟨a,b,c,_,hE,_,_⟩ := hp.generation_pi
  have hEn := hE.instantiate hn
  change S_wpc_barendregt_geuvers_klop.HasType P (Ω.context k)
    ((E.rename (Expr.liftRen (Expr.reverseIndex k))).instantiate (n.rename (Expr.reverseIndex k))) (.sort b) at hEn
  rw [Expr.instantiate_rename] at hEn
  rw [Ω.profile_at hw hEn,Ω.profile_at hw hp]
  simpa only [Expr.rename,Expr.instantiate_rename] using Profile.instantiate_product_path hw hp hn
end ContextTower

namespace Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable (hw : SystemWeaklyNormalizing P)
include hw
/-- G propagates through the normal form of a raw dependent product. -/
theorem ground_application_subst {Γ : List (Expr S)} {D E n h : Expr S} {s : S}
    {σ : Nat → Expr S} (hp : HasType P Γ (.pi D E) (.sort s))
    (hσ : Ω.TypedSubstitution Γ σ)
    (hh : h ∈ Ground Ω ((Expr.pi D E).subst σ).normalForm)
    (hn : n ∈ Top Ω (D.subst σ).normalForm) :
    Expr.app h n ∈ Ground Ω (E.subst (Expr.extend σ n)).normalForm := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hraw := ContextTower.HasType.subst hp hσ
  have hwraw := hraw.weaklyNormalizing hw
  change WeaklyNormalizing (.pi (D.subst σ) (E.subst (Expr.liftSub σ))) at hwraw
  have hrawD := ContextTower.HasType.subst hD hσ
  have hnr : Ω.HasType n (D.subst σ) := hn.1.conversion hrawD
    (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
  have hparts : WeaklyNormalizing (D.subst σ) ∧
      WeaklyNormalizing (E.subst (Expr.liftSub σ)) := by
    obtain ⟨normal, reduction, hnormal⟩ := hwraw
    obtain ⟨domain, body, rfl, hdomain, hbody⟩ := Reduces.pi_inv reduction
    exact ⟨⟨domain, hdomain, hnormal.pi_domain⟩, ⟨body, hbody, hnormal.pi_body⟩⟩
  have htarget : Ω.HasType (E.subst (Expr.extend σ n)) (.sort b) :=
    ContextTower.HasType.subst hE (hσ.cons hnr)
  have hnf : ((Expr.pi D E).subst σ).normalForm =
      .pi (D.subst σ).normalForm (E.subst (Expr.liftSub σ)).normalForm :=
    Expr.normalForm_pi hparts.1 hparts.2
  rw [hnf] at hh
  have hout := ground_application hw hh hn
  have hpN := hraw.normalForm hw
  rw [hnf] at hpN
  obtain ⟨t,ht⟩ := Ω.frame_target_sorted hpN hn.1
  have hr : Reduces (E.subst (Expr.extend σ n))
      ((E.subst (Expr.liftSub σ)).normalForm.instantiate n) := by
    rw [← Expr.instantiate_extended]
    exact (Expr.normalForm_spec hparts.2).1.subst (Expr.single n)
  have he := Expr.normalForm_converts (htarget.weaklyNormalizing hw)
    (ht.weaklyNormalizing hw) hr.converts
  rwa [he]
end Candidates

namespace Processed
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {U C : Set (Set S)} (H : Processed Ω U C) (hw : SystemWeaklyNormalizing P)
variable {Γ : List (Expr S)} {T : Expr S} {s : S} {σ : Nat → Expr S}
include H hw
theorem subst_closed (ht : HasType P Γ T (.sort s)) (hσ : Ω.TypedSubstitution Γ σ)
    (hT : Profile P Γ T ∈ U) : Ω.profile (T.subst σ) ∈ U :=
  H.closed hT (Ω.profile_subst_path hw ht hσ).reach

theorem subst_before (ht : HasType P Γ T (.sort s)) (hσ : Ω.TypedSubstitution Γ σ)
    (hT : Profile P Γ T ∈ C) : Ω.profile (T.subst σ) ∈ U ∨ Ω.profile (T.subst σ) ∈ C :=
  H.before hT (Ω.profile_subst_path hw ht hσ).reach

theorem top_ground_generic {e : Expr S}
    (ht : HasType P Γ T (.sort s)) (hσ : Ω.TypedSubstitution Γ σ)
    (hT : Profile P Γ T ∈ U) (he : e ∈ Candidates.Top Ω (T.subst σ).normalForm) :
    e ∈ Candidates.Ground Ω (T.subst σ).normalForm := by
  rw [H.invariant ((Expected.sorted ht).actual hw hσ) (by
    rw [Ω.profile_normalForm]
    exact H.subst_closed hw ht hσ hT)]
  exact he
end Processed

namespace ComponentInterface
open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

/-- The extra neutral invariant is exactly the G-prefix invariant in the
manuscript's spine argument. -/
def Transported {Γ : List (Expr S)} (M A : Expr S) (e : J.Env Γ) : Prop :=
  M.subst (J.images e) ∈ J.R A e ∧
    (Neutral M → Profile P Γ A ∉ C →
      M.subst (J.images e) ∈ Ground Ω (A.subst (J.images e)).normalForm)

namespace Transported
variable {J} {Γ : List (Expr S)} {M A B : Expr S} {e : J.Env Γ}
theorem sn (h : J.Transported M A e) (hA : Expected P Γ A) :
    StronglyNormalizing (M.subst (J.images e)) := (J.candidate e hA).upper h.1 |>.2

theorem convert (h : J.Transported M A e) (hA : Expected P Γ A)
    (hB : Expected P Γ B) (hc : Converts A B) : J.Transported M B e := by
  have hp := Profile.converts (P := P) (Γ := Γ) (hA.wn hw) (hB.wn hw) hc
  have he := Expr.normalForm_converts (hA.subst_wn hw (J.typed e))
    (hB.subst_wn hw (J.typed e)) (hc.subst (J.images e))
  refine ⟨?_,?_⟩
  · rw [← J.conversion e hA hB hc]; exact h.1
  · intro hn hout
    rw [← he]
    exact h.2 hn (hp ▸ hout)
end Transported

theorem transported_of_ground {Γ : List (Expr S)} {M A : Expr S} {e : J.Env Γ}
    (hA : Expected P Γ A) (hg : M.subst (J.images e) ∈ Ground Ω (A.subst (J.images e)).normalForm) :
    J.Transported M A e := ⟨(J.candidate e hA).lower hg,fun _ _ => hg⟩

theorem transported_at_sort {Γ : List (Expr S)} {M : Expr S} {e : J.Env Γ} {s : S}
    (ht : HasType P Γ M (.sort s)) (hs : StronglyNormalizing (M.subst (J.images e))) :
    J.Transported M (.sort s) e := by
  apply J.transported_of_ground (.inl ⟨s,rfl⟩)
  have hh : M.subst (J.images e) ∈ Top Ω (.sort s) :=
    ⟨ContextTower.HasType.subst ht (J.typed e),hs⟩
  simpa only [Expr.subst,Expr.normalForm_of_normal (Normal.sort s),sort_ground_eq_top] using hh

variable (H : Processed Ω U C)
include H

theorem transported_var {Γ : List (Expr S)} {A : Expr S} {i : Nat}
    (ht : HasType P Γ (.var i) A) (e : J.Env Γ) (ha : J.Admissible (U := U) e) :
    J.Transported (.var i) A e := by
  obtain ⟨B,hB,hc⟩ := ht.generation
  obtain ⟨s,hBs⟩ := HasType.lookup_sorted ht.valid hB
  have hea := Expected.of_type ht
  apply Transported.convert (A := B) (hA := .sorted hBs) (hB := hea) (hc := .symm _ _ hc)
  have hdr := ha i B hB
  by_cases hBU : Profile P Γ B ∈ U
  · apply J.transported_of_ground (.sorted hBs)
    exact H.top_ground_generic hw hBs (J.typed e) hBU
      ⟨(J.typed e i B hB).normalize_type hw,hdr.2.1 hBU⟩
  · by_cases hBC : Profile P Γ B ∈ C
    · exact ⟨hdr.1 hBC,fun _ hn => False.elim (hn hBC)⟩
    · exact J.transported_of_ground (.sorted hBs) (hdr.2.2 hBU hBC)

/-- Propagation for a neutral prefix. Unlike a candidate, G has application
closure; the processed invariant handles the sole transition out of C. -/
theorem transported_neutral_app {Γ : List (Expr S)} {f n D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (hn : HasType P Γ n D)
    (hf : Neutral f) (e : J.Env Γ)
    (hfr : J.Transported f (.pi D E) e) (hnr : J.Transported n D e) :
    J.Transported (.app f n) (E.instantiate n) e := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hExpected := Expected.sorted (hE.instantiate hn)
  have hnt := (J.candidate e (.sorted hD)).upper hnr.1
  have hg (hfg : f.subst (J.images e) ∈ Ground Ω ((Expr.pi D E).subst (J.images e)).normalForm) :
      J.Transported (.app f n) (E.instantiate n) e := by
    apply J.transported_of_ground hExpected
    rw [← Expr.instantiate_subst,Expr.instantiate_extended]
    exact ground_application_subst hw hp (J.typed e) hfg hnt
  by_cases hK : Profile P Γ (.pi D E) ∈ C
  · by_cases hKa : Ω.profile ((Expr.pi D E).subst (J.images e)) ∈ C
    · have hr := J.specialization e hp hn hK hKa _ hfr.1 hnr.1
      refine ⟨hr,?_⟩
      intro _ ho
      have hL := H.before hK (Profile.instantiate_product_path hw hp hn).reach
      rcases hL with hLU | hLC
      · exact H.top_ground_generic hw (hE.instantiate hn) (J.typed e) hLU
          ((J.candidate e hExpected).upper hr)
      · exact False.elim (ho hLC)
    · apply hg
      have haK := (H.subst_before hw hp (J.typed e) hK).resolve_right hKa
      rw [H.invariant ((Expected.sorted hp).actual hw (J.typed e)) (by
        rwa [Ω.profile_normalForm])]
      exact (J.candidate e (.sorted hp)).upper hfr.1
  · exact hg (hfr.2 hf hK)

end ComponentInterface
end S_wpc_barendregt_geuvers_klop

namespace S_wpc_barendregt_geuvers_klop.Candidates
universe u
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable (hw : SystemWeaklyNormalizing P)
include hw

theorem application_subst_type {Γ : List (Expr S)} {D E n h : Expr S} {s : S}
    {σ : Nat → Expr S} (hp : HasType P Γ (.pi D E) (.sort s))
    (hσ : Ω.TypedSubstitution Γ σ)
    (hh : Ω.HasType h ((Expr.pi D E).subst σ).normalForm)
    (hn : Ω.HasType n (D.subst σ).normalForm) :
    Ω.HasType (.app h n) (E.subst (Expr.extend σ n)).normalForm := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hraw := ContextTower.HasType.subst hp hσ
  have hrawD := ContextTower.HasType.subst hD hσ
  have hhr := hh.conversion hraw
    (.symm _ _ (Expr.normalForm_spec (hraw.weaklyNormalizing hw)).1.converts)
  have hnr := hn.conversion hrawD
    (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
  have hout := (hhr.application hnr).normalize_type hw
  simpa only [Expr.instantiate_extended] using hout

def RawProduct (Ω : ContextTower P) (D E : Expr S) (σ : Nat → Expr S)
    (X : Set (Expr S)) (Y : Expr S → Bool → Set (Expr S)) : Set (Expr S) :=
  {h | h ∈ Top Ω ((Expr.pi D E).subst σ).normalForm ∧
    ∀ n ∈ X, ∀ b, Expr.app h n ∈ Y n b}

theorem rawProduct_candidate {Γ : List (Expr S)} {D E : Expr S} {s : S}
    {σ : Nat → Expr S} {X : Set (Expr S)} {Y : Expr S → Bool → Set (Expr S)}
    (hp : HasType P Γ (.pi D E) (.sort s)) (hσ : Ω.TypedSubstitution Γ σ)
    (hX : IsCandidate Ω (D.subst σ).normalForm X)
    (hY : ∀ n ∈ X, ∀ b, IsCandidate Ω (E.subst (Expr.extend σ n)).normalForm (Y n b)) :
    IsCandidate Ω ((Expr.pi D E).subst σ).normalForm (RawProduct Ω D E σ X Y) where
  lower := by
    intro h hh
    refine ⟨ground_le_top hh,?_⟩
    intro n hn b
    exact (hY n hn b).lower (ground_application_subst hw hp hσ hh (hX.upper hn))
  upper := fun _ hh => hh.1
  expansion := by
    intro D' m a ns ht hD hm ha hns hc
    refine ⟨⟨ht,StronglyNormalizing.head_expansion hD hm ha hns hc.1.2⟩,?_⟩
    intro n hn b
    have ht' := application_subst_type hw hp hσ ht (hX.upper hn).1
    have hsn : StronglyNormalizingArgs (ns ++ [n]) := by
      apply StronglyNormalizingArgs.of_forall
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hns.of_mem hx
      · exact (List.mem_singleton.mp hx).symm ▸ (hX.upper hn).2
    have hc' := hc.2 n hn b
    have ht'' : Ω.HasType ((Expr.app (.lam D' m) a).apps (ns ++ [n]))
        (E.subst (Expr.extend σ n)).normalForm := by
      simpa only [Expr.apps_append,Expr.apps] using ht'
    have hc'' : (m.instantiate a).apps (ns ++ [n]) ∈ Y n b := by
      simpa only [Expr.apps_append,Expr.apps] using hc'
    simpa only [Expr.apps_append,Expr.apps] using
      (hY n hn b).expansion D' m a (ns ++ [n]) ht'' hD hm ha hsn hc'' 
end S_wpc_barendregt_geuvers_klop.Candidates

end OMA



namespace OMA

namespace S_wpc_barendregt_geuvers_klop

section
universe u v
namespace Neutral
variable {S : Type u} {M : Expr S} {ns : List (Expr S)}
theorem apps_head (h : Neutral (M.apps ns)) : Neutral M := by
  induction ns generalizing M with
  | nil => exact h
  | cons n ns ih =>
    have hh := ih h
    cases hh with
    | app hh => exact hh
end Neutral

namespace ComponentInterface
open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

def Transports (M : Expr S) : Prop :=
  ∀ (Γ : List (Expr S)) A, HasType P Γ M A →
    ∀ e : J.Env Γ, J.Admissible (U := U) e → J.Transported M A e

/-- Reflection of the fresh-variable instance proves SN of the open body. -/
theorem open_sn {Γ : List (Expr S)} {D b B : Expr S} {s : S}
    (hb : HasType P (D :: Γ) b B) (hD : HasType P Γ D (.sort s))
    (ih : J.Transports (U := U) b) (e : J.Env Γ) (ha : J.Admissible (U := U) e) :
    StronglyNormalizing (b.subst (Expr.liftSub (J.images e))) := by
  obtain ⟨z,e',he',ha'⟩ := J.fresh_extension e hD ha
  have hsn := (ih _ _ hb e' ha').sn (.of_type hb)
  rw [J.ext_images he',← Expr.instantiate_extended] at hsn
  exact StronglyNormalizing.of_subst (Expr.single (.var z)) hsn

variable (H : Processed Ω U C)
include H

theorem transports_lam {Γ : List (Expr S)} {D b B : Expr S} {s : S}
    (hb : HasType P (D :: Γ) b B) (hp : HasType P Γ (.pi D B) (.sort s))
    (ihD : J.Transports (U := U) D) (ihb : J.Transports (U := U) b)
    (e : J.Env Γ) (ha : J.Admissible (U := U) e) :
    J.Transported (.lam D b) (.pi D B) e := by
  classical
  obtain ⟨a,c,d,hD,hB,_,_⟩ := hp.generation_pi
  have hDs := (ihD _ _ hD e ha).sn (.of_type hD)
  have hbs := J.open_sn hb hD ihb e ha
  have htop : (Expr.lam D b).subst (J.images e) ∈ Top Ω ((Expr.pi D B).subst (J.images e)).normalForm :=
    ⟨(ContextTower.HasType.subst (.abstraction hb hp) (J.typed e)).normalize_type hw,hDs.lam hbs⟩
  refine ⟨?_,fun hn => by cases hn⟩
  by_cases hK : Profile P Γ (.pi D B) ∈ C
  · by_cases hKa : Ω.profile ((Expr.pi D B).subst (J.images e)) ∈ C
    · apply J.product_intro e hp hK hKa _ htop
      intro n hn e' he
      have hnt := (J.candidate e (.sorted hD)).upper hn
      have hDomain := ContextTower.HasType.subst hD (J.typed e)
      have hnr := hnt.1.conversion hDomain
        (.symm _ _ (Expr.normalForm_spec (hDomain.weaklyNormalizing hw)).1.converts)
      have hdBefore := H.before hK (Reach.single (.domain (Profile.triple hw hp)))
      have hadm : J.Admissible (U := U) e' := J.admissible_extension hD he ha
        (fun _ => hn) (fun _ => hnt.2) (fun hnu hnc => by
          rcases hdBefore with hu | hc
          · exact False.elim (hnu hu)
          · exact False.elim (hnc hc))
      have hbody := (ihb _ _ hb e' hadm).1
      have htapp := ((ContextTower.HasType.subst (.abstraction hb hp) (J.typed e)).application hnr).normalize_type hw
      change Ω.HasType (.app (.lam (D.subst (J.images e)) (b.subst (Expr.liftSub (J.images e)))) n)
        ((B.subst (Expr.liftSub (J.images e))).instantiate n).normalForm at htapp
      rw [Expr.instantiate_extended,← J.ext_images he] at htapp
      have hbmem : (b.subst (Expr.liftSub (J.images e))).instantiate n ∈ J.R B e' := by
        rwa [Expr.instantiate_extended,← J.ext_images he]
      exact (J.candidate e' (.of_type hb)).expansion _ _ _ [] htapp hDs hbs hnt.2 .nil hbmem
    · rw [J.outside e (.sorted hp) (.inr hKa)]; exact htop
  · rw [J.outside e (.sorted hp) (.inl hK)]; exact htop

/-- Strongly-normalizing substitution transport,
including a neutral G-prefix invariant. -/
theorem sn_fundamental {M : Expr S} (hs : StronglyNormalizing M) :
    J.Transports (U := U) M := by
  apply StronglyNormalizing.induction_descendants (Q := J.Transports (U := U)) _ hs
  intro M _ ihr ihp Γ A ht e ha
  cases M with
  | var i => exact J.transported_var H ht e ha
  | sort s =>
    obtain ⟨t,hat,hc⟩ := ht.generation
    have hst := HasType.sort_of_valid ht.valid hat
    exact (J.transported_at_sort hst (Normal.sort s).stronglyNormalizing).convert
      (.inl ⟨t,rfl⟩) (.of_type ht) (.symm _ _ hc)
  | pi D E =>
    obtain ⟨a,b,c,hD,hE,hr,hc⟩ := ht.generation_pi
    have hDs := (ihp D (Expr.ProperPart.child (.pi_domain D E)) _ _ hD e ha).sn (.of_type hD)
    have hEs := J.open_sn hE hD (ihp E (Expr.ProperPart.child (.pi_body D E))) e ha
    exact (J.transported_at_sort (.product hD hE hr) (hDs.pi hEs)).convert
      (.inl ⟨c,rfl⟩) (.of_type ht) (.symm _ _ hc)
  | lam D b =>
    obtain ⟨B,s,hb,hp,hc⟩ := ht.generation_lam
    exact (J.transports_lam H hb hp
      (ihp D (Expr.ProperPart.child (.lam_domain D b)))
      (ihp b (Expr.ProperPart.child (.lam_body D b))) e ha).convert
      (.sorted hp) (.of_type ht) (.symm _ _ hc)
  | app f n =>
    rcases ht.app_spine with hf | ⟨D,b,n',ns,he⟩
    · obtain ⟨D,E,hft,hnt,hc⟩ := ht.generation_app
      obtain ⟨s,hp⟩ := hft.product_type_sorted
      have hfr := ihp f (Expr.ProperPart.child (.app_left f n)) _ _ hft e ha
      have hnr := ihp n (Expr.ProperPart.child (.app_right f n)) _ _ hnt e ha
      exact (J.transported_neutral_app H hp hnt hf e hfr hnr).convert
        (.of_type (.application hft hnt)) (.of_type ht) (.symm _ _ hc)
    · have ht' : HasType P Γ ((Expr.app (.lam D b) n').apps ns) A := he ▸ ht
      have parts : ∀ N, Expr.ProperPart N ((Expr.app (.lam D b) n').apps ns) →
          J.Transports (U := U) N := by
        intro N hN; apply ihp N; change Expr.ProperPart N (.app f n); rwa [he]
      have hlampart : Expr.ProperPart (.lam D b) ((Expr.app (.lam D b) n').apps ns) :=
        (Expr.ProperPart.child (.app_left _ _)).trans_right (Expr.Subterm.apps_head ns)
      obtain ⟨T,hthead⟩ := ht'.apps_head
      obtain ⟨D',E',hlam,hn',_⟩ := hthead.generation_app
      obtain ⟨B,s,hb,hp,_⟩ := hlam.generation_lam
      obtain ⟨a,c,d,hD,_,_,_⟩ := hp.generation_pi
      have hDs := (parts D (Expr.ProperPart.trans_left (Expr.Subterm.of_child (.lam_domain D b)) hlampart) _ _ hD e ha).sn (.of_type hD)
      have hbs := J.open_sn hb hD (parts b (Expr.ProperPart.trans_left (Expr.Subterm.of_child (.lam_body D b)) hlampart)) e ha
      have hnp := (Expr.ProperPart.child (.app_right (.lam D b) n')).trans_right (Expr.Subterm.apps_head ns)
      have hns := (parts n' hnp _ _ hn' e ha).sn (.of_type hn')
      have hargs : StronglyNormalizingArgs (ns.map (Expr.subst (J.images e))) := by
        apply StronglyNormalizingArgs.of_forall
        intro z hz
        rcases List.mem_map.mp hz with ⟨L,hL,rfl⟩
        obtain ⟨Z,hZ⟩ := ht'.apps_arg hL
        exact (parts L (Expr.ProperPart.apps_arg hL) _ _ hZ e ha).sn (.of_type hZ)
      have hred : Beta (.app f n) ((b.instantiate n').apps ns) := by
        rw [he]; exact (Beta.head D b n').apps ns
      have hctr := (ihr _ hred _ _ (ht.subject_reduction hred) e ha).1
      have hctr' : ((b.subst (Expr.liftSub (J.images e))).instantiate (n'.subst (J.images e))).apps
          (ns.map (Expr.subst (J.images e))) ∈ J.R A e := by
        simpa only [Expr.subst_apps,Expr.instantiate_subst] using hctr
      have hty := (ContextTower.HasType.subst ht' (J.typed e)).normalize_type hw
      rw [Expr.subst_apps] at hty
      have hexp := (J.candidate e (.of_type ht)).expansion _ _ _ _ hty hDs hbs hns hargs hctr'
      constructor
      · rw [he,Expr.subst_apps]
        exact hexp
      · intro hn
        rw [he] at hn
        have hh := hn.apps_head
        cases hh with
        | app hn => cases hn
end ComponentInterface

namespace StronglyNormalizing
variable {S : Type u} {M : Expr S}
theorem reverseIndex (h : StronglyNormalizing M) (k : Nat) :
    StronglyNormalizing (M.rename (Expr.reverseIndex k)) := by
  apply of_rename (Expr.reverseIndex k)
  simpa only [Expr.reverseIndex_twice] using h
end StronglyNormalizing

namespace Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
/-- A single finite prefix supporting every exact typing of a tested stack. -/
inductive StackAt (k : Nat) : Expr S → List (Expr S) → Prop
  | nil (T) : StackAt k T []
  | cons {D E n ns} :
      HasType P (Ω.context k) (n.rename (Expr.reverseIndex k)) (D.rename (Expr.reverseIndex k)) →
      StronglyNormalizing n → StackAt k (E.instantiate n).normalForm ns →
      StackAt k (.pi D E) (n :: ns)
namespace StackAt
variable {Ω} {k j : Nat} {T : Expr S} {ns : List (Expr S)}
theorem mono (h : StackAt Ω k T ns) (hkj : k ≤ j) : StackAt Ω j T ns := by
  induction h with
  | nil T => exact .nil T
  | cons hn hsn _ ih => exact .cons (Ω.at_mono hn hkj) hsn ih

theorem tested (h : StackAt Ω k T ns) : TestedStack Ω T ns := by
  induction h with
  | nil T => exact .nil T
  | cons hn hs _ ih => exact .cons ⟨⟨k,hn⟩,hs⟩ ih
end StackAt
namespace TestedStack
variable {Ω} {T : Expr S} {ns : List (Expr S)}
theorem common_stage (h : TestedStack Ω T ns) : ∃ k, StackAt Ω k T ns := by
  induction h with
  | nil T => exact ⟨0,.nil T⟩
  | cons hn _ ih =>
    obtain ⟨k,hk⟩ := ih
    obtain ⟨j,hj⟩ := hn.1
    exact ⟨max j k,.cons (Ω.at_mono hj (le_max_left j k)) hn.2 (hk.mono (le_max_right j k))⟩
end TestedStack
end Candidates

namespace ComponentInterface

section
open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

theorem identity_admissible {k : Nat} {e : J.Env (Ω.context k)}
    (he : J.images e = Expr.var ∘ Expr.reverseIndex k) : J.Admissible (U := U) e := by
  intro i B hi
  obtain ⟨s,hB⟩ := HasType.lookup_sorted (Ω.valid k) hi
  have ht := (J.typed e i B hi).normalize_type hw
  have hG : J.images e i ∈ Ground Ω (B.subst (J.images e)).normalForm := by
    rw [he] at ht ⊢
    exact var_ground _ ht
  exact ⟨fun _ => (J.candidate e (.sorted hB)).lower hG,
    fun _ => (ground_le_top hG).2,fun _ _ => hG⟩

@[simp] theorem identity_actual {k : Nat} {e : J.Env (Ω.context k)}
    (he : J.images e = Expr.var ∘ Expr.reverseIndex k) (T : Expr S) :
    (T.rename (Expr.reverseIndex k)).subst (J.images e) = T := by
  rw [he,Expr.subst_var_rename,Expr.reverseIndex_twice]

end

open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C) (H : Processed Ω U C)
include J H

theorem run_stack {k : Nat} {e : J.Env (Ω.context k)}
    (he : J.images e = Expr.var ∘ Expr.reverseIndex k)
    {T : Expr S} {ns : List (Expr S)} (hstack : StackAt Ω k T ns) :
    ∀ {s}, HasType P (Ω.context k) (T.rename (Expr.reverseIndex k)) (.sort s) →
    Normal T → Ω.profile T ∈ U ∨ Ω.profile T ∈ C →
    ∀ h, h ∈ J.R (T.rename (Expr.reverseIndex k)) e → StronglyNormalizing (h.apps ns) := by
  induction hstack with
  | nil T =>
      intro s ht hN _ h hr
      exact (J.candidate e (.sorted ht)).upper hr |>.2
  | @cons D E n ns hn hsn hstack ih =>
      intro s ht hN hprofile h hr
      have hactual : ActualType Ω (.pi D E) := .inl ⟨hN,s,⟨k,ht⟩⟩
      rcases hprofile with hU | hC
      · have htop := (J.candidate e (.sorted ht)).upper hr
        rw [J.identity_actual he,Expr.normalForm_of_normal hN] at htop
        have hg : h ∈ Ground Ω (.pi D E) := by
          rw [H.invariant hactual hU]; exact htop
        exact hg.2 (n :: ns) (.cons ⟨⟨k,hn⟩,hsn⟩ hstack.tested)
      · obtain ⟨a,b,c,hD,hE,_,_⟩ := ht.generation_pi
        have hnR := (J.sn_fundamental H (hsn.reverseIndex k) _ _ hn e
          (J.identity_admissible he)).1
        have hr' := J.specialization e ht hn (by
          change Profile P (Ω.context k) ((Expr.pi D E).rename (Expr.reverseIndex k)) ∈ C
          rwa [← Ω.profile_at hw ht])
          (by
            change Ω.profile (((Expr.pi D E).rename (Expr.reverseIndex k)).subst (J.images e)) ∈ C
            rwa [J.identity_actual he]) h hr hnR
        change Expr.app h ((n.rename (Expr.reverseIndex k)).subst (J.images e)) ∈
          J.R ((E.rename (Expr.liftRen (Expr.reverseIndex k))).instantiate
            (n.rename (Expr.reverseIndex k))) e at hr'
        rw [J.identity_actual he,Expr.instantiate_rename] at hr'
        have htarget : HasType P (Ω.context k) ((E.instantiate n).rename (Expr.reverseIndex k)) (.sort b) := by
          have hti := hE.instantiate hn
          change HasType P (Ω.context k) ((E.rename (Expr.liftRen (Expr.reverseIndex k))).instantiate
            (n.rename (Expr.reverseIndex k))) (.sort b) at hti
          rwa [Expr.instantiate_rename] at hti
        have htargetΩ : Ω.HasType (E.instantiate n) (.sort b) := ⟨k,htarget⟩
        have hwtarget := htargetΩ.weaklyNormalizing hw
        have htargetN : HasType P (Ω.context k) ((E.instantiate n).normalForm.rename (Expr.reverseIndex k)) (.sort b) := by
          rw [← Expr.normalForm_rename hwtarget]
          exact htarget.normalForm hw
        have hconv : Converts ((E.instantiate n).rename (Expr.reverseIndex k))
            ((E.instantiate n).normalForm.rename (Expr.reverseIndex k)) :=
          (Expr.normalForm_spec hwtarget).1.converts.rename _
        rw [J.conversion e (.sorted htarget) (.sorted htargetN) hconv] at hr'
        have hprofile' : Ω.profile (E.instantiate n).normalForm ∈ U ∨
            Ω.profile (E.instantiate n).normalForm ∈ C := by
          rw [Ω.profile_normalForm]
          exact H.before hC (Ω.profile_instantiate_product_path hw ⟨k,ht⟩ ⟨k,hn⟩).reach
        exact ih htargetN (Expr.normalForm_spec hwtarget).2 hprofile' (.app h n) hr'

/-- Advancing a component uses one identity evaluation, not a new
substitution choice at each stack prefix. -/
theorem advance {T : Expr S} (hT : ActualType Ω T) (hC : Ω.profile T ∈ C) :
    Ground Ω T = Top Ω T := by
  apply Set.Subset.antisymm ground_le_top
  intro h hh
  rcases hT with ⟨hN,s,ks,ht⟩ | ⟨s,rfl⟩
  · refine ⟨hh.1,?_⟩
    intro ns hstack
    obtain ⟨kn,hs⟩ := hstack.common_stage
    obtain ⟨kh,hhT⟩ := hh.1
    let k := max ks (max kn kh)
    have hkT : ks ≤ k := le_max_left _ _
    have hkN : kn ≤ k := le_trans (le_max_left _ _) (le_max_right _ _)
    have hkH : kh ≤ k := le_trans (le_max_right _ _) (le_max_right _ _)
    have ht' := Ω.at_mono ht hkT
    have hh' := Ω.at_mono hhT hkH
    obtain ⟨e,he⟩ := J.inhabit (.var ∘ Expr.reverseIndex k) (.identity k)
    have hr := (J.sn_fundamental H (hh.2.reverseIndex k) _ _ hh' e
      (J.identity_admissible he)).1
    rw [J.identity_actual he] at hr
    exact J.run_stack H he (hs.mono hkN) ht' hN (.inr hC) h hr
  · rwa [sort_ground_eq_top]

end ComponentInterface
end

universe u v
open Classical Candidates

namespace Beta
variable {S : Type u}
/-- Renaming cannot create a redex, and every renamed step has an exact source. -/
theorem rename_source {M N : Expr S} {ρ : Nat → Nat} (h : Beta (M.rename ρ) N) :
    ∃ M', Beta M M' ∧ N = M'.rename ρ := by
  induction M generalizing ρ N with
  | var n => cases h
  | sort s => cases h
  | pi A B ihA ihB =>
    cases h with
    | pi_domain hh =>
      obtain ⟨A',ha,rfl⟩ := ihA hh
      exact ⟨_,.pi_domain ha,rfl⟩
    | pi_body hh =>
      obtain ⟨B',hb,rfl⟩ := ihB hh
      exact ⟨_,.pi_body hb,rfl⟩
  | lam A b ihA ihb =>
    cases h with
    | lam_domain hh =>
      obtain ⟨A',ha,rfl⟩ := ihA hh
      exact ⟨_,.lam_domain ha,rfl⟩
    | lam_body hh =>
      obtain ⟨b',hb,rfl⟩ := ihb hh
      exact ⟨_,.lam_body hb,rfl⟩
  | app f a ihf iha =>
    cases f <;> cases h
    all_goals first
      | (rename_i hh
         obtain ⟨f',hf,rfl⟩ := ihf hh
         exact ⟨_,.app_left hf,rfl⟩)
      | (rename_i hh
         obtain ⟨a',ha,rfl⟩ := iha hh
         exact ⟨_,.app_right ha,rfl⟩)
      | exact ⟨_,.head _ _ _,Expr.instantiate_rename _ _ _⟩
end Beta
namespace StronglyNormalizing
variable {S : Type u} {M : Expr S}
theorem rename (h : StronglyNormalizing M) (ρ : Nat → Nat) :
    StronglyNormalizing (M.rename ρ) := by
  induction h with
  | intro M _ ih =>
    apply Acc.intro
    intro N hn
    obtain ⟨M',hm,rfl⟩ := hn.rename_source
    exact ih M' hm
end StronglyNormalizing

namespace ContextTower
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

/-- Every valid finite context has a variable-valued interpretation in the
saturated tower. Substitution reflection does not require these names to be
surjective or even injective. -/
theorem variable_substitution {Γ : List (Expr S)} (hΓ : ValidContext P Γ) :
    ∃ ρ : Nat → Nat, Ω.TypedSubstitution Γ (Expr.var ∘ ρ) := by
  induction hΓ with
  | nil => exact ⟨id,fun _ _ h => nomatch h⟩
  | @cons Γ A s hΓ hA ih =>
    obtain ⟨ρ,hρ⟩ := ih
    have ht := HasType.subst hA hρ
    obtain ⟨n,_,hn⟩ := Ω.fresh_variable ht 0
    refine ⟨fun i => match i with | 0 => n | i+1 => ρ i,?_⟩
    convert hρ.cons hn using 1
    funext i; cases i <;> rfl

end ContextTower

/-- Finite primary-component induction. The supplied interfaces are consumed
one at a time, and Ground=Top is only used at strict predecessor components. -/
theorem all_ground_eq_top {S : Type u} [Fintype S] {P : Specification S}
    (Ω : ContextTower P) (hw : SystemWeaklyNormalizing P)
    (interfaces : ∀ C, IsComponent (PrimaryEdge P) C →
      Nonempty (ComponentInterface.{u,v} Ω hw C)) :
    ∀ {T}, ActualType Ω T → Ground Ω T = Top Ω T := by
  intro T hT
  let E := PrimaryEdge P
  have h : ∀ n, ∀ T : Expr S, Reach.rank E (Ω.profile T) = n → ActualType Ω T →
      Ground Ω T = Top Ω T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hr hT
      let V := Ω.profile T
      let C := Reach.component E V
      let U := {I | Reach.rank E I < n}
      have hC : IsComponent E C := Reach.component_isComponent E V
      have rankC {I} (hi : I ∈ C) : Reach.rank E I = n := by
        exact (Nat.le_antisymm (Reach.rank_mono E hi.2) (Reach.rank_mono E hi.1)).trans hr
      have hp : Processed Ω U C := by
        refine ⟨?_,?_,?_,?_⟩
        · apply Set.disjoint_left.mpr
          intro I hI hc
          have : Reach.rank E I < n := hI
          rw [rankC hc] at this
          exact Nat.lt_irrefl _ this
        · intro I J hj hij
          exact lt_of_le_of_lt (Reach.rank_mono E hij) hj
        · intro I J hj hij
          have hle : Reach.rank E I ≤ n := (Reach.rank_mono E hij).trans (le_of_eq (rankC hj))
          rcases lt_or_eq_of_le hle with hlt | heq
          · exact .inl hlt
          · exact .inr ⟨hj.1.trans (Reach.reverse_of_rank_eq E hij (heq.trans (rankC hj).symm)),
              hij.trans hj.2⟩
        · intro A hA hAu
          exact ih _ hAu A rfl hA
      obtain ⟨J⟩ := interfaces C hC
      exact J.advance hp hT (Reach.mem_component E V)
  exact h _ T rfl hT

/-- Once all actual types have Ground=Top, typed application preserves SN.
Types and annotations are normalized using WN, not assumed SN. -/
theorem application_sn_of_ground {S : Type u} {P : Specification S}
    (Ω : ContextTower P) (hw : SystemWeaklyNormalizing P)
    (hground : ∀ {T}, ActualType Ω T → Ground Ω T = Top Ω T)
    {Γ : List (Expr S)} {f a D E : Expr S}
    (hf : HasType P Γ f (.pi D E)) (ha : HasType P Γ a D)
    (hsf : StronglyNormalizing f) (hsa : StronglyNormalizing a) :
    StronglyNormalizing (.app f a) := by
  obtain ⟨ρ,hρ⟩ := Ω.variable_substitution hf.valid
  have hf' := ContextTower.HasType.subst hf hρ
  have ha' := ContextTower.HasType.subst ha hρ
  simp only [Expr.subst_var_rename] at hf' ha'
  obtain ⟨s,hpi⟩ := hf.product_type_sorted
  have hpi' := ContextTower.HasType.subst hpi hρ
  simp only [Expr.subst_var_rename,Expr.rename] at hpi'
  obtain ⟨a',b',c',hD,hE,hr,_⟩ := hpi.generation_pi
  have hDw := (ContextTower.HasType.subst hD hρ).weaklyNormalizing hw
  simp only [Expr.subst_var_rename] at hDw
  have hPw := hpi'.weaklyNormalizing hw
  have hDN : Normal (D.rename ρ).normalForm := (Expr.normalForm_spec hDw).2
  have hPN := (Expr.normalForm_spec hPw).2
  have hpNF : ((Expr.pi D E).rename ρ).normalForm =
      .pi (D.rename ρ).normalForm (E.rename (Expr.liftRen ρ)).normalForm := by
    apply Expr.normalForm_pi hDw
    obtain ⟨target, reduces, normal⟩ := hPw
    obtain ⟨domain, body, rfl, _, bodyReduces⟩ := Reduces.pi_inv reduces
    exact ⟨body, bodyReduces, normal.pi_body⟩
  have htype : ActualType Ω ((Expr.pi D E).rename ρ).normalForm :=
    .inl ⟨hPN,s,hpi'.normalForm hw⟩
  have hfg : f.rename ρ ∈ Ground Ω ((Expr.pi D E).rename ρ).normalForm := by
    rw [hground htype]
    exact ⟨hf'.normalize_type hw,hsf.rename ρ⟩
  rw [hpNF] at hfg
  have hag : a.rename ρ ∈ Top Ω (D.rename ρ).normalForm := ⟨ha'.normalize_type hw,hsa.rename ρ⟩
  have hs := (ground_le_top (ground_application hw hfg hag)).2
  exact StronglyNormalizing.of_rename ρ hs

end S_wpc_barendregt_geuvers_klop

end OMA



namespace OMA

namespace S_wpc_barendregt_geuvers_klop.SignedInterpretation

section
universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
variable {C : Set (Set S)} (hC : IsComponent (PrimaryEdge P) C)
variable (hw : SystemWeaklyNormalizing P)
variable (hno : ∀ I ∈ C, ¬ SignedPath (PrimaryEdge P) I I true)

abbrev Vector := (T : Expr S) → SignedCandidate Ω T (hC.signing (Ω.profile T))

noncomputable def value (v : Vector Ω hC) (T : Expr S) : Set (Expr S) :=
  if Ω.profile T ∈ C then (v T).set else Top Ω T

theorem value_candidate (v : Vector Ω hC) (T : Expr S) :
    IsCandidate Ω T (value Ω hC v T) := by
  unfold value; split
  · exact (v T).candidate
  · exact top_candidate

theorem value_forward {v w : Vector Ω hC} (hv : v ≤ w) {T : Expr S}
    (hs : Ω.profile T ∈ C → hC.signing (Ω.profile T) = false) :
    value Ω hC v T ⊆ value Ω hC w T := by
  unfold value; split
  · have hh := (SignedCandidate.order (v T) (w T)).mp (hv T)
    simpa only [hs ‹_›,Bool.false_eq_true,ite_false] using hh
  · exact Set.Subset.rfl

theorem value_backward {v w : Vector Ω hC} (hv : v ≤ w) {T : Expr S}
    (hs : Ω.profile T ∈ C → hC.signing (Ω.profile T) = true) :
    value Ω hC w T ⊆ value Ω hC v T := by
  unfold value; split
  · have hh := (SignedCandidate.order (v T) (w T)).mp (hv T)
    simpa only [hs ‹_›,ite_true] using hh
  · exact Set.Subset.rfl

noncomputable def stepCandidate (v : Vector Ω hC) (T : Expr S) : Candidate Ω T :=
  match T with
  | .pi D E =>
    if Normal (.pi D E) ∧ (∃ s, Ω.HasType (.pi D E) (.sort s)) ∧ Ω.profile (.pi D E) ∈ C then
      ⟨ProductTest Ω D E (value Ω hC v D) (fun n => {value Ω hC v (E.instantiate n).normalForm}),
        productTest_candidate hw (value_candidate Ω hC v D).upper (by
          intro n _ X hX
          rcases Set.mem_singleton_iff.mp hX with rfl
          exact value_candidate Ω hC v _)⟩
    else ⟨Top Ω (.pi D E),top_candidate⟩
  | T => ⟨Top Ω T,top_candidate⟩

noncomputable def step (v : Vector Ω hC) : Vector Ω hC :=
  fun T => SignedCandidate.wrap (stepCandidate Ω hC hw v T)

include hno in
theorem step_monotone : Monotone (step Ω hC hw) := by
  intro v w hv T
  apply (SignedCandidate.order _ _).mpr
  simp only [step,SignedCandidate.set_wrap]
  cases T with
  | sort s => cases hC.signing (Ω.profile (.sort s)) <;> exact Set.Subset.rfl
  | var i => cases hC.signing (Ω.profile (.var i)) <;> exact Set.Subset.rfl
  | lam D E => cases hC.signing (Ω.profile (.lam D E)) <;> exact Set.Subset.rfl
  | app f n => cases hC.signing (Ω.profile (.app f n)) <;> exact Set.Subset.rfl
  | pi D E =>
    dsimp only [stepCandidate]
    by_cases H : Normal (.pi D E) ∧ (∃ s, Ω.HasType (.pi D E) (.sort s)) ∧ Ω.profile (.pi D E) ∈ C
    · simp only [if_pos H]
      obtain ⟨hn,⟨s,ht⟩,hpC⟩ := H
      have hd : ∀ hD : Ω.profile D ∈ C,
          hC.signing (Ω.profile (.pi D E)) = Bool.xor (hC.signing (Ω.profile D)) true := by
        intro hD
        obtain ⟨a,b,c,hD',hE,hr,hconv⟩ := ht.choose_spec.generation_pi
        have hf := Profile.triple hw ht.choose_spec
        have hglob : ProfileTriple P (Ω.profile D)
            (Profile P (D.rename (Expr.reverseIndex ht.choose) :: Ω.context ht.choose)
              (E.rename (Expr.liftRen (Expr.reverseIndex ht.choose)))) (Ω.profile (.pi D E)) := by
          rw [Ω.profile_at hw hD',Ω.profile_at hw ht.choose_spec]
          exact hf
        exact hC.signing_cross hno hD hpC (.singleton (.domain hglob))
      have he : ∀ n, Ω.HasType n D → Ω.profile (E.instantiate n).normalForm ∈ C →
          hC.signing (Ω.profile (E.instantiate n).normalForm) = hC.signing (Ω.profile (.pi D E)) := by
        intro n hn hnc
        rw [Ω.profile_normalForm] at hnc ⊢
        simpa only [Bool.xor_false] using
          (hC.signing_cross hno hnc hpC (Ω.profile_instantiate_product_path hw ht hn).parity).symm
      have flip (a b : Bool) (h : a = Bool.xor b true) : b = !a := by
        cases a <;> cases b <;> cases h <;> rfl
      cases hs : hC.signing (Ω.profile (.pi D E)) with
      | false =>
        simp only [Bool.false_eq_true,ite_false]
        intro h hh
        refine ⟨hh.1,?_⟩
        intro n hn X hX
        rcases Set.mem_singleton_iff.mp hX with rfl
        have hn' : n ∈ value Ω hC v D := value_backward Ω hC hv (by
          intro hc
          simpa only [hs,Bool.not_false,Bool.not_true] using flip _ _ (hd hc)) hn
        have hout := hh.2 n hn' _ (Set.mem_singleton _)
        exact value_forward Ω hC hv (fun hc => (he n (value_candidate Ω hC w D |>.upper hn).1 hc).trans hs) hout
      | true =>
        simp only [ite_true]
        intro h hh
        refine ⟨hh.1,?_⟩
        intro n hn X hX
        rcases Set.mem_singleton_iff.mp hX with rfl
        have hn' : n ∈ value Ω hC w D := value_forward Ω hC hv (by
          intro hc
          simpa only [hs,Bool.not_false,Bool.not_true] using flip _ _ (hd hc)) hn
        have hout := hh.2 n hn' _ (Set.mem_singleton _)
        exact value_backward Ω hC hv (fun hc => (he n (value_candidate Ω hC v D |>.upper hn).1 hc).trans hs) hout
    · simp only [if_neg H]
      cases hC.signing (Ω.profile (.pi D E)) <;> exact Set.Subset.rfl

noncomputable def operator : Vector Ω hC →o Vector Ω hC :=
  ⟨step Ω hC hw,step_monotone Ω hC hw hno⟩

noncomputable def fixed : Vector Ω hC := (operator Ω hC hw hno).lfp

noncomputable def actual (T : Expr S) : Set (Expr S) := value Ω hC (fixed Ω hC hw hno) T

theorem actual_candidate (T : Expr S) : IsCandidate Ω T (actual Ω hC hw hno T) :=
  value_candidate Ω hC _ T

theorem actual_outside {T : Expr S} (ho : Ω.profile T ∉ C) : actual Ω hC hw hno T = Top Ω T := by
  simp only [actual,value,ho,ite_false]

theorem actual_product {D E : Expr S} {s : S} (hn : Normal (.pi D E))
    (ht : Ω.HasType (.pi D E) (.sort s)) (hc : Ω.profile (.pi D E) ∈ C) :
    actual Ω hC hw hno (.pi D E) =
      ProductTest Ω D E (actual Ω hC hw hno D) (fun n => {actual Ω hC hw hno (E.instantiate n).normalForm}) := by
  have he := congrArg (fun v : Vector Ω hC => (v (.pi D E)).set) (operator Ω hC hw hno).map_lfp
  change (step Ω hC hw (fixed Ω hC hw hno) (.pi D E)).set = _ at he
  dsimp only [step,SignedCandidate.set_wrap,stepCandidate] at he
  rw [if_pos (show Normal (.pi D E) ∧ (∃ s, Ω.HasType (.pi D E) (.sort s)) ∧
    Ω.profile (.pi D E) ∈ C from ⟨hn,⟨s,ht⟩,hc⟩)] at he
  simpa only [actual,value,hc,ite_true,SignedCandidate.set_wrap,fixed] using he.symm
end

universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
variable {C : Set (Set S)} (hC : IsComponent (PrimaryEdge P) C)
variable (hw : SystemWeaklyNormalizing P)
variable (hno : ∀ I ∈ C, ¬ SignedPath (PrimaryEdge P) I I true)

abbrev Environment (Γ : List (Expr S)) := {σ : Nat → Expr S // Ω.TypedSubstitution Γ σ}

noncomputable def R {Γ : List (Expr S)} (A : Expr S) (e : Environment Ω Γ) : Set (Expr S) :=
  if Profile P Γ A ∈ C then actual Ω hC hw hno (A.subst e.val).normalForm
  else Top Ω (A.subst e.val).normalForm

theorem R_candidate {Γ : List (Expr S)} (A : Expr S) (e : Environment Ω Γ) :
    IsCandidate Ω (A.subst e.val).normalForm (R Ω hC hw hno A e) := by
  unfold R; split
  · exact actual_candidate Ω hC hw hno _
  · exact top_candidate

theorem R_outside {Γ : List (Expr S)} (A : Expr S) (e : Environment Ω Γ)
    (ho : Profile P Γ A ∉ C ∨ Ω.profile (A.subst e.val) ∉ C) :
    R Ω hC hw hno A e = Top Ω (A.subst e.val).normalForm := by
  unfold R; split
  · exact actual_outside Ω hC hw hno (by
      rw [Ω.profile_normalForm]; exact ho.resolve_left (not_not.mpr ‹_›))
  · rfl

theorem R_conversion {Γ : List (Expr S)} {A B : Expr S}
    (e : Environment Ω Γ) (hA : Expected P Γ A) (hB : Expected P Γ B) (hc : Converts A B) :
    R Ω hC hw hno A e = R Ω hC hw hno B e := by
  have hwa : WeaklyNormalizing A := by
    rcases hA with ⟨s,rfl⟩ | ⟨s,h⟩
    · exact ⟨_,.refl,Normal.sort s⟩
    · exact h.weaklyNormalizing hw
  have hwb : WeaklyNormalizing B := by
    rcases hB with ⟨s,rfl⟩ | ⟨s,h⟩
    · exact ⟨_,.refl,Normal.sort s⟩
    · exact h.weaklyNormalizing hw
  have hp := Profile.converts (P := P) (Γ := Γ) hwa hwb hc
  have hn := Expr.normalForm_converts (hA.subst_wn hw e.property) (hB.subst_wn hw e.property) (hc.subst e.val)
  simp only [R,hp,hn]

theorem actual_sort (s : S) : actual Ω hC hw hno (.sort s) = Top Ω (.sort s) := by
  by_cases hc : Ω.profile (.sort s) ∈ C
  · have he := congrArg (fun v : Vector Ω hC => (v (.sort s)).set) (operator Ω hC hw hno).map_lfp
    change (step Ω hC hw (fixed Ω hC hw hno) (.sort s)).set = _ at he
    simpa only [step,stepCandidate,SignedCandidate.set_wrap,actual,value,hc,ite_true,fixed] using he.symm
  · exact actual_outside Ω hC hw hno hc

theorem R_sort {Γ : List (Expr S)} (s : S) (e : Environment Ω Γ) :
    R Ω hC hw hno (.sort s) e = Top Ω (.sort s) := by
  simp only [R,Expr.subst,Expr.normalForm_of_normal (Normal.sort s),actual_sort,ite_self]

theorem R_weakening {Γ : List (Expr S)} {D A n : Expr S} {s : S}
    {e : Environment Ω Γ} {f : Environment Ω (D :: Γ)}
    (hD : HasType P Γ D (.sort s)) (hA : Expected P Γ A)
    (he : f.val = Expr.extend e.val n) :
    R Ω hC hw hno (A.rename Nat.succ) f = R Ω hC hw hno A e := by
  rcases hA with ⟨a,rfl⟩ | ⟨a,hA⟩
  · exact (R_sort Ω hC hw hno a f).trans (R_sort Ω hC hw hno a e).symm
  · simp only [R,Profile.weaken hw hA hD,he,Expr.subst_raise_extend]

theorem R_before {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (e : Environment Ω Γ)
    (hp : ∃ K ∈ C, Reach (PrimaryEdge P) (Profile P Γ A) K) :
    R Ω hC hw hno A e = actual Ω hC hw hno (A.subst e.val).normalForm := by
  unfold R; split
  · rfl
  · rename_i hn
    refine (actual_outside Ω hC hw hno ?_).symm
    rw [Ω.profile_normalForm]
    intro ha
    obtain ⟨K,hK,hp⟩ := hp
    exact hn (hC.between ha hK (Ω.profile_subst_path hw hA e.property).reach hp)

/-- The actual fixed point tests precisely every raw argument; normalization of
its codomain commutes with this specialization by confluence. -/
theorem actual_raw_product {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (e : Environment Ω Γ)
    (ha : Ω.profile ((Expr.pi D E).subst e.val) ∈ C) (h : Expr S) :
    h ∈ actual Ω hC hw hno ((Expr.pi D E).subst e.val).normalForm ↔
    h ∈ Top Ω ((Expr.pi D E).subst e.val).normalForm ∧
      ∀ n, n ∈ actual Ω hC hw hno (D.subst e.val).normalForm →
        Expr.app h n ∈ actual Ω hC hw hno (E.subst (Expr.extend e.val n)).normalForm := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hraw := ContextTower.HasType.subst hp e.property
  have hwraw := hraw.weaklyNormalizing hw
  change WeaklyNormalizing (.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))) at hwraw
  have hparts : WeaklyNormalizing (D.subst e.val) ∧
      WeaklyNormalizing (E.subst (Expr.liftSub e.val)) := by
    obtain ⟨normal, reduction, hnormal⟩ := hwraw
    obtain ⟨domain, body, rfl, hdomain, hbody⟩ := Reduces.pi_inv reduction
    exact ⟨⟨domain, hdomain, hnormal.pi_domain⟩, ⟨body, hbody, hnormal.pi_body⟩⟩
  have hnf := Expr.normalForm_pi hparts.1 hparts.2
  have hpN := hraw.normalForm hw
  change Ω.HasType (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).normalForm (.sort s) at hpN
  rw [hnf] at hpN
  have hNC : Ω.profile (.pi (D.subst e.val).normalForm (E.subst (Expr.liftSub e.val)).normalForm) ∈ C := by
    rw [← hnf,Ω.profile_normalForm]; exact ha
  have hnormal : Normal (.pi (D.subst e.val).normalForm (E.subst (Expr.liftSub e.val)).normalForm) :=
    .pi (Expr.normalForm_spec hparts.1).2 (Expr.normalForm_spec hparts.2).2
  have hbody (n : Expr S) (hn : n ∈ actual Ω hC hw hno (D.subst e.val).normalForm) :
      (E.subst (Expr.extend e.val n)).normalForm =
        ((E.subst (Expr.liftSub e.val)).normalForm.instantiate n).normalForm := by
    have hnt := (actual_candidate Ω hC hw hno _).upper hn |>.1
    have hrawD := ContextTower.HasType.subst hD e.property
    have hnr := hnt.conversion hrawD
      (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
    have htarget := ContextTower.HasType.subst hE (e.property.cons hnr)
    obtain ⟨t,ht⟩ := Ω.frame_target_sorted hpN hnt
    have hr : Reduces (E.subst (Expr.extend e.val n))
        ((E.subst (Expr.liftSub e.val)).normalForm.instantiate n) := by
      rw [← Expr.instantiate_extended]
      exact (Expr.normalForm_spec hparts.2).1.subst (Expr.single n)
    exact Expr.normalForm_converts (htarget.weaklyNormalizing hw) (ht.weaklyNormalizing hw) hr.converts
  change h ∈ actual Ω hC hw hno (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).normalForm ↔ _
  change h ∈ actual Ω hC hw hno (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).normalForm ↔
    h ∈ Top Ω (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).normalForm ∧ _
  rw [hnf,actual_product Ω hC hw hno hnormal hpN hNC]
  constructor
  · rintro ⟨ht,hb⟩
    refine ⟨ht,?_⟩
    intro n hn
    rw [hbody n hn]
    exact hb n hn _ (Set.mem_singleton _)
  · rintro ⟨ht,hb⟩
    refine ⟨ht,?_⟩
    intro n hn X hX
    rcases Set.mem_singleton_iff.mp hX with rfl
    rw [← hbody n hn]
    exact hb n hn

theorem product_intro {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (e : Environment Ω Γ) (hp : HasType P Γ (.pi D E) (.sort s))
    (hg : Profile P Γ (.pi D E) ∈ C) (ha : Ω.profile ((Expr.pi D E).subst e.val) ∈ C)
    (h : Expr S) (ht : h ∈ Top Ω ((Expr.pi D E).subst e.val).normalForm)
    (hb : ∀ n, n ∈ R Ω hC hw hno D e → ∀ f : Environment Ω (D :: Γ),
      f.val = Expr.extend e.val n → Expr.app h n ∈ R Ω hC hw hno E f) :
    h ∈ R Ω hC hw hno (.pi D E) e := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hf := Profile.triple hw hp
  have hd := R_before Ω hC hw hno hD e ⟨_,hg,.single (.domain hf)⟩
  simp only [R,hg,ite_true]
  apply (actual_raw_product Ω hC hw hno hp e ha h).mpr
  refine ⟨ht,?_⟩
  intro n hn
  have hnt := (actual_candidate Ω hC hw hno _).upper hn |>.1
  have hrawD := ContextTower.HasType.subst hD e.property
  have hnr := hnt.conversion hrawD
    (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
  let f : Environment Ω (D :: Γ) := ⟨Expr.extend e.val n,e.property.cons hnr⟩
  have he := R_before Ω hC hw hno hE f ⟨_,hg,.single (.codomain hf)⟩
  have hh := hb n (hd.symm ▸ hn) f rfl
  exact he ▸ hh

theorem specialization {Γ : List (Expr S)} {D E N : Expr S} {s : S}
    (e : Environment Ω Γ) (hp : HasType P Γ (.pi D E) (.sort s)) (hN : HasType P Γ N D)
    (hg : Profile P Γ (.pi D E) ∈ C) (ha : Ω.profile ((Expr.pi D E).subst e.val) ∈ C)
    (h : Expr S) (hh : h ∈ R Ω hC hw hno (.pi D E) e)
    (hn : N.subst e.val ∈ R Ω hC hw hno D e) :
    Expr.app h (N.subst e.val) ∈ R Ω hC hw hno (E.instantiate N) e := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hf := Profile.triple hw hp
  have hd := R_before Ω hC hw hno hD e ⟨_,hg,.single (.domain hf)⟩
  have he := R_before Ω hC hw hno (hE.instantiate hN) e
    ⟨_,hg,(Profile.instantiate_product_path hw hp hN).reach⟩
  simp only [R,hg,ite_true] at hh
  have hout := (actual_raw_product Ω hC hw hno hp e ha h).mp hh |>.2 _ (hd ▸ hn)
  rw [he,← Expr.instantiate_subst,Expr.instantiate_extended]
  exact hout

noncomputable def componentInterface : ComponentInterface Ω hw C where
  Env := Environment Ω
  images := Subtype.val
  typed := Subtype.property
  inhabit σ hσ := ⟨⟨σ,hσ⟩,rfl⟩
  Ext e f n := f.val = Expr.extend e.val n
  ext_images he := he
  extend e _ _ hn := ⟨⟨_,e.property.cons hn⟩,rfl⟩
  R := R Ω hC hw hno
  candidate e _ := R_candidate Ω hC hw hno _ e
  conversion e ha hb hc := R_conversion Ω hC hw hno e ha hb hc
  outside e _ ho := R_outside Ω hC hw hno _ e ho
  weakening hd he hx := R_weakening Ω hC hw hno hd he hx
  product_intro e hp hg ha h ht hb := product_intro Ω hC hw hno e hp hg ha h ht hb
  specialization e hp hn hg ha h hh hN := specialization Ω hC hw hno e hp hn hg ha h hh hN

end S_wpc_barendregt_geuvers_klop.SignedInterpretation

end OMA



namespace OMA

namespace S_wpc_barendregt_geuvers_klop.OneChildInterpretation

section
universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))

abbrev Bits := Nat → Bool

def extendBit (θ : Bits) (b : Bool) : Bits
  | 0 => b
  | n+1 => θ n

def head : Expr S → Option Nat
  | .var n => some n
  | .app f _ => head f
  | _ => none

/-- Both choices are tested at each binder. Specialization will select the
extreme choice given by the unique internal support path. -/
noncomputable def eval (Γ : List (Expr S)) (A : Expr S) (σ : Nat → Expr S) (θ : Bits) : Set (Expr S) :=
  if Profile P Γ A ∈ C ∧ Ω.profile (A.subst σ) ∈ C then
    match A with
    | .pi D E => RawProduct Ω D E σ (eval Γ D σ θ)
        (fun n b => eval (D :: Γ) E (Expr.extend σ n) (extendBit θ b))
    | A => match head A with
      | none => Top Ω (A.subst σ).normalForm
      | some i => if θ i then Top Ω (A.subst σ).normalForm else Bottom Ω (A.subst σ).normalForm
  else Top Ω (A.subst σ).normalForm

@[simp] theorem head_rename (A : Expr S) (ρ : Nat → Nat) :
    head (A.rename ρ) = (head A).map ρ := by
  induction A with
  | app f n ihf ihn => exact ihf
  | var i => rfl
  | sort s => rfl
  | lam D m ihD ihm => rfl
  | pi D E ihD ihE => rfl

theorem head_subst {A : Expr S} {i : Nat} (hi : head A = some i) (σ : Nat → Expr S) :
    head (A.subst σ) = head (σ i) := by
  induction A with
  | var j => cases hi; rfl
  | app f n ihf ihn => exact ihf hi
  | sort s => cases hi
  | pi D E ihD ihE => cases hi
  | lam D m ihD ihm => cases hi

theorem head_beta {A B : Expr S} {i : Nat} (hi : head A = some i) (hr : Beta A B) :
    head B = some i := by
  induction hr with
  | head D m n => cases hi
  | app_left hr ih => exact ih hi
  | app_right hr ih => exact hi
  | lam_domain hr ih => cases hi
  | lam_body hr ih => cases hi
  | pi_domain hr ih => cases hi
  | pi_body hr ih => cases hi

theorem head_reduces {A B : Expr S} {i : Nat} (hi : head A = some i) (hr : Reduces A B) :
    head B = some i := by
  induction hr with
  | refl => exact hi
  | tail hr hs ih => exact head_beta ih hs

theorem head_normalForm {A : Expr S} {i : Nat} (hi : head A = some i) (hw : WeaklyNormalizing A) :
    head A.normalForm = some i := head_reduces hi (Expr.normalForm_spec hw).1

theorem eval_pi (Γ : List (Expr S)) (D E : Expr S) (σ : Nat → Expr S) (θ : Bits) :
    eval Ω C Γ (.pi D E) σ θ =
      if Profile P Γ (.pi D E) ∈ C ∧ Ω.profile ((Expr.pi D E).subst σ) ∈ C then
        RawProduct Ω D E σ (eval Ω C Γ D σ θ)
          (fun n b => eval Ω C (D :: Γ) E (Expr.extend σ n) (extendBit θ b))
      else Top Ω ((Expr.pi D E).subst σ).normalForm := rfl

theorem eval_head {Γ : List (Expr S)} {A : Expr S} {σ : Nat → Expr S} {θ : Bits} {i : Nat}
    (hg : Profile P Γ A ∈ C) (ha : Ω.profile (A.subst σ) ∈ C) (hi : head A = some i) :
    eval Ω C Γ A σ θ = if θ i then Top Ω (A.subst σ).normalForm else Bottom Ω (A.subst σ).normalForm := by
  cases A <;> simp only [eval,if_pos (And.intro hg ha)]
  all_goals first | (cases hi <;> rfl) | (rw [hi])

theorem eval_sort (Γ : List (Expr S)) (s : S) (σ : Nat → Expr S) (θ : Bits) :
    eval Ω C Γ (.sort s) σ θ = Top Ω (.sort s) := by
  simp only [eval,head,ite_self,Expr.subst,Expr.normalForm_of_normal (Normal.sort s)]

variable (hw : SystemWeaklyNormalizing P)
include hw

theorem eval_candidate {Γ : List (Expr S)} {A : Expr S} {s : S}
    {σ : Nat → Expr S} (hA : HasType P Γ A (.sort s)) (hσ : Ω.TypedSubstitution Γ σ) (θ : Bits) :
    IsCandidate Ω (A.subst σ).normalForm (eval Ω C Γ A σ θ) := by
  induction A generalizing Γ s σ θ with
  | pi D E ihD ihE =>
    rw [eval]
    split
    · obtain ⟨a,b,c,hD,hE,_,_⟩ := hA.generation_pi
      have hX := ihD hD hσ θ
      apply rawProduct_candidate hw hA hσ hX
      intro n hn bit
      have hrawD := ContextTower.HasType.subst hD hσ
      have ht := (hX.upper hn).1.conversion hrawD
        (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
      exact ihE hE (hσ.cons ht) (extendBit θ bit)
    · exact top_candidate
  | var i =>
    simp only [eval,head]
    split
    · split <;> first | exact top_candidate | exact bottom_candidate
    · exact top_candidate
  | sort s => simp only [eval,head,ite_self]; exact top_candidate
  | lam D m ihD ihm => simp only [eval,head,ite_self]; exact top_candidate
  | app f n ihf ihn =>
    simp only [eval]
    split
    · cases hh : head (.app f n) with
      | none => exact top_candidate
      | some i =>
        change IsCandidate Ω (Expr.subst σ (.app f n)).normalForm
          (if θ i then Top Ω (Expr.subst σ (.app f n)).normalForm else Bottom Ω (Expr.subst σ (.app f n)).normalForm)
        split <;> first | exact top_candidate | exact bottom_candidate
    · exact top_candidate

omit hw in
theorem eval_outside {Γ : List (Expr S)} {A : Expr S} {σ : Nat → Expr S} {θ : Bits}
    (ho : Profile P Γ A ∉ C ∨ Ω.profile (A.subst σ) ∉ C) :
    eval Ω C Γ A σ θ = Top Ω (A.subst σ).normalForm := by
  have hn : ¬ (Profile P Γ A ∈ C ∧ Ω.profile (A.subst σ) ∈ C) :=
    fun h => ho.elim (fun hn => hn h.1) (fun hn => hn h.2)
  cases A <;> simp only [eval,if_neg hn]

def dropSupport : Option (Nat × Bool) → Option (Nat × Bool)
  | some (0,_) => none
  | some (n+1,p) => some (n,p)
  | none => none

def flipSupport : Option (Nat × Bool) → Option (Nat × Bool) :=
  Option.map (fun (n,p) => (n,!p))

noncomputable def support (Γ : List (Expr S)) (A : Expr S) : Option (Nat × Bool) :=
  if Profile P Γ A ∈ C then
    match A with
    | .pi D E => if Profile P Γ D ∈ C then flipSupport (support Γ D)
        else dropSupport (support (D :: Γ) E)
    | A => (head A).map (fun i => (i,false))
  else none

structure Environment (Γ : List (Expr S)) where
  images : Nat → Expr S
  typed : Ω.TypedSubstitution Γ images
  bits : Bits

noncomputable def R {Γ : List (Expr S)} (A : Expr S) (e : Environment Ω Γ) : Set (Expr S) :=
  eval Ω C Γ A.normalForm e.images e.bits

theorem normal_subst_eq {Γ : List (Expr S)} {A : Expr S}
    (hA : Expected P Γ A) (e : Environment Ω Γ) :
    (A.normalForm.subst e.images).normalForm = (A.subst e.images).normalForm := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · rw [Expr.normalForm_of_normal (Normal.sort s)]
  · exact Expr.normalForm_converts
      ((ContextTower.HasType.subst (hA.normalForm hw) e.typed).weaklyNormalizing hw)
      ((ContextTower.HasType.subst hA e.typed).weaklyNormalizing hw)
      (.symm _ _ ((Expr.normalForm_spec (hA.weaklyNormalizing hw)).1.converts.subst e.images))

theorem R_candidate {Γ : List (Expr S)} {A : Expr S} (hA : Expected P Γ A) (e : Environment Ω Γ) :
    IsCandidate Ω (A.subst e.images).normalForm (R Ω C A e) := by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · simp only [R,Expr.normalForm_of_normal (Normal.sort s),eval,head,ite_self]
    exact top_candidate
  · rw [← normal_subst_eq Ω hw (.sorted hA) e]
    exact eval_candidate Ω C hw (hA.normalForm hw) e.typed e.bits

theorem R_conversion {Γ : List (Expr S)} {A B : Expr S}
    (hA : Expected P Γ A) (hB : Expected P Γ B) (hc : Converts A B) (e : Environment Ω Γ) :
    R Ω C A e = R Ω C B e := by
  simp only [R,Expr.normalForm_converts (hA.wn hw) (hB.wn hw) hc]

end

section
universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))
variable (hw : SystemWeaklyNormalizing P)

theorem eval_recontext {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (hc : ContextEquivalent P Γ Δ)
    (σ : Nat → Expr S) (θ : Bits) : eval Ω C Γ A σ θ = eval Ω C Δ A σ θ := by
  induction A generalizing Γ Δ s σ θ with
  | pi D E ihD ihE =>
    obtain ⟨a,b,c,hD,hE,_,_⟩ := hA.generation_pi
    have hp : Profile P Γ (.pi D E) = Profile P Δ (.pi D E) := Set.ext (fun s => hc.typing _ _)
    rw [eval_pi,eval_pi,hp]
    congr 1
    apply congrArg₂ (RawProduct Ω D E σ) (ihD hD hc σ θ)
    funext n bit
    exact ihE hE (hc.cons hD) _ _
  | var i =>
    have hp : Profile P Γ (.var i) = Profile P Δ (.var i) := Set.ext (fun s => hc.typing _ _)
    simp only [eval,hp]
  | sort s => rw [eval_sort,eval_sort]
  | app f n ihf ihn =>
    have hp : Profile P Γ (.app f n) = Profile P Δ (.app f n) := Set.ext (fun s => hc.typing _ _)
    simp only [eval,hp]
  | lam D m ihD ihm => exact False.elim hA.lambda_cannot_have_sort_type

include hw in
theorem eval_rename {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (hΔ : ValidContext P Δ)
    (ρ : Nat → Nat) (hρ : TypingTree.DeclRenaming Γ Δ ρ)
    (σ τ : Nat → Expr S) (θ ψ : Bits) (hσ : τ ∘ ρ = σ) (hθ : ψ ∘ ρ = θ) :
    eval Ω C Γ A σ θ = eval Ω C Δ (A.rename ρ) τ ψ := by
  induction A generalizing Γ Δ s ρ σ τ θ ψ with
  | pi D E ihD ihE =>
    obtain ⟨a,b,c,hD,hE,_,_⟩ := hA.generation_pi
    have hp := Profile.rename hw hA hΔ ρ (hρ.typed hΔ)
    have he (M : Expr S) : (M.rename ρ).subst τ = M.subst σ := by rw [Expr.subst_rename,hσ]
    rw [eval_pi]
    change _ = eval Ω C Δ (.pi (D.rename ρ) (E.rename (Expr.liftRen ρ))) τ ψ
    rw [eval_pi]
    have hraw : (Expr.pi (D.rename ρ) (E.rename (Expr.liftRen ρ))).subst τ = (Expr.pi D E).subst σ := he (.pi D E)
    have hX := ihD hD hΔ ρ hρ σ τ θ ψ hσ hθ
    have hY : (fun n bit => eval Ω C (D :: Γ) E (Expr.extend σ n) (extendBit θ bit)) =
        (fun n bit => eval Ω C (D.rename ρ :: Δ) (E.rename (Expr.liftRen ρ))
          (Expr.extend τ n) (extendBit ψ bit)) := by
      funext n bit
      apply ihE hE (.cons hΔ (hD.rename hΔ ρ (hρ.typed hΔ))) _ (hρ.lift D)
      · funext i; cases i with
        | zero => rfl
        | succ i => exact congrFun hσ i
      · funext i; cases i with
        | zero => rfl
        | succ i => exact congrFun hθ i
    change Profile P Δ (Expr.pi (D.rename ρ) (E.rename (Expr.liftRen ρ))) = _ at hp
    rw [hp,hraw]
    congr 1
    unfold RawProduct
    rw [hraw,hX,hY]
  | sort s => rw [eval_sort,Expr.rename,eval_sort]
  | var i =>
    have hp := Profile.rename hw hA hΔ ρ (hρ.typed hΔ)
    have he : (.var (ρ i) : Expr S).subst τ = Expr.subst σ (.var i) := congrFun hσ i
    change Profile P Δ (.var (ρ i)) = _ at hp
    simp only [eval,Expr.rename,hp,he,head]
    rw [show ψ (ρ i) = θ i from congrFun hθ i]
  | lam D m ihD ihm => exact False.elim hA.lambda_cannot_have_sort_type
  | app f n ihf ihn =>
    have hp := Profile.rename hw hA hΔ ρ (hρ.typed hΔ)
    have he : ((Expr.app f n).rename ρ).subst τ = (Expr.app f n).subst σ := by rw [Expr.subst_rename,hσ]
    simp only [Expr.rename] at hp he ⊢
    simp only [eval,hp,he,head,head_rename]
    cases hh : head f with
    | none => rfl
    | some i => simp only [Option.map_some]; rw [show ψ (ρ i) = θ i from congrFun hθ i]

namespace Environment
variable {Ω}
def Ext {Γ : List (Expr S)} {D : Expr S} (e : Environment Ω Γ) (f : Environment Ω (D :: Γ)) (n : Expr S) : Prop :=
  f.images = Expr.extend e.images n ∧ ∀ i, f.bits (i+1) = e.bits i
end Environment

theorem R_sort {Γ : List (Expr S)} (s : S) (e : Environment Ω Γ) :
    R Ω C (.sort s) e = Top Ω (.sort s) := by
  rw [R,Expr.normalForm_of_normal (Normal.sort s),eval_sort]

include hw in
theorem R_weakening {Γ : List (Expr S)} {D A n : Expr S} {s : S}
    {e : Environment Ω Γ} {f : Environment Ω (D :: Γ)}
    (hD : HasType P Γ D (.sort s)) (hA : Expected P Γ A) (he : e.Ext f n) :
    R Ω C (A.rename Nat.succ) f = R Ω C A e := by
  rcases hA with ⟨a,rfl⟩ | ⟨a,hA⟩
  · exact (R_sort Ω C a f).trans (R_sort Ω C a e).symm
  · rw [R,R,Expr.normalForm_rename (hA.weaklyNormalizing hw)]
    symm
    apply eval_rename Ω C hw (hA.normalForm hw) (.cons hD.valid hD) Nat.succ (TypingTree.DeclRenaming.weaken D)
    · rw [he.1]; rfl
    · exact funext (fun i => he.2 i)

end

section
universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))
variable (hw : SystemWeaklyNormalizing P)
include hw

theorem normal_product {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (σ : Nat → Expr S)
    (hσ : Ω.TypedSubstitution Γ σ) (θ : Bits) :
    eval Ω C Γ (Expr.pi D E).normalForm σ θ =
      if Profile P Γ (.pi D E) ∈ C ∧ Ω.profile ((Expr.pi D E).subst σ) ∈ C then
        RawProduct Ω D E σ (eval Ω C Γ D.normalForm σ θ)
          (fun n b => eval Ω C (D :: Γ) E.normalForm (Expr.extend σ n) (extendBit θ b))
      else Top Ω ((Expr.pi D E).subst σ).normalForm := by
  obtain ⟨a,b,c,hD,hE,hr,_⟩ := hp.generation_pi
  have hDN := hD.normalForm hw
  have hEN := hE.normalForm hw
  have cD := (Expr.normalForm_spec (hD.weaklyNormalizing hw)).1.converts
  have cE := (Expr.normalForm_spec (hE.weaklyNormalizing hw)).1.converts
  let ctx := ContextEquivalent.head_conversion hD hDN cD
  have hEN' := (ctx.typing _ _).mp hEN
  have hpn : HasType P Γ (.pi D.normalForm E.normalForm) (.sort c) := .product hDN hEN' hr
  have nc := Converts.pi cD cE
  have he : Profile P Γ (.pi D E) = Profile P Γ (.pi D.normalForm E.normalForm) :=
    Profile.converts (hp.weaklyNormalizing hw) (hpn.weaklyNormalizing hw) nc
  have hrw := (ContextTower.HasType.subst hp hσ).weaklyNormalizing hw
  have hnw := (ContextTower.HasType.subst hpn hσ).weaklyNormalizing hw
  have hnf := Expr.normalForm_converts hrw hnw (nc.subst σ)
  have hae : Ω.profile ((Expr.pi D E).subst σ) = Ω.profile ((Expr.pi D.normalForm E.normalForm).subst σ) := by
    rw [←Ω.profile_normalForm ((Expr.pi D E).subst σ),←Ω.profile_normalForm ((Expr.pi D.normalForm E.normalForm).subst σ),hnf]
  rw [Expr.normalForm_pi (hD.weaklyNormalizing hw) (hE.weaklyNormalizing hw),eval_pi,←he,←hae]
  split
  · unfold RawProduct
    rw [←hnf]
    simp_rw [←eval_recontext Ω C hEN ctx]
  · exact congrArg (Top Ω) hnf.symm

theorem R_outside {Γ : List (Expr S)} {A : Expr S} (hA : Expected P Γ A)
    (e : Environment Ω Γ) (ho : Profile P Γ A ∉ C ∨ Ω.profile (A.subst e.images) ∉ C) :
    R Ω C A e = Top Ω (A.subst e.images).normalForm := by
  have hnf := normal_subst_eq Ω hw hA e
  rw [R,eval_outside Ω C,hnf]
  rcases ho with ho | ho
  · exact .inl (by rwa [Profile.normalForm])
  · exact .inr (by
      rw [←Ω.profile_normalForm (A.normalForm.subst e.images),hnf,Ω.profile_normalForm]
      exact ho)

theorem product_iff {Γ : List (Expr S)} {D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (hg : Profile P Γ (.pi D E) ∈ C)
    (e : Environment Ω Γ) (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C) (h : Expr S) :
    h ∈ R Ω C (.pi D E) e ↔
      h ∈ Top Ω ((Expr.pi D E).subst e.images).normalForm ∧
      ∀ n, n ∈ R Ω C D e → ∀ f : Environment Ω (D :: Γ), e.Ext f n → Expr.app h n ∈ R Ω C E f := by
  rw [R,normal_product Ω C hw hp e.images e.typed e.bits,if_pos ⟨hg,ha⟩]
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  constructor
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hn f he
    have hb : f.bits = extendBit e.bits (f.bits 0) := by
      funext i; cases i with
      | zero => rfl
      | succ i => exact he.2 i
    change Expr.app h n ∈ eval Ω C (D :: Γ) E.normalForm f.images f.bits
    rw [he.1,hb]
    exact hbody n hn (f.bits 0)
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hn bit
    have hrawD := ContextTower.HasType.subst hD e.typed
    have hnt := ((R_candidate Ω C hw (.sorted hD) e).upper hn).1.conversion hrawD
      (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
    let f : Environment Ω (D :: Γ) := ⟨Expr.extend e.images n,e.typed.cons hnt,extendBit e.bits bit⟩
    exact hbody n hn f ⟨rfl,fun _ => rfl⟩

end

section
universe u
open Classical
variable {S : Type u} {P : Specification S} (C : Set (Set S))

/-- Replaced supported heads are assigned the extremum appropriate to the
comparison direction and path parity. Unreplaced heads retain their bit. -/
def CompatibleBits (r : Option (Nat × Bool)) (dir : Bool) (σ : Nat → Expr S) (θ ψ : Bits) : Prop :=
  ∀ i p, r = some (i,p) → (∃ j, σ i = .var j ∧ θ i = ψ j) ∨ θ i = Bool.xor dir p

def Below {α : Type*} (dir : Bool) (X Y : Set α) : Prop := if dir then Y ⊆ X else X ⊆ Y

theorem support_outside {Γ : List (Expr S)} {A : Expr S} (h : Profile P Γ A ∉ C) :
    support (P := P) C Γ A = none := by cases A <;> simp only [support,if_neg h]

theorem support_head {Γ : List (Expr S)} {A : Expr S} {i : Nat}
    (hg : Profile P Γ A ∈ C) (hi : head A = some i) : support (P := P) C Γ A = some (i,false) := by
  cases A <;> simp only [support,if_pos hg]
  all_goals first | (cases hi <;> rfl) | (rw [hi]; rfl)

theorem bits_domain {Γ : List (Expr S)} {D E : Expr S} {dir : Bool}
    {σ : Nat → Expr S} {θ ψ : Bits} (hg : Profile P Γ (.pi D E) ∈ C)
    (hb : CompatibleBits (support (P := P) C Γ (.pi D E)) dir σ θ ψ) :
    CompatibleBits (support (P := P) C Γ D) (!dir) σ θ ψ := by
  intro i p hi
  by_cases hd : Profile P Γ D ∈ C
  · have hp : support (P := P) C Γ (.pi D E) = some (i,!p) := by
      rw [support,if_pos hg,if_pos hd,flipSupport,hi]; rfl
    rcases hb i (!p) hp with h | h
    · exact .inl h
    · right
      have he : Bool.xor dir (!p) = Bool.xor (!dir) p := by cases dir <;> cases p <;> rfl
      exact h.trans he
  · rw [support_outside C hd] at hi
    cases hi

theorem bits_body (hw : SystemWeaklyNormalizing P)
    (hno : ∀ {I J K}, ProfileTriple P I J K → I ∈ C → J ∈ C → K ∈ C → False)
    {Γ : List (Expr S)} {D E : Expr S} {s : S} {dir : Bool}
    {σ : Nat → Expr S} {θ ψ : Bits} (hp : HasType P Γ (.pi D E) (.sort s))
    (hg : Profile P Γ (.pi D E) ∈ C)
    (hb : CompatibleBits (support (P := P) C Γ (.pi D E)) dir σ θ ψ) (bit : Bool) :
    CompatibleBits (support (P := P) C (D :: Γ) E) dir (Expr.liftSub σ) (extendBit θ bit) (extendBit ψ bit) := by
  intro i p hi
  by_cases hd : Profile P Γ D ∈ C
  · have he : Profile P (D :: Γ) E ∉ C := fun he => hno (Profile.triple hw hp) hd he hg
    rw [support_outside C he] at hi
    cases hi
  · cases i with
    | zero => exact .inl ⟨0,rfl,rfl⟩
    | succ i =>
      have hh : support (P := P) C Γ (.pi D E) = some (i,p) := by
        rw [support,if_pos hg,if_neg hd,hi]; rfl
      rcases hb i p hh with ⟨j,hj,he⟩ | he
      · left
        exact ⟨j+1,by rw [Expr.liftSub_succ,hj]; rfl,he⟩
      · exact .inr he

noncomputable def chosenBit (Γ : List (Expr S)) (A : Expr S) : Bool :=
  match support (P := P) C Γ A with
  | some (0,p) => p
  | _ => true

theorem bits_single (Γ : List (Expr S)) (A N : Expr S) (θ : Bits) :
    CompatibleBits (support (P := P) C Γ A) false (Expr.single N) (extendBit θ (chosenBit (P := P) C Γ A)) θ := by
  intro i p hi
  cases i with
  | zero =>
    right
    simp only [extendBit,chosenBit,hi,Bool.false_xor]
  | succ i => exact .inl ⟨i,rfl,rfl⟩

end

section
universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))
variable (hw : SystemWeaklyNormalizing P)
include hw

theorem subst_profile_path {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (hΔ : ValidContext P Δ) (δ : Nat → Expr S)
    (hδ : TypedSubstitution P Γ Δ δ) :
    PositivePath (PrimaryEdge P) (Profile P Δ (A.subst δ)) (Profile P Γ A) :=
  Profile.inclusion_path
    (Profile.feasible ((hA.subst hΔ δ hδ).weaklyNormalizing hw) (Profile.nonempty_of_sorted hw (hA.subst hΔ δ hδ)))
    (Profile.feasible (hA.weaklyNormalizing hw) (Profile.nonempty_of_sorted hw hA))
    (Profile.growth hw (hA.weaklyNormalizing hw) hΔ δ hδ)

theorem neutral_compare {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (hΔ : ValidContext P Δ) (δ : Nat → Expr S)
    (hδ : TypedSubstitution P Γ Δ δ) (e : Environment Ω Δ) (θ : Bits) (dir : Bool) {i : Nat}
    (hi : head A = some i) (hg : Profile P Γ A ∈ C)
    (hp : Profile P Δ (A.subst δ) ∈ C)
    (ha : Ω.profile (A.subst (fun i => (δ i).subst e.images)) ∈ C)
    (hb : CompatibleBits (support (P := P) C Γ A) dir δ θ e.bits) :
    Below dir (eval Ω C Γ A (fun i => (δ i).subst e.images) θ) (R Ω C (A.subst δ) e) := by
  have ht := hA.subst hΔ δ hδ
  have hcomp : ((A.subst δ).subst e.images) = A.subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
  have hc := R_candidate Ω C hw (.sorted ht) e
  rw [hcomp] at hc
  rw [eval_head Ω C hg ha hi]
  rcases hb i false (support_head C hg hi) with ⟨j,hj,hbit⟩ | hbit
  · have hhead : head (A.subst δ).normalForm = some j :=
      head_normalForm (by rw [head_subst hi,hj]; rfl) (ht.weaklyNormalizing hw)
    have hnf := normal_subst_eq Ω hw (.sorted ht) e
    have ha' : Ω.profile (((A.subst δ).normalForm).subst e.images) ∈ C := by
      rw [←Ω.profile_normalForm (((A.subst δ).normalForm).subst e.images),hnf,Ω.profile_normalForm,hcomp]
      exact ha
    have he : R Ω C (A.subst δ) e =
        if e.bits j then Top Ω (A.subst (fun i => (δ i).subst e.images)).normalForm
        else Bottom Ω (A.subst (fun i => (δ i).subst e.images)).normalForm := by
      rw [R,eval_head Ω C (by rwa [Profile.normalForm]) ha' hhead,hnf,hcomp]
    rw [he,hbit]
    cases dir <;> exact Set.Subset.rfl
  · simp only [Bool.xor_false] at hbit
    rw [hbit]
    cases dir with
    | false => exact bottom_le hc
    | true => exact hc.upper

omit hw in
@[simp] theorem head_apps (M : Expr S) (ns : List (Expr S)) : head (M.apps ns) = head M := by
  induction ns generalizing M with
  | nil => rfl
  | cons n ns ih => exact ih _

omit hw in
theorem normal_app_head {Γ : List (Expr S)} {f n : Expr S} {s : S}
    (ht : HasType P Γ (.app f n) (.sort s)) (hn : Normal (.app f n)) :
    ∃ i, head (.app f n) = some i := by
  have hneutral {M : Expr S} (h : Neutral M) : ∃ i, head M = some i := by
    induction h with
    | var i => exact ⟨i,rfl⟩
    | app h ih => exact ih
  obtain ⟨s,he⟩ | h | ⟨D,E,he⟩ := ht.sorted_normal_shape hn
  · cases he
  · exact hneutral h
  · cases he

variable (hC : IsComponent (PrimaryEdge P) C)
variable (hno : ∀ {I J K}, ProfileTriple P I J K → I ∈ C → J ∈ C → K ∈ C → False)
include hC hno hw

/-- The one-child polarity comparison at a generic normal type. The post-type
may have arbitrary newly exposed normal constructors. -/
theorem compare_subst {Γ Δ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (hN : Normal A)
    (hrel : ∃ K ∈ C, Reach (PrimaryEdge P) (Profile P Γ A) K)
    (hΔ : ValidContext P Δ) (δ : Nat → Expr S) (hδ : TypedSubstitution P Γ Δ δ)
    (e : Environment Ω Δ) (θ : Bits) (dir : Bool)
    (hb : CompatibleBits (support (P := P) C Γ A) dir δ θ e.bits) :
    Below dir (eval Ω C Γ A (fun i => (δ i).subst e.images) θ) (R Ω C (A.subst δ) e) := by
  induction A generalizing Γ Δ s δ θ dir with
  | var i =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.var i).subst δ).subst e.images) = (Expr.var i).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.profile_subst_path hw ht e.typed
    have hpg := subst_profile_path hw hA hΔ δ hδ
    by_cases ha : Ω.profile ((Expr.var i).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : Profile P Γ (Expr.var i) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : Profile P Δ ((Expr.var i).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach
    exact neutral_compare Ω C hw hA hΔ δ hδ e θ dir rfl hg hp ha hb
  | app f n ihf ihn =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.app f n).subst δ).subst e.images) = (Expr.app f n).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.profile_subst_path hw ht e.typed
    have hpg := subst_profile_path hw hA hΔ δ hδ
    by_cases ha : Ω.profile ((Expr.app f n).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : Profile P Γ (Expr.app f n) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : Profile P Δ ((Expr.app f n).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach

    obtain ⟨i,hi⟩ := normal_app_head hA hN
    exact neutral_compare Ω C hw hA hΔ δ hδ e θ dir hi hg hp ha hb
  | sort a =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.sort a).subst δ).subst e.images) = (Expr.sort a).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.profile_subst_path hw ht e.typed
    have hpg := subst_profile_path hw hA hΔ δ hδ
    by_cases ha : Ω.profile ((Expr.sort a).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : Profile P Γ (Expr.sort a) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : Profile P Δ ((Expr.sort a).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach

    rw [eval_sort,Expr.subst,R_sort]
    cases dir <;> exact Set.Subset.rfl
  | lam D m ihD ihm =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.lam D m).subst δ).subst e.images) = (Expr.lam D m).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.profile_subst_path hw ht e.typed
    have hpg := subst_profile_path hw hA hΔ δ hδ
    by_cases ha : Ω.profile ((Expr.lam D m).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : Profile P Γ (Expr.lam D m) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : Profile P Δ ((Expr.lam D m).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach
    exact False.elim hA.lambda_cannot_have_sort_type
  | pi D E ihD ihE =>
    have ht := hA.subst hΔ δ hδ
    have he : (((Expr.pi D E).subst δ).subst e.images) = (Expr.pi D E).subst (fun i => (δ i).subst e.images) := Expr.subst_subst _ _ _
    have hpa := Ω.profile_subst_path hw ht e.typed
    have hpg := subst_profile_path hw hA hΔ δ hδ
    by_cases ha : Ω.profile ((Expr.pi D E).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg : Profile P Γ (Expr.pi D E) ∈ C := by
      obtain ⟨K,hK,hpath⟩ := hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp : Profile P Δ ((Expr.pi D E).subst δ) ∈ C := by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach

    obtain ⟨a,b,c,hD,hE,hr,_⟩ := hA.generation_pi
    have hDn := hN.pi_domain
    have hEn := hN.pi_body
    have tr := Profile.triple hw hA
    have relD : ∃ K ∈ C, Reach (PrimaryEdge P) (Profile P Γ D) K := ⟨_,hg,.single (.domain tr)⟩
    have relE : ∃ K ∈ C, Reach (PrimaryEdge P) (Profile P (D :: Γ) E) K := ⟨_,hg,.single (.codomain tr)⟩
    have hδD := hD.subst hΔ δ hδ
    have dom := ihD hD hDn relD hΔ δ hδ e θ (!dir) (bits_domain C hg hb)
    have body (n : Expr S) (hn : n ∈ R Ω C (D.subst δ) e) (bit : Bool) :
        Below dir (eval Ω C (D :: Γ) E (Expr.extend (fun i => (δ i).subst e.images) n) (extendBit θ bit))
          (eval Ω C (D.subst δ :: Δ) (E.subst (Expr.liftSub δ)).normalForm
            (Expr.extend e.images n) (extendBit e.bits bit)) := by
      have hrawD := ContextTower.HasType.subst hδD e.typed
      have hnt := ((R_candidate Ω C hw (.sorted hδD) e).upper hn).1.conversion hrawD
        (.symm _ _ (Expr.normalForm_spec (hrawD.weaklyNormalizing hw)).1.converts)
      let f : Environment Ω (D.subst δ :: Δ) := ⟨Expr.extend e.images n,e.typed.cons hnt,extendBit e.bits bit⟩
      have hbody := ihE hE hEn relE (.cons hΔ hδD) (Expr.liftSub δ) (hδ.lift hδD)
        f (extendBit θ bit) dir (bits_body C hw hno hA hg hb bit)
      have hei : (fun i => (Expr.liftSub δ i).subst f.images) = Expr.extend (fun i => (δ i).subst e.images) n := by
        funext i
        cases i with
        | zero => rfl
        | succ i => exact Expr.subst_raise_extend (δ i) n e.images
      rw [hei] at hbody
      exact hbody
    rw [eval_pi,if_pos ⟨hg,ha⟩,R,Expr.subst,normal_product Ω C hw ht _ e.typed e.bits,if_pos ⟨hp,by change Ω.profile (((Expr.pi D E).subst δ).subst e.images) ∈ C; rwa [he]⟩]
    change Below dir (RawProduct Ω D E _ _ _) (RawProduct Ω (D.subst δ) (E.subst (Expr.liftSub δ)) e.images _ _)
    have hraw : ((Expr.pi (D.subst δ) (E.subst (Expr.liftSub δ))).subst e.images).normalForm =
        ((Expr.pi D E).subst (fun i => (δ i).subst e.images)).normalForm := congrArg Expr.normalForm he
    cases dir with
    | false =>
      intro h hh
      refine ⟨hraw.symm ▸ hh.1,?_⟩
      intro n hn bit
      exact body n hn bit (hh.2 n (dom hn) bit)
    | true =>
      intro h hh
      refine ⟨hraw ▸ hh.1,?_⟩
      intro n hn bit
      exact body n (dom hn) bit (hh.2 n (dom hn) bit)

end

universe u
open Classical Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (C : Set (Set S))
variable (hw : SystemWeaklyNormalizing P) (hC : IsComponent (PrimaryEdge P) C)
variable (hno : ∀ {I J K}, ProfileTriple P I J K → I ∈ C → J ∈ C → K ∈ C → False)
include hw hC hno

theorem specialization {Γ : List (Expr S)} {D E N : Expr S} {s : S}
    (e : Environment Ω Γ) (hp : HasType P Γ (.pi D E) (.sort s))
    (hN : HasType P Γ N D) (hg : Profile P Γ (.pi D E) ∈ C)
    (ha : Ω.profile ((Expr.pi D E).subst e.images) ∈ C) (h : Expr S)
    (hh : h ∈ R Ω C (.pi D E) e) (hn : N.subst e.images ∈ R Ω C D e) :
    Expr.app h (N.subst e.images) ∈ R Ω C (E.instantiate N) e := by
  obtain ⟨a,b,c,hD,hE,hr,_⟩ := hp.generation_pi
  let bit := chosenBit (P := P) C (D :: Γ) E.normalForm
  let f : Environment Ω (D :: Γ) := ⟨Expr.extend e.images (N.subst e.images),
    e.typed.cons (ContextTower.HasType.subst hN e.typed),extendBit e.bits bit⟩
  have hm := ((product_iff Ω C hw hp hg e ha h).mp hh).2 (N.subst e.images) hn f ⟨rfl,fun _ => rfl⟩
  have hrel : ∃ K ∈ C, Reach (PrimaryEdge P) (Profile P (D :: Γ) E.normalForm) K := by
    rw [Profile.normalForm]
    exact ⟨_,hg,.single (.codomain (Profile.triple hw hp))⟩
  have hc := compare_subst Ω C hw hC hno (hE.normalForm hw)
    (Expr.normalForm_spec (hE.weaklyNormalizing hw)).2 hrel hD.valid (Expr.single N)
    (TypedSubstitution.single hN) e f.bits false (bits_single C (D :: Γ) E.normalForm N e.bits)
  have he : (fun i => (Expr.single N i).subst e.images) = f.images := by
    funext i; cases i <;> rfl
  rw [he] at hc
  have hout := hc hm
  have ht := hE.instantiate hN
  have ht' := (hE.normalForm hw).instantiate hN
  have cE := (Expr.normalForm_spec (hE.weaklyNormalizing hw)).1.converts.subst (Expr.single N)
  exact (R_conversion Ω C hw (.sorted ht) (.sorted ht') cE e).symm ▸ hout

/-- One-child components need no relational exclusion: both fresh extremes
are tested, and polarity selects one of those tests at specialization. -/
noncomputable def componentInterface : ComponentInterface Ω hw C where
  Env := Environment Ω
  images := Environment.images
  typed := Environment.typed
  inhabit σ hσ := ⟨⟨σ,hσ,fun _ => false⟩,rfl⟩
  Ext := Environment.Ext
  ext_images he := he.1
  extend e _ n hn := ⟨⟨Expr.extend e.images n,e.typed.cons hn,extendBit e.bits false⟩,rfl,fun _ => rfl⟩
  R := R Ω C
  candidate e hA := R_candidate Ω C hw hA e
  conversion e ha hb hc := R_conversion Ω C hw ha hb hc e
  outside e ht ho := R_outside Ω C hw ht e ho
  weakening hd he hx := R_weakening Ω C hw hd he hx
  product_intro e hp hg ha h ht hb := (product_iff Ω C hw hp hg e ha h).mpr ⟨ht,hb⟩
  specialization e hp hN hg ha h hh hn := specialization Ω C hw hC hno e hp hN hg ha h hh hn

end S_wpc_barendregt_geuvers_klop.OneChildInterpretation

end OMA

namespace OMA.S_wpc_barendregt_geuvers_klop
universe u
private theorem feq {S : Type u} (P : Specification S) :
    (fun (i : Set S) => i.Nonempty ∧ ∃ Γ t, ValidContext P Γ ∧ Normal t ∧ i = {s | HasType P Γ t (.sort s)}) = FeasibleProfile P := by
  funext i
  apply propext
  constructor <;> rintro ⟨hn,Γ,t,hg,ht,he⟩ <;> refine ⟨hn,Γ,t,hg,ht,?_⟩ <;> simpa [Profile,Expr.normalForm_of_normal ht] using he.symm
private theorem teq {S : Type u} (P : Specification S) :
    (fun (i j k : Set S) => FeasibleProfile P i ∧ FeasibleProfile P j ∧ FeasibleProfile P k ∧ k = {c | ∃ a ∈ i, ∃ b ∈ j, P.rule a b c}) = ProfileTriple P := by
  funext i j k; apply propext
  constructor <;> rintro ⟨a,b,c,d⟩ <;> exact ⟨a,b,c,d⟩
private theorem eeq {S : Type u} (P : Specification S) :
    (fun (i k : Set S) (p : Bool) => if p then ∃ j, ProfileTriple P i j k else (FeasibleProfile P i ∧ FeasibleProfile P k ∧ k ⊂ i) ∨ ∃ j, ProfileTriple P j i k) = PrimaryEdge P := by
  funext i k p; apply propext; cases p
  · constructor
    · rintro (⟨a,b,c⟩ | ⟨j,hj⟩); exact .inclusion a b c; exact .codomain hj
    · intro h; cases h with
      | inclusion a b c => exact Or.inl ⟨a,b,c⟩
      | codomain h => exact Or.inr ⟨_,h⟩
  · constructor
    · rintro ⟨j,hj⟩; exact .domain hj
    · intro h; cases h with | domain h => exact ⟨_,h⟩
private theorem peq {V : Type u} :
    (fun (e : V → V → Bool → Prop) (i j : V) (b : Bool) => ∀ R : V → V → Bool → Prop, (∀ x, R x x false) → (∀ x y z p q, e x y p → R y z q → R x z (p.xor q)) → R i j b) = SignedPath := by
  funext e i j b; apply propext
  constructor
  · intro h; exact h _ SignedPath.nil (fun _ _ _ _ _ a c => .cons a c)
  · intro h R hn hc; induction h with
    | nil x => exact hn x
    | cons h _ ih => exact hc _ _ _ _ _ h ih
end OMA.S_wpc_barendregt_geuvers_klop
open OMA.S_wpc_barendregt_geuvers_klop
theorem OMA.solution : OMA.R_wpc_barendregt_geuvers_klop_R1_H2_R1.H1 := by
  intro n P hw
  let V := Set (Fin n)
  let critP (T : V → V → V → Prop) (E : V → V → Bool → Prop) (Path : (V → V → Bool → Prop) → V → V → Bool → Prop) :=
    let Cmp := fun e (C : Set V) => ∃ r ∈ C, ∀ v, v ∈ C ↔ (∃ b, Path e r v b) ∧ ∃ b, Path e v r b
    ∃ C, Cmp E C ∧ (∃ i ∈ C, Path E i i true) ∧ (∃ i ∈ C, ∃ j ∈ C, ∃ k ∈ C, T i j k)
  let F := fun (i : V) => i.Nonempty ∧ ∃ Γ t, ValidContext P Γ ∧ Normal t ∧ i = {s | HasType P Γ t (.sort s)}
  let T := fun (i j k : V) => F i ∧ F j ∧ F k ∧ k = {c | ∃ a ∈ i, ∃ b ∈ j, P.rule a b c}
  let E := fun (i k : V) (p : Bool) => if p then ∃ j, T i j k else (F i ∧ F k ∧ k ⊂ i) ∨ ∃ j, T j i k
  let Path := fun (e : V → V → Bool → Prop) (i j : V) (b : Bool) =>
    ∀ R : V → V → Bool → Prop, (∀ x, R x x false) → (∀ x y z p q, e x y p → R y z q → R x z (p.xor q)) → R i j b
  change ¬ critP T E Path → _
  have hF : F = FeasibleProfile P := feq P
  have hT : T = ProfileTriple P := by dsimp only [T]; rw [hF]; exact teq P
  have hE : E = PrimaryEdge P := by dsimp only [E]; rw [hT,hF]; exact eeq P
  have hP : Path = SignedPath := peq
  rw [hT,hE,hP]
  intro hn Γ f a D E hf ha sf sa
  obtain ⟨s,t,hat⟩ := hf.has_axiom
  let Ω := ContextTowerConstruction.tower P hat
  apply application_sn_of_ground Ω hw _ hf ha sf sa
  apply all_ground_eq_top Ω hw
  intro C hC
  by_cases ho : ∃ I ∈ C, SignedPath (PrimaryEdge P) I I true
  · refine ⟨OneChildInterpretation.componentInterface Ω C hw hC ?_⟩
    intro I J K ht hi hj hk
    exact hn ⟨C,hC,ho,I,hi,J,hj,K,hk,ht⟩
  · exact ⟨SignedInterpretation.componentInterface Ω hC hw (fun I hi hp => ho ⟨I,hi,hp⟩)⟩
