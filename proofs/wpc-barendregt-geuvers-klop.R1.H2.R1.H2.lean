import OMAReductions.R_wpc_barendregt_geuvers_klop_R1_H2_R1
/- Adapted from OpenAI openai/math, commit 3344da59991ed94f9ba711217b29c1d760badfa6, lean/OAI/Computability/TypeSystem, Apache-2.0. -/
namespace OMA
namespace S_wpc_barendregt_geuvers_klop
universe u
namespace Expr
variable {S:Type u}
@[simp] theorem liftRen_zero (ρ:Nat → Nat):liftRen ρ 0 = 0:=rfl
@[simp] theorem liftRen_succ (ρ:Nat → Nat) (n:Nat) :
    liftRen ρ (n + 1) = ρ n + 1:=rfl
@[simp] theorem liftRen_id:liftRen id = id:=by
  funext n
  cases n <;> rfl
theorem liftRen_comp (ρ τ:Nat → Nat):liftRen (ρ ∘ τ) = liftRen ρ ∘ liftRen τ:=by
  funext n
  cases n <;> rfl
@[simp] theorem rename_id (M:Expr S):rename id M = M:=by
  induction M with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [rename,ihf,iha]
  | lam A b ihA ihb => simp [rename,ihA,ihb]
  | pi A B ihA ihB => simp [rename,ihA,ihB]
theorem rename_comp (M:Expr S) (ρ τ:Nat → Nat) :
    rename ρ (rename τ M) = rename (ρ ∘ τ) M:=by
  induction M generalizing ρ τ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [rename,ihf,iha]
  | lam A b ihA ihb => simp only [rename,ihA,ihb,liftRen_comp]
  | pi A B ihA ihB => simp only [rename,ihA,ihB,liftRen_comp]
@[simp] theorem liftSub_zero (σ:Nat → Expr S):liftSub σ 0 = var 0:=rfl
@[simp] theorem liftSub_succ (σ:Nat → Expr S) (n:Nat) :
    liftSub σ (n + 1) = rename Nat.succ (σ n):=rfl
@[simp] theorem liftSub_var:liftSub (var:Nat → Expr S) = var:=by
  funext n
  cases n <;> rfl
@[simp] theorem subst_var (M:Expr S):subst var M = M:=by
  induction M with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp [subst,ihf,iha]
  | lam A b ihA ihb => simp [subst,ihA,ihb]
  | pi A B ihA ihB => simp [subst,ihA,ihB]
theorem subst_rename (M:Expr S) (σ:Nat → Expr S) (ρ:Nat → Nat) :
    subst σ (rename ρ M) = subst (σ ∘ ρ) M:=by
  have hlift:∀ (σ:Nat → Expr S) (ρ:Nat → Nat),
      liftSub σ ∘ liftRen ρ = liftSub (σ ∘ ρ):=by
    intro σ ρ
    funext n
    cases n <;> rfl
  induction M generalizing σ ρ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [rename,subst,ihf,iha]
  | lam A b ihA ihb => simp only [rename,subst,ihA,ihb,hlift]
  | pi A B ihA ihB => simp only [rename,subst,ihA,ihB,hlift]
theorem rename_subst (M:Expr S) (ρ:Nat → Nat) (σ:Nat → Expr S) :
    rename ρ (subst σ M) = subst (fun n => rename ρ (σ n)) M:=by
  have hlift:∀ (ρ:Nat → Nat) (σ:Nat → Expr S),
      (fun n => rename (liftRen ρ) (liftSub σ n)) =
        liftSub (fun n => rename ρ (σ n)):=by
    intro ρ σ
    funext n
    cases n with
    | zero => rfl
    | succ n =>
        simp only [liftSub_succ,rename_comp]
        rfl
  induction M generalizing ρ σ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [subst,rename,ihf,iha]
  | lam A b ihA ihb => simp only [subst,rename,ihA,ihb,hlift]
  | pi A B ihA ihB => simp only [subst,rename,ihA,ihB,hlift]
theorem subst_subst (M:Expr S) (σ τ:Nat → Expr S) :
    subst σ (subst τ M) = subst (fun n => subst σ (τ n)) M:=by
  have hlift:∀ (σ τ:Nat → Expr S),
      (fun n => subst (liftSub σ) (liftSub τ n)) =
        liftSub (fun n => subst σ (τ n)):=by
    intro σ τ
    funext n
    cases n with
    | zero => rfl
    | succ n =>
        simp only [liftSub_succ,subst_rename,rename_subst]
        rfl
  induction M generalizing σ τ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [subst,ihf,iha]
  | lam A b ihA ihb => simp only [subst,ihA,ihb,hlift]
  | pi A B ihA ihB => simp only [subst,ihA,ihB,hlift]
theorem instantiate_rename (b a:Expr S) (ρ:Nat → Nat) :
    (b.rename (liftRen ρ)).instantiate (a.rename ρ) = (b.instantiate a).rename ρ:=by
  simp only [instantiate,subst_rename,rename_subst]
  congr 1
  funext n
  cases n <;> rfl
theorem instantiate_subst (b a:Expr S) (σ:Nat → Expr S) :
    (b.subst (liftSub σ)).instantiate (a.subst σ) = (b.instantiate a).subst σ:=by
  simp only [instantiate,subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [liftSub_succ,subst_rename]
      exact subst_var (σ n)
end Expr
namespace Beta
variable {S:Type u} {M N:Expr S}
theorem rename (h:Beta M N) (ρ:Nat → Nat):Beta (M.rename ρ) (N.rename ρ):=by
  induction h generalizing ρ with
  | head A b a =>
      simpa only [Expr.rename,← Expr.instantiate_rename] using
        (Beta.head (A.rename ρ) (b.rename (Expr.liftRen ρ)) (a.rename ρ))
  | app_left _ ih => exact .app_left (ih ρ)
  | app_right _ ih => exact .app_right (ih ρ)
  | lam_domain _ ih => exact .lam_domain (ih ρ)
  | lam_body _ ih => exact .lam_body (ih (Expr.liftRen ρ))
  | pi_domain _ ih => exact .pi_domain (ih ρ)
  | pi_body _ ih => exact .pi_body (ih (Expr.liftRen ρ))
theorem subst (h:Beta M N) (σ:Nat → Expr S):Beta (M.subst σ) (N.subst σ):=by
  induction h generalizing σ with
  | head A b a =>
      simpa only [Expr.subst,← Expr.instantiate_subst] using
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
inductive Parallel {S:Type u}:Expr S → Expr S → Prop
  | var (n):Parallel (.var n) (.var n)
  | sort (s):Parallel (.sort s) (.sort s)
  | app {f f' a a'}:Parallel f f' → Parallel a a' →
      Parallel (.app f a) (.app f' a')
  | lam {A A' b b'}:Parallel A A' → Parallel b b' →
      Parallel (.lam A b) (.lam A' b')
  | pi {A A' B B'}:Parallel A A' → Parallel B B' →
      Parallel (.pi A B) (.pi A' B')
  | head {b b' a a'} (A):Parallel b b' → Parallel a a' →
      Parallel (.app (.lam A b) a) (b'.instantiate a')
namespace Parallel
variable {S:Type u} {M N:Expr S}
theorem refl (M:Expr S):Parallel M M:=by
  induction M with
  | var n => exact .var n
  | sort s => exact .sort s
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ ihA ihB => exact .pi ihA ihB
theorem of_beta (h:Beta M N):Parallel M N:=by
  induction h with
  | head A b a => exact .head A (refl b) (refl a)
  | app_left _ ih => exact .app ih (refl _)
  | app_right _ ih => exact .app (refl _) ih
  | lam_domain _ ih => exact .lam ih (refl _)
  | lam_body _ ih => exact .lam (refl _) ih
  | pi_domain _ ih => exact .pi ih (refl _)
  | pi_body _ ih => exact .pi (refl _) ih
theorem rename (h:Parallel M N) (ρ:Nat → Nat) :
    Parallel (M.rename ρ) (N.rename ρ):=by
  induction h generalizing ρ with
  | var n => exact .var _
  | sort s => exact .sort _
  | app _ _ ihf iha => exact .app (ihf ρ) (iha ρ)
  | lam _ _ ihA ihb => exact .lam (ihA ρ) (ihb (Expr.liftRen ρ))
  | pi _ _ ihA ihB => exact .pi (ihA ρ) (ihB (Expr.liftRen ρ))
  | head A _ _ ihb iha =>
      simpa only [Expr.rename,← Expr.instantiate_rename] using
        (Parallel.head (A.rename ρ) (ihb (Expr.liftRen ρ)) (iha ρ))
theorem subst (h:Parallel M N) (σ τ:Nat → Expr S)
    (hστ:∀ n,Parallel (σ n) (τ n)):Parallel (M.subst σ) (N.subst τ):=by
  have hlift (σ τ:Nat → Expr S) (hστ:∀ n,Parallel (σ n) (τ n)) :
      ∀ n,Parallel (Expr.liftSub σ n) (Expr.liftSub τ n):=by
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
      simpa only [Expr.subst,← Expr.instantiate_subst] using
        (Parallel.head (A.subst σ) (ihb _ _ (hlift σ τ hστ)) (iha σ τ hστ))
theorem instantiate {b b' a a':Expr S} (hb:Parallel b b') (ha:Parallel a a') :
    Parallel (b.instantiate a) (b'.instantiate a'):=by
  apply hb.subst
  intro n
  cases n with
  | zero => exact ha
  | succ n => exact .var n
end Parallel
namespace Expr
variable {S:Type u}
def develop:Expr S → Expr S
  | var n => var n
  | sort s => sort s
  | app (lam _ b) a => (develop b).instantiate (develop a)
  | app f a => app (develop f) (develop a)
  | lam A b => lam (develop A) (develop b)
  | pi A B => pi (develop A) (develop B)
end Expr
namespace Parallel
variable {S:Type u} {M N:Expr S}
theorem triangle (h:Parallel M N):Parallel N M.develop:=by
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
theorem diamond {a b c:Expr S} (hab:Parallel a b) (hac:Parallel a c) :
    ∃ d,Parallel b d ∧ Parallel c d:=⟨a.develop,hab.triangle,hac.triangle⟩
end Parallel
abbrev Reduces {S:Type u}:=Relation.ReflTransGen (@Beta S)
namespace Reduces
variable {S:Type u} {f f' a a' A A' b b':Expr S}
theorem app (hf:Reduces f f') (ha:Reduces a a') :
    Reduces (.app f a) (.app f' a'):=by
  exact (hf.lift (fun x => Expr.app x a) (fun _ _ h => Beta.app_left h)).trans
    (ha.lift (fun x => Expr.app f' x) (fun _ _ h => Beta.app_right h))
theorem lam (hA:Reduces A A') (hb:Reduces b b') :
    Reduces (.lam A b) (.lam A' b'):=by
  exact (hA.lift (fun x => Expr.lam x b) (fun _ _ h => Beta.lam_domain h)).trans
    (hb.lift (fun x => Expr.lam A' x) (fun _ _ h => Beta.lam_body h))
theorem pi (hA:Reduces A A') (hb:Reduces b b') :
    Reduces (.pi A b) (.pi A' b'):=by
  exact (hA.lift (fun x => Expr.pi x b) (fun _ _ h => Beta.pi_domain h)).trans
    (hb.lift (fun x => Expr.pi A' x) (fun _ _ h => Beta.pi_body h))
theorem rename {M N:Expr S} (h:Reduces M N) (ρ:Nat → Nat) :
    Reduces (M.rename ρ) (N.rename ρ):=h.lift _ (fun _ _ h => h.rename ρ)
theorem subst {M N:Expr S} (h:Reduces M N) (σ:Nat → Expr S) :
    Reduces (M.subst σ) (N.subst σ):=h.lift _ (fun _ _ h => h.subst σ)
end Reduces
namespace Parallel
variable {S:Type u} {M N:Expr S}
theorem reduces (h:Parallel M N):Reduces M N:=by
  induction h with
  | var n => exact .refl
  | sort s => exact .refl
  | app _ _ ihf iha => exact Reduces.app ihf iha
  | lam _ _ ihA ihb => exact Reduces.lam ihA ihb
  | pi _ _ ihA ihB => exact Reduces.pi ihA ihB
  | head A _ _ ihb iha =>
      exact (Reduces.app (Reduces.lam .refl ihb) iha).tail (.head _ _ _)
theorem rtc_reduces {M N:Expr S} (h:Relation.ReflTransGen Parallel M N) :
    Reduces M N:=Relation.reflTransGen_closed (fun _ _ h => h.reduces) _ _ h
end Parallel
namespace Reduces
variable {S:Type u} {M N:Expr S}
theorem parallel (h:Reduces M N):Relation.ReflTransGen Parallel M N :=
  Relation.ReflTransGen.mono (fun _ _ h => Parallel.of_beta h) _ _ h
theorem confluent {a b c:Expr S} (hab:Reduces a b) (hac:Reduces a c) :
    Relation.Join Reduces b c:=by
  have hd:∀ a b c:Expr S,Parallel a b → Parallel a c →
      ∃ d,Relation.ReflGen Parallel b d ∧ Relation.ReflTransGen Parallel c d:=by
    intro a b c hab hac
    obtain ⟨d,hb,hc⟩:=Parallel.diamond hab hac
    exact ⟨d,.single hb,.single hc⟩
  obtain ⟨d,hb,hc⟩:=Relation.church_rosser hd hab.parallel hac.parallel
  exact ⟨d,Parallel.rtc_reduces hb,Parallel.rtc_reduces hc⟩
end Reduces
namespace Converts
variable {S:Type u} {M N:Expr S}
theorem join (h:Converts M N):Relation.Join Reduces M N:=by
  induction h with
  | rel a b h => exact ⟨b,.single h,.refl⟩
  | refl a => exact ⟨a,.refl,.refl⟩
  | symm a b _ ih =>
      obtain ⟨c,ha,hb⟩:=ih
      exact ⟨c,hb,ha⟩
  | trans a b c _ _ ih₁ ih₂ =>
      obtain ⟨d,ha,hb⟩:=ih₁
      obtain ⟨e,hb',hc⟩:=ih₂
      obtain ⟨f,hd,he⟩:=Reduces.confluent hb hb'
      exact ⟨f,ha.trans hd,hc.trans he⟩
end Converts
namespace Normal
variable {S:Type u} {M N:Expr S}
theorem reduces_eq (hM:Normal M) (h:Reduces M N):M = N:=by
  induction h with
  | refl => rfl
  | @tail N N' _ h ih => exact False.elim (hM N' (ih ▸ h))
theorem eq_of_converts (hM:Normal M) (hN:Normal N) (h:Converts M N):M = N:=by
  obtain ⟨K,hMK,hNK⟩:=h.join
  exact (hM.reduces_eq hMK).trans (hN.reduces_eq hNK).symm
end Normal
namespace Reduces
variable {S:Type u} {A B N:Expr S}
theorem pi_inv (h:Reduces (.pi A B) N) :
    ∃ A' B',N = .pi A' B' ∧ Reduces A A' ∧ Reduces B B':=by
  induction h with
  | refl => exact ⟨A,B,rfl,.refl,.refl⟩
  | tail _ h ih =>
      obtain ⟨A',B',rfl,hA,hB⟩:=ih
      cases h with
      | pi_domain h => exact ⟨_,_,rfl,hA.tail h,hB⟩
      | pi_body h => exact ⟨_,_,rfl,hA,hB.tail h⟩
theorem converts {M N:Expr S} (h:Reduces M N):Converts M N :=
  Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ h
end Reduces
namespace Converts
variable {S:Type u}
theorem product_compatibility {A B A' B':Expr S}
    (h:Converts (.pi A B) (.pi A' B')):Converts A A' ∧ Converts B B':=by
  obtain ⟨T,hT,hT'⟩:=h.join
  obtain ⟨D,E,hDE,hA,hB⟩:=hT.pi_inv
  obtain ⟨D',E',hDE',hA',hB'⟩:=hT'.pi_inv
  have heq:=Expr.pi.inj (hDE.symm.trans hDE')
  obtain ⟨rfl,rfl⟩:=heq
  exact ⟨.trans _ _ _ hA.converts (.symm _ _ hA'.converts),
    .trans _ _ _ hB.converts (.symm _ _ hB'.converts)⟩
end Converts
namespace StronglyNormalizing
variable {S:Type u} {M N:Expr S}
theorem step (hM:StronglyNormalizing M) (h:Beta M N):StronglyNormalizing N :=
  hM.inv h
theorem reduces (hM:StronglyNormalizing M) (h:Reduces M N):StronglyNormalizing N:=by
  induction h with
  | refl => exact hM
  | tail _ h ih => exact ih.step h
theorem of_map {f:Expr S → Expr S}
    (hf:∀ {M N},Beta M N → Beta (f M) (f N)) {M:Expr S}
    (h:StronglyNormalizing (f M)):StronglyNormalizing M:=by
  have aux:∀ N,StronglyNormalizing N → ∀ M,f M = N → StronglyNormalizing M:=by
    intro N hN
    induction hN with
    | intro N _ ih =>
        intro M heq
        apply Acc.intro
        intro M' hM
        exact ih (f M') (heq ▸ hf hM) M' rfl
  exact aux _ h M rfl
theorem app_left {f a:Expr S} (h:StronglyNormalizing (.app f a)) :
    StronglyNormalizing f:=of_map (fun h => Beta.app_left h) h
theorem app_right {f a:Expr S} (h:StronglyNormalizing (.app f a)) :
    StronglyNormalizing a:=of_map (fun h => Beta.app_right h) h
theorem lam_domain {A b:Expr S} (h:StronglyNormalizing (.lam A b)) :
    StronglyNormalizing A:=of_map (fun h => Beta.lam_domain h) h
theorem lam_body {A b:Expr S} (h:StronglyNormalizing (.lam A b)) :
    StronglyNormalizing b:=of_map (fun h => Beta.lam_body h) h
theorem pi_domain {A B:Expr S} (h:StronglyNormalizing (.pi A B)) :
    StronglyNormalizing A:=of_map (fun h => Beta.pi_domain h) h
theorem pi_body {A B:Expr S} (h:StronglyNormalizing (.pi A B)) :
    StronglyNormalizing B:=of_map (fun h => Beta.pi_body h) h
theorem of_subst (σ:Nat → Expr S) (h:StronglyNormalizing (M.subst σ)) :
    StronglyNormalizing M:=of_map (fun h => h.subst σ) h
theorem of_rename (ρ:Nat → Nat) (h:StronglyNormalizing (M.rename ρ)) :
    StronglyNormalizing M:=of_map (fun h => h.rename ρ) h
theorem lam {A b:Expr S} (hA:StronglyNormalizing A) (hb:StronglyNormalizing b) :
    StronglyNormalizing (.lam A b):=by
  induction hA generalizing b with
  | intro A hA ihA =>
      induction hb with
      | intro b hb ihb =>
          apply Acc.intro
          intro N hN
          cases hN with
          | lam_domain h => exact ihA _ h (Acc.intro _ hb)
          | lam_body h => exact ihb _ h
theorem pi {A B:Expr S} (hA:StronglyNormalizing A) (hB:StronglyNormalizing B) :
    StronglyNormalizing (.pi A B):=by
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
variable {S:Type u}
def apps (f:Expr S):List (Expr S) → Expr S
  | [] => f
  | a :: as => apps (.app f a) as
@[simp] theorem apps_nil (f:Expr S):apps f [] = f:=rfl
@[simp] theorem apps_cons (f a:Expr S) (as:List (Expr S)) :
    apps f (a :: as) = apps (.app f a) as:=rfl
theorem apps_append (f:Expr S) (as bs:List (Expr S)) :
    apps f (as ++ bs) = apps (apps f as) bs:=by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact ih (.app f a)
end Expr
inductive ArgsStep {S:Type u}:List (Expr S) → List (Expr S) → Prop
  | head {a a' as}:Beta a a' → ArgsStep (a :: as) (a' :: as)
  | tail {a as as'}:ArgsStep as as' → ArgsStep (a :: as) (a :: as')
def StronglyNormalizingArgs {S:Type u} (as:List (Expr S)):Prop :=
  Acc (fun bs as => ArgsStep as bs) as
namespace Beta
variable {S:Type u} {f f':Expr S}
theorem apps (h:Beta f f') (as:List (Expr S)) :
    Beta (f.apps as) (f'.apps as):=by
  induction as generalizing f f' with
  | nil => exact h
  | cons a as ih => exact ih (.app_left h)
theorem apps_inv {as:List (Expr S)} {N:Expr S}
    (hf:∀ A b,f ≠ .lam A b) (h:Beta (f.apps as) N) :
    (∃ f',Beta f f' ∧ N = f'.apps as) ∨
    (∃ as',ArgsStep as as' ∧ N = f.apps as'):=by
  induction as generalizing f N with
  | nil => exact .inl ⟨N,h,rfl⟩
  | cons a as ih =>
      obtain ⟨g,hg,rfl⟩ | ⟨as',has,rfl⟩ :=
        ih (f:=.app f a) (by intro A b heq; cases heq) h
      · cases hg with
        | head A b a => exact False.elim (hf A b rfl)
        | app_left hg => exact .inl ⟨_,hg,rfl⟩
        | app_right hg => exact .inr ⟨_,.head hg,rfl⟩
      · exact .inr ⟨_,.tail has,rfl⟩
end Beta
namespace ArgsStep
variable {S:Type u} {as bs:List (Expr S)}
theorem apps (h:ArgsStep as bs) (f:Expr S):Beta (f.apps as) (f.apps bs):=by
  induction h generalizing f with
  | head h => exact (Beta.app_right h).apps _
  | tail h ih => exact ih (.app f _)
end ArgsStep
namespace Reduces
variable {S:Type u} {f f':Expr S}
theorem apps (h:Reduces f f') (as:List (Expr S)) :
    Reduces (f.apps as) (f'.apps as):=h.lift _ (fun _ _ h => h.apps as)
end Reduces
namespace StronglyNormalizingArgs
variable {S:Type u}
theorem nil:StronglyNormalizingArgs ([]:List (Expr S)):=by
  apply Acc.intro
  intro bs h
  cases h
theorem cons {a:Expr S} {as:List (Expr S)} (ha:StronglyNormalizing a)
    (has:StronglyNormalizingArgs as):StronglyNormalizingArgs (a :: as):=by
  induction ha generalizing as with
  | intro a ha iha =>
      induction has with
      | intro as has ihas =>
          apply Acc.intro
          intro bs h
          cases h with
          | head h => exact iha _ h (Acc.intro _ has)
          | tail h => exact ihas _ h
theorem of_forall {as:List (Expr S)} (h:∀ a ∈ as,StronglyNormalizing a) :
    StronglyNormalizingArgs as:=by
  induction as with
  | nil => exact nil
  | cons a as ih =>
      exact cons (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))
theorem head {a:Expr S} {as:List (Expr S)}
    (h:StronglyNormalizingArgs (a :: as)):StronglyNormalizing a :=
  Subrelation.accessible (fun h => ArgsStep.head h)
    (InvImage.accessible (fun a => a :: as) h)
theorem tail {a:Expr S} {as:List (Expr S)}
    (h:StronglyNormalizingArgs (a :: as)):StronglyNormalizingArgs as :=
  Subrelation.accessible (fun h => ArgsStep.tail h)
    (InvImage.accessible (fun as => a :: as) h)
theorem of_mem {a:Expr S} {as:List (Expr S)}
    (h:StronglyNormalizingArgs as) (ha:a ∈ as):StronglyNormalizing a:=by
  induction as with
  | nil => cases ha
  | cons b bs ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact h.head
      · exact ih h.tail ha
end StronglyNormalizingArgs
namespace StronglyNormalizing
variable {S:Type u}
theorem apps_head {f:Expr S} {as:List (Expr S)}
    (h:StronglyNormalizing (f.apps as)):StronglyNormalizing f :=
  of_map (fun h => h.apps as) h
theorem var_apps (n:Nat) {as:List (Expr S)} (has:StronglyNormalizingArgs as) :
    StronglyNormalizing ((Expr.var n:Expr S).apps as):=by
  induction has with
  | intro as has ih =>
      apply Acc.intro
      intro N hN
      obtain ⟨f,hf,rfl⟩ | ⟨bs,hbs,rfl⟩ :=
        hN.apps_inv (by intro A b heq; cases heq)
      · cases hf
      · exact ih _ hbs
theorem head_expansion {A b a:Expr S} {as:List (Expr S)}
    (hA:StronglyNormalizing A) (hb:StronglyNormalizing b)
    (ha:StronglyNormalizing a) (has:StronglyNormalizingArgs as)
    (hc:StronglyNormalizing ((b.instantiate a).apps as)) :
    StronglyNormalizing ((Expr.app (.lam A b) a).apps as):=by
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
                  obtain ⟨f,hf,rfl⟩ | ⟨bs,hbs,rfl⟩ :=
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
variable {S:Type u}
inductive Child:Expr S → Expr S → Prop
  | app_left (f a):Child f (.app f a)
  | app_right (f a):Child a (.app f a)
  | lam_domain (D m):Child D (.lam D m)
  | lam_body (D m):Child m (.lam D m)
  | pi_domain (D E):Child D (.pi D E)
  | pi_body (D E):Child E (.pi D E)
inductive Subterm:Expr S → Expr S → Prop
  | refl (M):Subterm M M
  | tail {M N L}:Subterm M N → Child N L → Subterm M L
namespace Child
variable {M N M':Expr S}
theorem beta_lift (h:Child M N) (hr:Beta M M') :
    ∃ N',Beta N N' ∧ Child M' N':=by
  cases h with
  | app_left f a => exact ⟨_,.app_left hr,.app_left _ _⟩
  | app_right f a => exact ⟨_,.app_right hr,.app_right _ _⟩
  | lam_domain D m => exact ⟨_,.lam_domain hr,.lam_domain _ _⟩
  | lam_body D m => exact ⟨_,.lam_body hr,.lam_body _ _⟩
  | pi_domain D E => exact ⟨_,.pi_domain hr,.pi_domain _ _⟩
  | pi_body D E => exact ⟨_,.pi_body hr,.pi_body _ _⟩
theorem sn (h:Child M N) (hs:StronglyNormalizing N):StronglyNormalizing M:=by
  cases h with
  | app_left => exact hs.app_left
  | app_right => exact hs.app_right
  | lam_domain => exact hs.lam_domain
  | lam_body => exact hs.lam_body
  | pi_domain => exact hs.pi_domain
  | pi_body => exact hs.pi_body
end Child
namespace Subterm
variable {M N L M':Expr S}
theorem trans (h:Subterm M N) (h':Subterm N L):Subterm M L:=by
  induction h' with
  | refl => exact h
  | tail _ hc ih => exact .tail ih hc
theorem of_child (h:Child M N):Subterm M N:=.tail (.refl M) h
theorem beta_lift (h:Subterm M N) (hr:Beta M M') :
    ∃ N',Beta N N' ∧ Subterm M' N':=by
  induction h with
  | refl => exact ⟨_,hr,.refl _⟩
  | tail h hc ih =>
    obtain ⟨N',hr',hs'⟩:=ih
    obtain ⟨L',hr'',hc'⟩:=hc.beta_lift hr'
    exact ⟨L',hr'',.tail hs' hc'⟩
theorem sn (h:Subterm M N) (hs:StronglyNormalizing N):StronglyNormalizing M:=by
  induction h with
  | refl => exact hs
  | tail h hc ih => exact ih (hc.sn hs)
end Subterm
end Expr
namespace StronglyNormalizing
variable {S:Type u}
theorem induction_subterms {Q:Expr S → Prop}
    (step:∀ M,StronglyNormalizing M → (∀ N,Beta M N → Q N) →
      (∀ N,Expr.Child N M → Q N) → Q M)
    {M:Expr S} (hs:StronglyNormalizing M):Q M:=by
  have aux:∀ M:Expr S,StronglyNormalizing M → ∀ N,Expr.Subterm N M → Q N:=by
    intro M hs
    induction hs with
    | intro M hred ih =>
      intro N
      have hreds (N:Expr S) (hNM:Expr.Subterm N M):∀ L,Beta N L → Q L:=by
        intro L hr
        obtain ⟨M',hr',hLM'⟩:=hNM.beta_lift hr
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
theorem induction_descendants {Q:Expr S → Prop}
    (step:∀ M,StronglyNormalizing M → (∀ N,Beta M N → Q N) →
      (∀ N,(∃ K,Expr.Child K M ∧ Expr.Subterm N K) → Q N) → Q M)
    {M:Expr S} (hs:StronglyNormalizing M):Q M:=by
  have h:Q M ∧ ∀ N,Expr.Subterm N M → Q N:=by
    apply induction_subterms (Q:=fun M => Q M ∧ ∀ N,Expr.Subterm N M → Q N) _ hs
    intro M hM hr hc
    have hq:Q M:=step M hM (fun N h => (hr N h).1) (by
      rintro N ⟨K,hK,hN⟩
      exact (hc K hK).2 N hN)
    refine ⟨hq,?_⟩
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
inductive Lookup {S:Type u}:List (Expr S) → Nat → Expr S → Prop
  | zero (A Γ):Lookup (A :: Γ) 0 (A.rename Nat.succ)
  | succ {Γ n A} (B):Lookup Γ n A → Lookup (B :: Γ) (n + 1) (A.rename Nat.succ)
namespace HasType
variable {S:Type u} {P:Specification S}
theorem sort_of_valid {Γ:List (Expr S)} (hΓ:ValidContext P Γ)
    {s t:S} (hst:P.sortAxioms s t):HasType P Γ (.sort s) (.sort t):=by
  induction hΓ with
  | nil => exact .ax hst
  | cons _ hA ih => exact .weaken ih hA
theorem product_domain {Γ:List (Expr S)} {M T:Expr S} (h:HasType P Γ M T) :
    ∀ A B,M = .pi A B → ∃ s,HasType P Γ A (.sort s):=by
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
          obtain ⟨rfl,rfl⟩:=Expr.pi.inj heq
          obtain ⟨t,ht⟩:=ihM D E rfl
          exact ⟨t,.weaken ht hC⟩
  | product hA hB hr ihA ihB =>
      intro A B heq
      cases heq
      exact ⟨_,hA⟩
  | abstraction hb hT ihb ihT => intro A B heq; cases heq
  | application hf ha ihf iha => intro A B heq; cases heq
  | conversion hM hB hconv ihM ihB => exact ihM
end HasType
namespace Converts
variable {S:Type u} {M N:Expr S}
theorem subst (h:Converts M N) (σ:Nat → Expr S) :
    Converts (M.subst σ) (N.subst σ):=by
  induction h with
  | rel a b h => exact .rel _ _ (h.subst σ)
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
theorem rename (h:Converts M N) (ρ:Nat → Nat) :
    Converts (M.rename ρ) (N.rename ρ):=by
  induction h with
  | rel a b h => exact .rel _ _ (h.rename ρ)
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
end Converts
def TySub {S:Type u} (P:Specification S)
    (Γ Δ:List (Expr S)) (σ:Nat → Expr S):Prop :=
  ∀ n A,Lookup Γ n A → HasType P Δ (σ n) (A.subst σ)
namespace TySub
variable {S:Type u} {P:Specification S} {Γ Δ:List (Expr S)}
    {σ:Nat → Expr S}
theorem tail {A:Expr S} (hσ:TySub P (A :: Γ) Δ σ) :
    TySub P Γ Δ (σ ∘ Nat.succ):=by
  intro n B hB
  have h:=hσ (n + 1) (B.rename Nat.succ) (.succ A hB)
  simpa only [Expr.subst_rename,Function.comp_def] using h
theorem lift {A:Expr S} {s:S} (hσ:TySub P Γ Δ σ)
    (hA:HasType P Δ (A.subst σ) (.sort s)) :
    TySub P (A :: Γ) (A.subst σ :: Δ) (Expr.liftSub σ):=by
  intro n B hn
  cases hn with
  | zero =>
      have ht:=HasType.var hA
      simpa only [Expr.liftSub_zero,Expr.subst_rename,Expr.rename_subst,
        Expr.liftSub_succ,Function.comp_def] using ht
  | succ C hn =>
      have ht:=HasType.weaken (hσ _ _ hn) hA
      simpa only [Expr.liftSub_succ,Expr.rename_subst,Expr.subst_rename,
        Function.comp_def] using ht
end TySub
namespace HasType
variable {S:Type u} {P:Specification S} {Γ:List (Expr S)} {M T:Expr S}
theorem subst (h:HasType P Γ M T) {Δ:List (Expr S)}
    (hΔ:ValidContext P Δ) (σ:Nat → Expr S) (hσ:TySub P Γ Δ σ) :
    HasType P Δ (M.subst σ) (T.subst σ):=by
  induction h generalizing Δ σ with
  | ax h => exact sort_of_valid hΔ h
  | var h ih => exact hσ _ _ (.zero _ _)
  | weaken hM hA ihM ihA =>
      simpa only [Expr.subst_rename] using ihM hΔ (σ ∘ Nat.succ) hσ.tail
  | product hA hB hr ihA ihB =>
      have hA':=ihA hΔ σ hσ
      exact .product hA' (ihB (.cons hΔ hA') _ (hσ.lift hA')) hr
  | @abstraction Γ A b B s hb hprod ihb ihprod =>
      have hprod':=ihprod hΔ σ hσ
      obtain ⟨t,hA'⟩:=hprod'.product_domain _ _ rfl
      exact .abstraction (ihb (.cons hΔ hA') _ (hσ.lift hA')) hprod'
  | application hf ha ihf iha =>
      simpa only [Expr.subst,Expr.instantiate_subst] using
        (HasType.application (ihf hΔ σ hσ) (iha hΔ σ hσ))
  | conversion hM hB hconv ihM ihB =>
      exact .conversion (ihM hΔ σ hσ) (ihB hΔ σ hσ) (hconv.subst σ)
end HasType
namespace Expr
variable {S:Type u}
theorem subst_var_rename (M:Expr S) (ρ:Nat → Nat) :
    M.subst (var ∘ ρ) = M.rename ρ:=by
  rw [← subst_rename,subst_var]
@[simp] theorem subst_lift_single (M a:Expr S) :
    (M.rename Nat.succ).subst (single a) = M:=by
  rw [subst_rename]
  exact subst_var M
end Expr
namespace HasType
variable {S:Type u} {P:Specification S}
theorem lookup {Γ:List (Expr S)} (hΓ:ValidContext P Γ)
    {n:Nat} {A:Expr S} (hn:Lookup Γ n A):HasType P Γ (.var n) A:=by
  induction hΓ generalizing n A with
  | nil => cases hn
  | cons hΓ hB ih =>
      cases hn with
      | zero => exact .var hB
      | succ _ hn => exact .weaken (ih hn) hB
end HasType
namespace TySub
variable {S:Type u} {P:Specification S}
theorem identity {Γ:List (Expr S)} (hΓ:ValidContext P Γ) :
    TySub P Γ Γ Expr.var:=by
  intro n A hn
  simpa only [Expr.subst_var] using HasType.lookup hΓ hn
theorem weaken {Γ:List (Expr S)} {A:Expr S} {s:S}
    (hA:HasType P Γ A (.sort s)) :
    TySub P Γ (A :: Γ) (Expr.var ∘ Nat.succ):=by
  intro n B hn
  simpa only [Expr.subst_var_rename,Function.comp_apply,Expr.rename] using
    (HasType.weaken (HasType.lookup hA.valid hn) hA)
theorem single {Γ:List (Expr S)} {a A:Expr S} (ha:HasType P Γ a A) :
    TySub P (A :: Γ) Γ (Expr.single a):=by
  intro n B hn
  cases hn with
  | zero => simpa only [Expr.single,Expr.subst_lift_single] using ha
  | succ _ hn =>
      simpa only [Expr.single,Expr.subst_lift_single] using HasType.lookup ha.valid hn
end TySub
namespace HasType
section
variable {S:Type u} {P:Specification S} {Γ Δ:List (Expr S)}
theorem rename {M A:Expr S} (h:HasType P Γ M A)
    (hΔ:ValidContext P Δ) (ρ:Nat → Nat)
    (hρ:∀ n B,Lookup Γ n B → HasType P Δ (.var (ρ n)) (B.rename ρ)) :
    HasType P Δ (M.rename ρ) (A.rename ρ):=by
  have hσ:TySub P Γ Δ (Expr.var ∘ ρ):=by
    intro n B hn
    simpa only [Expr.subst_var_rename,Function.comp_apply] using hρ n B hn
  simpa only [Expr.subst_var_rename] using h.subst hΔ (Expr.var ∘ ρ) hσ
theorem instantiate {A b B a:Expr S}
    (hb:HasType P (A :: Γ) b B) (ha:HasType P Γ a A) :
    HasType P Γ (b.instantiate a) (B.instantiate a) :=
  hb.subst ha.valid _ (TySub.single ha)
theorem weaken_under {A D b B:Expr S} {s t:S}
    (hb:HasType P (A :: Γ) b B) (hA:HasType P Γ A (.sort s))
    (hD:HasType P Γ D (.sort t)) :
    HasType P (A.rename Nat.succ :: D :: Γ)
      (b.rename (Expr.liftRen Nat.succ)) (B.rename (Expr.liftRen Nat.succ)):=by
  have hA':HasType P (D :: Γ) (A.subst (Expr.var ∘ Nat.succ)) (.sort s):=by
    simpa only [Expr.subst_var_rename,Expr.rename] using HasType.weaken hA hD
  have hσ:=(TySub.weaken hD).lift hA'
  have h:=hb.subst (.cons (.cons hD.valid hD) hA') _ hσ
  have heq:Expr.liftSub (Expr.var ∘ Nat.succ:Nat → Expr S) =
      Expr.var ∘ Expr.liftRen Nat.succ:=by
    funext n
    cases n <;> rfl
  simpa only [heq,Expr.subst_var_rename] using h
theorem context_head_conversion {A A' b B:Expr S} {s t:S}
    (hb:HasType P (A :: Γ) b B) (hA:HasType P Γ A (.sort s))
    (hA':HasType P Γ A' (.sort t)) (hc:Converts A A') :
    HasType P (A' :: Γ) b B:=by
  have hσ:TySub P (A :: Γ) (A' :: Γ) Expr.var:=by
    intro n D hn
    rw [Expr.subst_var]
    cases hn with
    | zero =>
        exact .conversion (.var hA') (.weaken hA hA')
          (.symm _ _ (hc.rename Nat.succ))
    | succ _ hn => exact .weaken (lookup hA.valid hn) hA'
  simpa only [Expr.subst_var] using hb.subst (.cons hA'.valid hA') _ hσ
end
variable {S:Type u} {P:Specification S}
def Generation (P:Specification S) (Γ:List (Expr S))
    (M T:Expr S):Prop :=
  match M with
  | .var n => ∃ A,Lookup Γ n A ∧ Converts T A
  | .sort s => ∃ t,P.sortAxioms s t ∧ Converts T (.sort t)
  | .app f a => ∃ A B,HasType P Γ f (.pi A B) ∧ HasType P Γ a A ∧
      Converts T (B.instantiate a)
  | .lam A b => ∃ B s,HasType P (A :: Γ) b B ∧
      HasType P Γ (.pi A B) (.sort s) ∧ Converts T (.pi A B)
  | .pi A B => ∃ s₁ s₂ s₃,HasType P Γ A (.sort s₁) ∧
      HasType P (A :: Γ) B (.sort s₂) ∧ P.rule s₁ s₂ s₃ ∧
      Converts T (.sort s₃)
theorem generation {Γ:List (Expr S)} {M T:Expr S}
    (h:HasType P Γ M T):Generation P Γ M T:=by
  induction h with
  | ax h => exact ⟨_,h,.refl _⟩
  | var h ih => exact ⟨_,.zero _ _,.refl _⟩
  | @weaken Γ M T D s hM hD ihM ihD =>
      cases M with
      | var n =>
          obtain ⟨A,hA,hc⟩:=ihM
          exact ⟨_,.succ D hA,hc.rename Nat.succ⟩
      | sort t =>
          obtain ⟨t',ht,hc⟩:=ihM
          exact ⟨t',ht,hc.rename Nat.succ⟩
      | app f a =>
          obtain ⟨A,B,hf,ha,hc⟩:=ihM
          refine ⟨_,_,.weaken hf hD,.weaken ha hD,?_⟩
          simpa only [Expr.instantiate_rename] using hc.rename Nat.succ
      | lam A b =>
          obtain ⟨B,t,hb,hPi,hc⟩:=ihM
          obtain ⟨r,hA⟩:=hPi.product_domain _ _ rfl
          exact ⟨_,t,hb.weaken_under hA hD,.weaken hPi hD,
            hc.rename Nat.succ⟩
      | pi A B =>
          obtain ⟨t₁,t₂,t₃,hA,hB,hr,hc⟩:=ihM
          exact ⟨t₁,t₂,t₃,.weaken hA hD,hB.weaken_under hA hD,
            hr,hc.rename Nat.succ⟩
  | product hA hB hr ihA ihB => exact ⟨_,_,_,hA,hB,hr,.refl _⟩
  | abstraction hb hPi ihb ihPi => exact ⟨_,_,hb,hPi,.refl _⟩
  | application hf ha ihf iha => exact ⟨_,_,hf,ha,.refl _⟩
  | @conversion Γ M A B s hM hB hc ihM ihB =>
      cases M with
      | var n =>
          obtain ⟨D,hD,hd⟩:=ihM
          exact ⟨D,hD,.trans _ _ _ (.symm _ _ hc) hd⟩
      | sort t =>
          obtain ⟨r,hr,hd⟩:=ihM
          exact ⟨r,hr,.trans _ _ _ (.symm _ _ hc) hd⟩
      | app f a =>
          obtain ⟨D,E,hf,ha,hd⟩:=ihM
          exact ⟨D,E,hf,ha,.trans _ _ _ (.symm _ _ hc) hd⟩
      | lam D b =>
          obtain ⟨E,r,hb,hPi,hd⟩:=ihM
          exact ⟨E,r,hb,hPi,.trans _ _ _ (.symm _ _ hc) hd⟩
      | pi D E =>
          obtain ⟨r₁,r₂,r₃,hD,hE,hr,hd⟩:=ihM
          exact ⟨r₁,r₂,r₃,hD,hE,hr,.trans _ _ _ (.symm _ _ hc) hd⟩
theorem generation_pi {Γ:List (Expr S)} {A B T:Expr S}
    (h:HasType P Γ (.pi A B) T) :
    ∃ s₁ s₂ s₃,HasType P Γ A (.sort s₁) ∧
      HasType P (A :: Γ) B (.sort s₂) ∧ P.rule s₁ s₂ s₃ ∧
      Converts T (.sort s₃):=h.generation
theorem generation_lam {Γ:List (Expr S)} {A b T:Expr S}
    (h:HasType P Γ (.lam A b) T) :
    ∃ B s,HasType P (A :: Γ) b B ∧ HasType P Γ (.pi A B) (.sort s) ∧
      Converts T (.pi A B):=h.generation
theorem generation_app {Γ:List (Expr S)} {f a T:Expr S}
    (h:HasType P Γ (.app f a) T) :
    ∃ A B,HasType P Γ f (.pi A B) ∧ HasType P Γ a A ∧
      Converts T (B.instantiate a):=h.generation
theorem regularity {Γ:List (Expr S)} {M A:Expr S} (h:HasType P Γ M A) :
    (∃ s,A = .sort s) ∨ (∃ s,HasType P Γ A (.sort s)):=by
  induction h with
  | ax h => exact .inl ⟨_,rfl⟩
  | var h ih => exact .inr ⟨_,.weaken h h⟩
  | weaken hM hD ihM ihD =>
      obtain ⟨s,rfl⟩ | ⟨s,hA⟩:=ihM
      · exact .inl ⟨s,rfl⟩
      · exact .inr ⟨s,.weaken hA hD⟩
  | product hA hB hr ihA ihB => exact .inl ⟨_,rfl⟩
  | abstraction hb hPi ihb ihPi => exact .inr ⟨_,hPi⟩
  | application hf ha ihf iha =>
      obtain ⟨s,heq⟩ | ⟨s,hPi⟩:=ihf
      · cases heq
      · obtain ⟨s₁,s₂,s₃,hA,hB,hr,hc⟩:=hPi.generation_pi
        exact .inr ⟨s₂,hB.instantiate ha⟩
  | conversion hM hA hc ihM ihA => exact .inr ⟨_,hA⟩
theorem product_type_sorted {Γ:List (Expr S)} {M A B:Expr S}
    (h:HasType P Γ M (.pi A B)):∃ s,HasType P Γ (.pi A B) (.sort s):=by
  obtain ⟨s,heq⟩ | hs:=h.regularity
  · cases heq
  · exact hs
end HasType
namespace Converts
variable {S:Type u}
theorem pi {A A' B B':Expr S} (hA:Converts A A') (hB:Converts B B') :
    Converts (.pi A B) (.pi A' B'):=by
  obtain ⟨D,hD,hD'⟩:=hA.join
  obtain ⟨E,hE,hE'⟩:=hB.join
  exact .trans _ _ _ (hD.pi hE).converts (.symm _ _ (hD'.pi hE').converts)
theorem pi_not_sort {A B:Expr S} {s:S}:¬ Converts (.pi A B) (.sort s):=by
  intro h
  obtain ⟨N,hN,hs⟩:=h.join
  have heq:=(Normal.sort s).reduces_eq hs
  obtain ⟨D,E,hDE,_,_⟩:=hN.pi_inv
  cases heq.trans hDE
theorem sort_inj {s t:S} (h:Converts (Expr.sort s) (.sort t)):s = t :=
  Expr.sort.inj ((Normal.sort s).eq_of_converts (Normal.sort t) h)
theorem instantiate_right {a a':Expr S} (h:Converts a a') (B:Expr S) :
    Converts (B.instantiate a) (B.instantiate a'):=by
  induction h with
  | rel a a' h =>
      exact (Parallel.instantiate (Parallel.refl B) (Parallel.of_beta h)).reduces.converts
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c hab hbc ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
end Converts
namespace HasType
variable {S:Type u} {P:Specification S}
theorem application_type_sorted_aux {Γ:List (Expr S)} {M T:Expr S}
    (h:HasType P Γ M T) :
    ∀ f a,M = .app f a → ∃ s,HasType P Γ T (.sort s):=by
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
          obtain ⟨r,hr⟩:=ihM g b rfl
          exact ⟨r,.weaken hr hD⟩
  | product hA hB hr ihA ihB => intro f a heq; cases heq
  | abstraction hb hPi ihb ihPi => intro f a heq; cases heq
  | application hf ha ihf iha =>
      intro f a heq
      obtain ⟨s,hPi⟩:=hf.product_type_sorted
      obtain ⟨s₁,s₂,s₃,hA,hB,hr,hc⟩:=hPi.generation_pi
      exact ⟨s₂,hB.instantiate ha⟩
  | conversion hM hT hc ihM ihT => intro f a heq; exact ⟨_,hT⟩
theorem application_type_sorted {Γ:List (Expr S)} {f a T:Expr S}
    (h:HasType P Γ (.app f a) T):∃ s,HasType P Γ T (.sort s) :=
  h.application_type_sorted_aux f a rfl
theorem abstraction_type_sorted {Γ:List (Expr S)} {A b T:Expr S}
    (h:HasType P Γ (.lam A b) T):∃ s,HasType P Γ T (.sort s):=by
  obtain ⟨s,hT⟩ | hs:=h.regularity
  · obtain ⟨B,t,hb,hPi,hc⟩:=h.generation_lam
    subst T
    exact False.elim (Converts.pi_not_sort (.symm _ _ hc))
  · exact hs
theorem conversion_from_sort {Γ:List (Expr S)} {M T:Expr S} {s:S}
    (h:HasType P Γ M (.sort s))
    (hT:(∃ t,T = .sort t) ∨ ∃ t,HasType P Γ T (.sort t))
    (hc:Converts T (.sort s)):HasType P Γ M T:=by
  obtain ⟨t,rfl⟩ | ⟨t,ht⟩:=hT
  · have heq:=hc.sort_inj
    subst t
    exact h
  · exact .conversion h ht (.symm _ _ hc)
theorem subject_reduction {Γ:List (Expr S)} {M N T:Expr S}
    (h:HasType P Γ M T) (hr:Beta M N):HasType P Γ N T:=by
  induction hr generalizing Γ T with
  | head A b a =>
      obtain ⟨r,hT⟩:=h.application_type_sorted
      obtain ⟨D,E,hf,ha,hc⟩:=h.generation_app
      obtain ⟨B,s,hb,hPi,hp⟩:=hf.generation_lam
      obtain ⟨hDA,hEB⟩:=hp.product_compatibility
      obtain ⟨t,hA⟩:=hPi.product_domain A B rfl
      have haA:=HasType.conversion ha hA hDA
      have hresult:=hb.instantiate haA
      exact .conversion hresult hT (.trans _ _ _
        (.symm _ _ (hEB.subst (Expr.single a))) (.symm _ _ hc))
  | app_left hr ih =>
      obtain ⟨r,hT⟩:=h.application_type_sorted
      obtain ⟨A,B,hf,ha,hc⟩:=h.generation_app
      exact .conversion (.application (ih hf) ha) hT (.symm _ _ hc)
  | @app_right f a a' hr ih =>
      obtain ⟨r,hT⟩:=h.application_type_sorted
      obtain ⟨A,B,hf,ha,hc⟩:=h.generation_app
      exact .conversion (.application hf (ih ha)) hT (.trans _ _ _
        (.symm _ _ ((show Converts a a' from .rel _ _ hr).instantiate_right B)) (.symm _ _ hc))
  | @lam_domain A A' b hr ih =>
      obtain ⟨r,hT⟩:=h.abstraction_type_sorted
      obtain ⟨B,s,hb,hPi,hc⟩:=h.generation_lam
      obtain ⟨s₁,s₂,s₃,hA,hB,hrule,hs⟩:=hPi.generation_pi
      have hA':=ih hA
      have heq:Converts A A':=.rel _ _ hr
      have hb':=hb.context_head_conversion hA hA' heq
      have hB':=hB.context_head_conversion hA hA' heq
      have hp':=HasType.product hA' hB' hrule
      exact .conversion (.abstraction hb' hp') hT (.trans _ _ _
        (.symm _ _ (heq.pi (.refl B))) (.symm _ _ hc))
  | lam_body hr ih =>
      obtain ⟨r,hT⟩:=h.abstraction_type_sorted
      obtain ⟨B,s,hb,hPi,hc⟩:=h.generation_lam
      exact .conversion (.abstraction (ih hb) hPi) hT (.symm _ _ hc)
  | pi_domain hr ih =>
      obtain ⟨s₁,s₂,s₃,hA,hB,hrule,hc⟩:=h.generation_pi
      have hA':=ih hA
      have hB':=hB.context_head_conversion hA hA' (.rel _ _ hr)
      exact (HasType.product hA' hB' hrule).conversion_from_sort h.regularity hc
  | pi_body hr ih =>
      obtain ⟨s₁,s₂,s₃,hA,hB,hrule,hc⟩:=h.generation_pi
      exact (HasType.product hA (ih hB) hrule).conversion_from_sort h.regularity hc
theorem subject_reduces {Γ:List (Expr S)} {M N T:Expr S}
    (h:HasType P Γ M T) (hr:Reduces M N):HasType P Γ N T:=by
  induction hr with
  | refl => exact h
  | tail _ hr ih => exact ih.subject_reduction hr
end HasType
namespace Normal
variable {S:Type u} {M:Expr S}
end Normal
namespace Expr
variable {S:Type u}
noncomputable def nfTerm (M:Expr S):Expr S:=by
  classical
  exact if h:WeaklyNormalizing M then Classical.choose h else M
theorem nfTerm_spec {M:Expr S} (h:WeaklyNormalizing M) :
    Reduces M M.nfTerm ∧ Normal M.nfTerm:=by
  rw [nfTerm,dif_pos h]
  exact Classical.choose_spec h
theorem nfTerm_eq {M N:Expr S} (hr:Reduces M N) (hn:Normal N) :
    M.nfTerm = N:=by
  have h:WeaklyNormalizing M:=⟨N,hr,hn⟩
  obtain ⟨hm,hnm⟩:=nfTerm_spec h
  exact hnm.eq_of_converts hn (.trans _ _ _ (.symm _ _ hm.converts) hr.converts)
@[simp] theorem nfTerm_of_normal {M:Expr S} (h:Normal M):M.nfTerm = M :=
  nfTerm_eq .refl h
theorem nfTerm_converts {M N:Expr S} (hM:WeaklyNormalizing M)
    (hN:WeaklyNormalizing N) (hc:Converts M N):M.nfTerm = N.nfTerm:=by
  obtain ⟨hm,hnm⟩:=nfTerm_spec hM
  obtain ⟨hn,hnn⟩:=nfTerm_spec hN
  exact hnm.eq_of_converts hnn (.trans _ _ _ (.symm _ _ hm.converts)
    (.trans _ _ _ hc hn.converts))
theorem nfTerm_pi {A B:Expr S}
    (hA:WeaklyNormalizing A) (hB:WeaklyNormalizing B) :
    (Expr.pi A B).nfTerm = .pi A.nfTerm B.nfTerm :=
  nfTerm_eq ((nfTerm_spec hA).1.pi (nfTerm_spec hB).1)
    ((nfTerm_spec hA).2.pi (nfTerm_spec hB).2)
end Expr
namespace HasType
variable {S:Type u} {P:Specification S} {Γ:List (Expr S)} {M A:Expr S}
theorem weakNorm (h:HasType P Γ M A) (hw:SystemWeaklyNormalizing P) :
    WeaklyNormalizing M:=hw Γ h.valid M ⟨A,.inl h⟩
theorem type_weakNorm (h:HasType P Γ M A) (hw:SystemWeaklyNormalizing P) :
    WeaklyNormalizing A:=hw Γ h.valid A ⟨M,.inr h⟩
theorem nfTerm (h:HasType P Γ M A) (hw:SystemWeaklyNormalizing P) :
    HasType P Γ M.nfTerm A :=
  h.subject_reduces (Expr.nfTerm_spec (h.weakNorm hw)).1
theorem normalize_type (h:HasType P Γ M A) (hw:SystemWeaklyNormalizing P) :
    HasType P Γ M A.nfTerm:=by
  obtain ⟨s,rfl⟩ | ⟨s,hA⟩:=h.regularity
  · simpa only [Expr.nfTerm_of_normal (Normal.sort s)] using h
  · exact .conversion h (hA.nfTerm hw)
      (Expr.nfTerm_spec (h.type_weakNorm hw)).1.converts
end HasType
inductive Neutral {S:Type u}:Expr S → Prop
  | var (n):Neutral (.var n)
  | app {f a}:Neutral f → Neutral (.app f a)
namespace HasType
variable {S:Type u} {P:Specification S} {Γ:List (Expr S)}
theorem sort_cannot_have_product_type {s:S} {A B:Expr S}
    (h:HasType P Γ (.sort s) (.pi A B)):False:=by
  obtain ⟨t,ht,hc⟩:=h.generation
  exact Converts.pi_not_sort hc
theorem product_cannot_have_product_type {A B D E:Expr S}
    (h:HasType P Γ (.pi A B) (.pi D E)):False:=by
  obtain ⟨s₁,s₂,s₃,hA,hB,hr,hc⟩:=h.generation_pi
  exact Converts.pi_not_sort hc
theorem lambda_cannot_have_sort_type {A b:Expr S} {s:S}
    (h:HasType P Γ (.lam A b) (.sort s)):False:=by
  obtain ⟨B,t,hb,hPi,hc⟩:=h.generation_lam
  exact Converts.pi_not_sort (.symm _ _ hc)
theorem neutral_unique {M A B:Expr S} (hn:Neutral M)
    (hA:HasType P Γ M A) (hB:HasType P Γ M B):Converts A B:=by
  induction hn generalizing A B with
  | var n =>
      obtain ⟨D,hD,hcD⟩:=hA.generation
      obtain ⟨E,hE,hcE⟩:=hB.generation
      have heq:D = E:=by
        clear hA hB hcD hcE
        induction hD generalizing E with
        | zero A Γ => cases hE; rfl
        | succ C hD ih =>
            cases hE with
            | succ _ hE => exact congrArg (Expr.rename Nat.succ) (ih _ hE)
      subst E
      exact .trans _ _ _ hcD (.symm _ _ hcE)
  | @app f a hn ih =>
      obtain ⟨D,E,hf,ha,hc⟩:=hA.generation_app
      obtain ⟨D',E',hf',ha',hc'⟩:=hB.generation_app
      have he:=(ih hf hf').product_compatibility.2
      exact .trans _ _ _ hc (.trans _ _ _ (he.subst (Expr.single a)) (.symm _ _ hc'))
theorem normal_shape {M T:Expr S} (h:HasType P Γ M T) (hn:Normal M) :
    (∃ s,M = .sort s) ∨ Neutral M ∨ (∃ A B,M = .pi A B) ∨
      (∃ A b,M = .lam A b):=by
  induction M generalizing T with
  | var n => exact .inr (.inl (.var n))
  | sort s => exact .inl ⟨s,rfl⟩
  | lam A b ihA ihb => exact .inr (.inr (.inr ⟨A,b,rfl⟩))
  | pi A B ihA ihB => exact .inr (.inr (.inl ⟨A,B,rfl⟩))
  | app f a ihf iha =>
      obtain ⟨D,E,hf,ha,hc⟩:=h.generation_app
      obtain ⟨s,rfl⟩ | hnf | ⟨A,B,rfl⟩ | ⟨A,b,rfl⟩:=ihf hf hn.app_left
      · exact False.elim hf.sort_cannot_have_product_type
      · exact .inr (.inl (.app hnf))
      · exact False.elim hf.product_cannot_have_product_type
      · exact False.elim (hn _ (.head A b a))
theorem sorted_normal_shape {M:Expr S} {s:S}
    (h:HasType P Γ M (.sort s)) (hn:Normal M) :
    (∃ t,M = .sort t) ∨ Neutral M ∨ (∃ A B,M = .pi A B):=by
  obtain h | h | h | ⟨A,b,rfl⟩:=h.normal_shape hn
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr h)
  · exact False.elim h.lambda_cannot_have_sort_type
end HasType
inductive TyTree {S:Type u} (P:Specification S) :
    List (Expr S) → Expr S → Expr S → Type u
  | var {Γ n A T} (typing:HasType P Γ (.var n) T)
      (declaration:Lookup Γ n A) (convert:Converts T A):TyTree P Γ (.var n) T
  | sort {Γ s t T} (typing:HasType P Γ (.sort s) T)
      (sortAxioms:P.sortAxioms s t) (convert:Converts T (.sort t)):TyTree P Γ (.sort s) T
  | product {Γ A B a b c T} (typing:HasType P Γ (.pi A B) T)
      (domain:TyTree P Γ A (.sort a)) (body:TyTree P (A :: Γ) B (.sort b))
      (rule:P.rule a b c) (convert:Converts T (.sort c)):TyTree P Γ (.pi A B) T
  | abstraction {Γ A b B a s T} (typing:HasType P Γ (.lam A b) T)
      (annotation:TyTree P Γ A (.sort a)) (body:TyTree P (A :: Γ) b B)
      (product:HasType P Γ (.pi A B) (.sort s)) (convert:Converts T (.pi A B)) :
      TyTree P Γ (.lam A b) T
  | application {Γ f a A B T} (typing:HasType P Γ (.app f a) T)
      (function:TyTree P Γ f (.pi A B)) (argument:TyTree P Γ a A)
      (convert:Converts T (B.instantiate a)):TyTree P Γ (.app f a) T
namespace TyTree
variable {S:Type u} {P:Specification S} {Γ:List (Expr S)} {M T:Expr S}
theorem typing (t:TyTree P Γ M T):HasType P Γ M T:=by
  cases t with
  | var h _ _ => exact h
  | sort h _ _ => exact h
  | product h _ _ _ _ => exact h
  | abstraction h _ _ _ _ => exact h
  | application h _ _ _ => exact h
def retarget {T':Expr S} (t:TyTree P Γ M T)
    (ht:HasType P Γ M T') (hc:Converts T' T):TyTree P Γ M T':=by
  cases t with
  | var _ hd he => exact .var ht hd (.trans _ _ _ hc he)
  | sort _ ha he => exact .sort ht ha (.trans _ _ _ hc he)
  | product _ d b hr he => exact .product ht d b hr (.trans _ _ _ hc he)
  | abstraction _ d b hp he => exact .abstraction ht d b hp (.trans _ _ _ hc he)
  | application _ f a he => exact .application ht f a (.trans _ _ _ hc he)
theorem nonempty (h:HasType P Γ M T):Nonempty (TyTree P Γ M T):=by
  induction M generalizing Γ T with
  | var n =>
      obtain ⟨A,hd,hc⟩:=h.generation
      exact ⟨.var h hd hc⟩
  | sort s =>
      obtain ⟨t,ha,hc⟩:=h.generation
      exact ⟨.sort h ha hc⟩
  | pi A B ihA ihB =>
      obtain ⟨a,b,c,hA,hB,hr,hc⟩:=h.generation_pi
      exact ⟨.product h (ihA hA).some (ihB hB).some hr hc⟩
  | lam A b ihA ihb =>
      obtain ⟨B,s,hb,hp,hc⟩:=h.generation_lam
      obtain ⟨a,a',c,hA,_,_,_⟩:=hp.generation_pi
      exact ⟨.abstraction h (ihA hA).some (ihb hb).some hp hc⟩
  | app f a ihf iha =>
      obtain ⟨A,B,hf,ha,hc⟩:=h.generation_app
      exact ⟨.application h (ihf hf).some (iha ha).some hc⟩
noncomputable def ofTyping (h:HasType P Γ M T):TyTree P Γ M T:=(nonempty h).some
def DeclRenaming (Γ Δ:List (Expr S)) (ρ:Nat → Nat):Prop :=
  ∀ n A,Lookup Γ n A → Lookup Δ (ρ n) (A.rename ρ)
namespace DeclRenaming
variable {Δ:List (Expr S)} {ρ:Nat → Nat}
theorem typed (h:DeclRenaming Γ Δ ρ) (hΔ:ValidContext P Δ) :
    ∀ n A,Lookup Γ n A → HasType P Δ (.var (ρ n)) (A.rename ρ) :=
  fun n A hn => HasType.lookup hΔ (h n A hn)
theorem lift (h:DeclRenaming Γ Δ ρ) (A:Expr S) :
    DeclRenaming (A :: Γ) (A.rename ρ :: Δ) (Expr.liftRen ρ):=by
  intro n B hn
  cases hn with
  | zero =>
      simpa only [Expr.liftRen,Expr.rename_comp,Function.comp_def] using Lookup.zero (A.rename ρ) Δ
  | succ _ hn =>
      have hh:=Lookup.succ (A.rename ρ) (h _ _ hn)
      simpa only [Expr.liftRen,Expr.rename_comp,Function.comp_def] using hh
end DeclRenaming
noncomputable def rename (t:TyTree P Γ M T) {Δ:List (Expr S)} (hΔ:ValidContext P Δ)
    (ρ:Nat → Nat) (hρ:DeclRenaming Γ Δ ρ) :
    TyTree P Δ (M.rename ρ) (T.rename ρ):=by
  induction t generalizing Δ ρ with
  | var h hd hc => exact .var (h.rename hΔ ρ (hρ.typed hΔ)) (hρ _ _ hd) (hc.rename ρ)
  | sort h ha hc => exact .sort (h.rename hΔ ρ (hρ.typed hΔ)) ha (hc.rename ρ)
  | @product Γ A B a b c T h d e hr hc ihd ihe =>
      have hA:HasType P Δ (A.rename ρ) (.sort a):=d.typing.rename hΔ ρ (hρ.typed hΔ)
      exact .product (h.rename hΔ ρ (hρ.typed hΔ)) (ihd hΔ ρ hρ)
        (ihe (.cons hΔ hA) _ (hρ.lift A)) hr (hc.rename ρ)
  | @abstraction Γ A b B a s T h d e hp hc ihd ihe =>
      have hA:HasType P Δ (A.rename ρ) (.sort a):=d.typing.rename hΔ ρ (hρ.typed hΔ)
      exact .abstraction (h.rename hΔ ρ (hρ.typed hΔ)) (ihd hΔ ρ hρ)
        (ihe (.cons hΔ hA) _ (hρ.lift A)) (hp.rename hΔ ρ (hρ.typed hΔ)) (hc.rename ρ)
  | application h f a hc ihf iha =>
      apply TyTree.application (h.rename hΔ ρ (hρ.typed hΔ)) (ihf hΔ ρ hρ) (iha hΔ ρ hρ)
      simpa only [Expr.instantiate_rename] using hc.rename ρ
namespace DeclRenaming
variable {Δ:List (Expr S)}
theorem weaken (A:Expr S):DeclRenaming Γ (A :: Γ) Nat.succ :=
  fun _ _ h => .succ A h
end DeclRenaming
abbrev StoredSubstitution (P:Specification S) (Γ Δ:List (Expr S))
    (σ:Nat → Expr S):Type u :=
  ∀ n A,Lookup Γ n A → TyTree P Δ (σ n) (A.subst σ)
namespace StoredSubstitution
variable {Δ:List (Expr S)} {σ:Nat → Expr S}
theorem typed (ts:StoredSubstitution P Γ Δ σ):TySub P Γ Δ σ :=
  fun n A hn => (ts n A hn).typing
noncomputable def lift (ts:StoredSubstitution P Γ Δ σ) {A:Expr S} {s:S}
    (hA:HasType P Δ (A.subst σ) (.sort s)) :
    StoredSubstitution P (A :: Γ) (A.subst σ :: Δ) (Expr.liftSub σ) :=
  fun n => match n with
  | 0 => fun B hn => by
      have he:B = A.rename Nat.succ:=by cases hn; rfl
      have he':B.subst (Expr.liftSub σ) = (A.subst σ).rename Nat.succ:=by
        rw [he,Expr.subst_rename,Expr.rename_subst]
        rfl
      exact .var (he'.symm ▸ HasType.var hA) (.zero _ _) (by rw [he']; exact .refl _)
  | n+1 => fun B hn => by
      let hex:∃ B',Lookup Γ n B' ∧ B = B'.rename Nat.succ:=by
        cases hn with
        | succ _ h => exact ⟨_,h,rfl⟩
      let tt:=(ts _ _ hex.choose_spec.1).rename (.cons hA.valid hA) Nat.succ (DeclRenaming.weaken _)
      have he:B.subst (Expr.liftSub σ) = (hex.choose.subst σ).rename Nat.succ:=by
        calc
          B.subst (Expr.liftSub σ) = (hex.choose.rename Nat.succ).subst (Expr.liftSub σ) :=
            congrArg (Expr.subst (Expr.liftSub σ)) hex.choose_spec.2
          _ = (hex.choose.subst σ).rename Nat.succ:=by
            rw [Expr.subst_rename,Expr.rename_subst]
            rfl
      exact tt.retarget (he.symm ▸ tt.typing) (by rw [he]; exact .refl _)
end StoredSubstitution
noncomputable def subst (t:TyTree P Γ M T) {Δ:List (Expr S)}
    (hΔ:ValidContext P Δ) (σ:Nat → Expr S) (ts:StoredSubstitution P Γ Δ σ) :
    TyTree P Δ (M.subst σ) (T.subst σ):=by
  induction t generalizing Δ σ with
  | var h hd hc => exact (ts _ _ hd).retarget (h.subst hΔ σ ts.typed) (hc.subst σ)
  | sort h ha hc => exact .sort (h.subst hΔ σ ts.typed) ha (hc.subst σ)
  | @product Γ A B a b c T h d e hr hc ihd ihe =>
      have hA:HasType P Δ (A.subst σ) (.sort a):=d.typing.subst hΔ σ ts.typed
      exact .product (h.subst hΔ σ ts.typed) (ihd hΔ σ ts)
        (ihe (.cons hΔ hA) _ (ts.lift hA)) hr (hc.subst σ)
  | @abstraction Γ A b B a s T h d e hp hc ihd ihe =>
      have hA:HasType P Δ (A.subst σ) (.sort a):=d.typing.subst hΔ σ ts.typed
      exact .abstraction (h.subst hΔ σ ts.typed) (ihd hΔ σ ts)
        (ihe (.cons hΔ hA) _ (ts.lift hA)) (hp.subst hΔ σ ts.typed) (hc.subst σ)
  | application h f a hc ihf iha =>
      apply TyTree.application (h.subst hΔ σ ts.typed) (ihf hΔ σ ts) (iha hΔ σ ts)
      simpa only [Expr.instantiate_subst] using hc.subst σ
end TyTree
namespace Expr
variable {S:Type u}
def ProperPart (N M:Expr S):Prop:=∃ K,Child K M ∧ Subterm N K
namespace ProperPart
variable {N M L:Expr S}
theorem child (h:Child N M):ProperPart N M:=⟨N,h,.refl N⟩
theorem subterm (h:ProperPart N M):Subterm N M:=by
  obtain ⟨K,hK,hN⟩:=h
  exact .tail hN hK
theorem trans_right (h:ProperPart N M) (hML:Subterm M L):ProperPart N L:=by
  induction hML with
  | refl => exact h
  | tail hML hL ih => exact ⟨_,hL,h.subterm.trans hML⟩
theorem trans_left (hNM:Subterm N M) (h:ProperPart M L):ProperPart N L:=by
  obtain ⟨K,hK,hM⟩:=h
  exact ⟨K,hK,hNM.trans hM⟩
end ProperPart
namespace Subterm
variable {M:Expr S}
theorem apps_head (ns:List (Expr S)):Subterm M (M.apps ns):=by
  induction ns generalizing M with
  | nil => exact .refl M
  | cons n ns ih => exact (of_child (.app_left M n)).trans (ih (M:=.app M n))
end Subterm
namespace ProperPart
variable {M n:Expr S} {ns:List (Expr S)}
theorem apps_arg (hn:n ∈ ns):ProperPart n (M.apps ns):=by
  induction ns generalizing M with
  | nil => cases hn
  | cons a ns ih =>
    rcases List.mem_cons.mp hn with rfl | hn
    · exact (child (.app_right M n)).trans_right (Subterm.apps_head ns)
    · exact ih hn
end ProperPart
@[simp] theorem subst_apps (M:Expr S) (ns:List (Expr S)) (σ:Nat → Expr S) :
    (M.apps ns).subst σ = (M.subst σ).apps (ns.map (Expr.subst σ)):=by
  induction ns generalizing M with
  | nil => rfl
  | cons n ns ih => exact ih (.app M n)
end Expr
namespace HasType
variable {S:Type u} {P:Specification S} {Γ:List (Expr S)}
theorem spine_shape {M T:Expr S} (h:HasType P Γ M T) :
    (∃ s,M = .sort s) ∨ Neutral M ∨ (∃ A B,M = .pi A B) ∨
      (∃ A b ns,M = (Expr.lam A b).apps ns):=by
  induction M generalizing T with
  | var n => exact .inr (.inl (.var n))
  | sort s => exact .inl ⟨s,rfl⟩
  | lam A b => exact .inr (.inr (.inr ⟨A,b,[],rfl⟩))
  | pi A B => exact .inr (.inr (.inl ⟨A,B,rfl⟩))
  | app f a ihf iha =>
    obtain ⟨D,E,hf,_,_⟩:=h.generation_app
    rcases ihf hf with ⟨s,rfl⟩ | hn | ⟨A,B,rfl⟩ | ⟨A,b,ns,rfl⟩
    · exact False.elim hf.sort_cannot_have_product_type
    · exact .inr (.inl (.app hn))
    · exact False.elim hf.product_cannot_have_product_type
    · exact .inr (.inr (.inr ⟨A,b,ns ++ [a],by simp only [Expr.apps_append,Expr.apps]⟩))
theorem app_spine {f a T:Expr S} (h:HasType P Γ (.app f a) T) :
    Neutral f ∨ ∃ D b n ns,Expr.app f a = (Expr.app (.lam D b) n).apps ns:=by
  obtain ⟨D,E,hf,_,_⟩:=h.generation_app
  rcases hf.spine_shape with ⟨s,rfl⟩ | hn | ⟨A,B,rfl⟩ | ⟨A,b,ns,rfl⟩
  · exact False.elim hf.sort_cannot_have_product_type
  · exact .inl hn
  · exact False.elim hf.product_cannot_have_product_type
  · right
    cases ns with
    | nil => exact ⟨A,b,a,[],rfl⟩
    | cons n ns => exact ⟨A,b,n,ns ++ [a],by simp only [Expr.apps_append,Expr.apps]⟩
theorem apps_head {M T:Expr S} {ns:List (Expr S)} (h:HasType P Γ (M.apps ns) T) :
    ∃ A,HasType P Γ M A:=by
  induction ns generalizing M T with
  | nil => exact ⟨T,h⟩
  | cons n ns ih =>
    obtain ⟨A,hA⟩:=ih h
    obtain ⟨D,E,hf,_,_⟩:=hA.generation_app
    exact ⟨_,hf⟩
theorem apps_arg {M T n:Expr S} {ns:List (Expr S)}
    (h:HasType P Γ (M.apps ns) T) (hn:n ∈ ns):∃ A,HasType P Γ n A:=by
  induction ns generalizing M T with
  | nil => cases hn
  | cons a ns ih =>
    rcases List.mem_cons.mp hn with rfl | hn
    · obtain ⟨T,hT⟩:=h.apps_head (M:=.app M n) (ns:=ns)
      obtain ⟨D,E,_,ha,_⟩:=hT.generation_app
      exact ⟨D,ha⟩
    · exact ih h hn
end HasType
namespace Normal
variable {S:Type u}
theorem rename {M:Expr S} (h:Normal M) (ρ:Nat → Nat) :
    Normal (M.rename ρ):=by
  induction M generalizing ρ with
  | var n => exact Normal.var _
  | sort s => exact Normal.sort _
  | pi A B ihA ihB => exact (ihA h.pi_domain ρ).pi (ihB h.pi_body _)
  | lam A b ihA ihb => exact (ihA h.lam_domain ρ).lam (ihb h.lam_body _)
  | app f a ihf iha =>
      have hf:=ihf h.app_left ρ
      have ha:=iha h.app_right ρ
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
variable {S:Type u}
def Scoped:Nat → Expr S → Prop
  | n,.var i => i < n
  | _,.sort _ => True
  | n,.app M N => Scoped n M ∧ Scoped n N
  | n,.lam A b => Scoped n A ∧ Scoped (n+1) b
  | n,.pi A B => Scoped n A ∧ Scoped (n+1) B
namespace Scoped
variable {n m:Nat} {M:Expr S}
theorem rename (h:Scoped n M) (ρ:Nat → Nat)
    (hρ:∀ i,i < n → ρ i < m):Scoped m (M.rename ρ):=by
  induction M generalizing n m ρ with
  | var i => exact hρ i h
  | sort _ => trivial
  | app M N ihM ihN => exact ⟨ihM h.1 _ hρ,ihN h.2 _ hρ⟩
  | lam A b ihA ihb | pi A b ihA ihb =>
      refine ⟨ihA h.1 _ hρ,ihb h.2 _ ?_⟩
      intro i hi
      cases i with
      | zero => exact Nat.zero_lt_succ _
      | succ i => exact Nat.succ_lt_succ (hρ i (Nat.lt_of_succ_lt_succ hi))
theorem mono (h:Scoped n M) (hnm:n ≤ m):Scoped m M:=by
  simpa only [rename_id] using h.rename id (fun _ hi => lt_of_lt_of_le hi hnm)
theorem rename_congr (h:Scoped n M) {ρ τ:Nat → Nat}
    (he:∀ i,i < n → ρ i = τ i):M.rename ρ = M.rename τ:=by
  induction M generalizing n ρ τ with
  | var i => exact congrArg Expr.var (he i h)
  | sort _ => rfl
  | app M N ihM ihN => exact congrArg₂ Expr.app (ihM h.1 he) (ihN h.2 he)
  | lam A b ihA ihb | pi A b ihA ihb =>
      have hl:∀ i,i < n+1 → liftRen ρ i = liftRen τ i:=by
        intro i hi
        cases i with
        | zero => rfl
        | succ i => exact congrArg Nat.succ (he i (Nat.lt_of_succ_lt_succ hi))
      simp only [Expr.rename,ihA h.1 he,ihb h.2 hl]
theorem subst (h:Scoped n M) (σ:Nat → Expr S)
    (hσ:∀ i,i < n → Scoped m (σ i)):Scoped m (M.subst σ):=by
  induction M generalizing n m σ with
  | var i => exact hσ i h
  | sort _ => trivial
  | app M N ihM ihN => exact ⟨ihM h.1 _ hσ,ihN h.2 _ hσ⟩
  | lam A b ihA ihb | pi A b ihA ihb =>
      refine ⟨ihA h.1 _ hσ,ihb h.2 _ ?_⟩
      intro i hi
      cases i with
      | zero => exact Nat.zero_lt_succ _
      | succ i =>
          exact (hσ i (Nat.lt_of_succ_lt_succ hi)).rename Nat.succ
            (fun _ hi => Nat.succ_lt_succ hi)
theorem instantiate {b a:Expr S} (hb:Scoped (n+1) b) (ha:Scoped n a) :
    Scoped n (b.instantiate a):=by
  apply hb.subst
  intro i hi
  cases i with
  | zero => exact ha
  | succ i => exact Nat.lt_of_succ_lt_succ hi
end Scoped
def revIx (n i:Nat):Nat:=if i < n then n - 1 - i else i
theorem revIx_lt {n i:Nat} (hi:i < n):revIx n i < n:=by
  simp only [revIx,if_pos hi]
  omega
theorem revIx_involutive (n:Nat):Function.Involutive (revIx n):=by
  intro i
  unfold revIx
  split_ifs <;> omega
@[simp] theorem revIx_twice (n:Nat) (M:Expr S) :
    (M.rename (revIx n)).rename (revIx n) = M:=by
  rw [rename_comp]
  have he:revIx n ∘ revIx n = id:=funext (revIx_involutive n)
  rw [he,rename_id]
theorem Scoped.revIx {n:Nat} {M:Expr S} (h:Scoped n M) :
    Scoped n (M.rename (revIx n)) :=
  h.rename _ (fun _ hi => revIx_lt hi)
theorem Scoped.reverseIndex_succ {n:Nat} {M:Expr S} (h:Scoped n M) :
    M.rename (Expr.revIx (n+1)) = (M.rename (Expr.revIx n)).rename Nat.succ:=by
  rw [rename_comp]
  apply h.rename_congr
  intro i hi
  simp only [Function.comp_apply,Expr.revIx,if_pos hi]
  rw [if_pos (Nat.lt_succ_of_lt hi)]
  omega
end Expr
namespace HasType
variable {S:Type u} {P:Specification S} {Γ:List (Expr S)} {M A:Expr S}
theorem scope (h:HasType P Γ M A):M.Scoped Γ.length ∧ A.Scoped Γ.length:=by
  induction h with
  | ax _ => exact ⟨True.intro,True.intro⟩
  | var _ ih =>
      exact ⟨Nat.zero_lt_succ _,ih.1.rename Nat.succ (fun _ hi => Nat.succ_lt_succ hi)⟩
  | weaken _ _ ih _ =>
      exact ⟨ih.1.rename Nat.succ (fun _ hi => Nat.succ_lt_succ hi),
        ih.2.rename Nat.succ (fun _ hi => Nat.succ_lt_succ hi)⟩
  | product _ _ _ ihA ihB => exact ⟨⟨ihA.1,ihB.1⟩,True.intro⟩
  | abstraction _ _ ihb ihPi => exact ⟨⟨ihPi.1.1,ihb.1⟩,ihPi.1⟩
  | application _ _ ihf iha => exact ⟨⟨ihf.1,iha.1⟩,ihf.2.2.instantiate iha.1⟩
  | conversion _ _ _ ihM ihB => exact ⟨ihM.1,ihB.1⟩
end HasType
namespace Beta
variable {S:Type u} {M N:Expr S}
theorem scope (h:Beta M N) {n:Nat} (hM:M.Scoped n):N.Scoped n:=by
  induction h generalizing n with
  | head _ _ _ => exact hM.1.2.instantiate hM.2
  | app_left _ ih => exact ⟨ih hM.1,hM.2⟩
  | app_right _ ih => exact ⟨hM.1,ih hM.2⟩
  | lam_domain _ ih | pi_domain _ ih => exact ⟨ih hM.1,hM.2⟩
  | lam_body _ ih | pi_body _ ih => exact ⟨hM.1,ih hM.2⟩
end Beta
namespace Reduces
variable {S:Type u} {M N:Expr S}
theorem scope (h:Reduces M N) {n:Nat} (hM:M.Scoped n):N.Scoped n:=by
  induction h with
  | refl => exact hM
  | tail _ h ih => exact h.scope ih
end Reduces
namespace WeaklyNormalizing
variable {S:Type u} {M:Expr S}
theorem rename (h:WeaklyNormalizing M) (ρ:Nat → Nat) :
    WeaklyNormalizing (M.rename ρ):=by
  obtain ⟨N,hr,hn⟩:=h
  exact ⟨N.rename ρ,Reduces.rename hr ρ,hn.rename ρ⟩
theorem revIx_iff (n:Nat) :
    WeaklyNormalizing (M.rename (Expr.revIx n)) ↔ WeaklyNormalizing M:=by
  constructor
  · intro h
    simpa only [Expr.revIx_twice] using h.rename (Expr.revIx n)
  · intro h
    exact h.rename _
end WeaklyNormalizing
structure CTower {S:Type u} (P:Specification S) where
  context:Nat → List (Expr S)
  valid:∀ n,ValidContext P (context n)
  length:∀ n,(context n).length = n
  step:∀ n,∃ A s,HasType P (context n) A (.sort s) ∧ context (n+1) = A :: context n
  saturated:∀ (n:Nat) (A:Expr S) (s:S),HasType P (context n) (A.rename (Expr.revIx n)) (.sort s) →
    ∀ lower,∃ m,n ≤ m ∧ lower ≤ m ∧
      context (m+1) = A.rename (Expr.revIx m) :: context m
namespace ContextTowerConstruction
variable {S:Type u} (P:Specification S)
structure Stage (n:Nat) where
  context:List (Expr S)
  valid:ValidContext P context
  length:context.length = n
variable [Countable S]
noncomputable def enumeration:Nat → Expr S:=by
  letI:Nonempty (Expr S):=⟨.var 0⟩
  exact (exists_surjective_nat (Expr S)).choose
theorem enumeration_surjective:Function.Surjective (enumeration (S:=S)):=by
  let:Nonempty (Expr S):=⟨.var 0⟩
  exact (exists_surjective_nat (Expr S)).choose_spec
noncomputable def scheduled (n:Nat):Expr S:=enumeration (Nat.unpair n).1
theorem scheduled_late (A:Expr S) (lower:Nat) :
    ∃ m,lower ≤ m ∧ scheduled m = A:=by
  obtain ⟨k,hk⟩:=enumeration_surjective A
  exact ⟨Nat.pair k lower,Nat.right_le_pair _ _,by simpa only [scheduled,Nat.unpair_pair]⟩
variable {s₀ t₀:S} (h₀:P.sortAxioms s₀ t₀)
noncomputable def next {n:Nat} (Γ:Stage P n) :
    {A:Expr S // ∃ s,HasType P Γ.context A (.sort s)}:=by
  classical
  let A:Expr S:=(scheduled n).rename (Expr.revIx n)
  exact if ht:∃ s,HasType P Γ.context A (.sort s) then ⟨A,ht⟩
    else ⟨.sort s₀,t₀,HasType.sort_of_valid Γ.valid h₀⟩
noncomputable def stages:(n:Nat) → Stage P n
  | 0 => ⟨[],.nil,rfl⟩
  | n+1 =>
      let Γ:=stages n
      let A:=next P h₀ Γ
      ⟨A.val :: Γ.context,.cons Γ.valid A.property.choose_spec,
        by simp only [List.length_cons,Γ.length]⟩
noncomputable def contexts (n:Nat):List (Expr S):=(stages P h₀ n).context
theorem valid (n:Nat):ValidContext P (contexts P h₀ n):=(stages P h₀ n).valid
theorem length (n:Nat):(contexts P h₀ n).length = n:=(stages P h₀ n).length
theorem step (n:Nat):∃ A s,HasType P (contexts P h₀ n) A (.sort s) ∧
    contexts P h₀ (n+1) = A :: contexts P h₀ n :=
  ⟨(next P h₀ (stages P h₀ n)).val,_,(next P h₀ (stages P h₀ n)).property.choose_spec,rfl⟩
theorem rename_next {n:Nat} {M A:Expr S}
    (h:HasType P (contexts P h₀ n) (M.rename (Expr.revIx n))
      (A.rename (Expr.revIx n))) :
    HasType P (contexts P h₀ (n+1)) (M.rename (Expr.revIx (n+1)))
      (A.rename (Expr.revIx (n+1))):=by
  have hm:M.Scoped n:=by
    have hh:=h.scope.1.revIx
    rw [length,Expr.revIx_twice] at hh
    exact hh
  have ha:A.Scoped n:=by
    have hh:=h.scope.2.revIx
    rw [length,Expr.revIx_twice] at hh
    exact hh
  obtain ⟨D,s,ht,he⟩:=step P h₀ n
  rw [he,hm.reverseIndex_succ,ha.reverseIndex_succ]
  exact .weaken h ht
theorem rename_mono {n m:Nat} {M A:Expr S}
    (h:HasType P (contexts P h₀ n) (M.rename (Expr.revIx n))
      (A.rename (Expr.revIx n))) (hnm:n ≤ m) :
    HasType P (contexts P h₀ m) (M.rename (Expr.revIx m))
      (A.rename (Expr.revIx m)):=by
  induction hnm with
  | refl => exact h
  | step _ ih => exact rename_next P h₀ ih
theorem at_scheduled {n:Nat} (s:S)
    (h:HasType P (contexts P h₀ n) ((scheduled n).rename (Expr.revIx n)) (.sort s)) :
    contexts P h₀ (n+1) = (scheduled n).rename (Expr.revIx n) :: contexts P h₀ n:=by
  classical
  have ht:∃ t,HasType P (stages P h₀ n).context
      ((scheduled n).rename (Expr.revIx n)) (.sort t):=⟨s,h⟩
  simp only [contexts,stages,next,dif_pos ht]
theorem saturated (n:Nat) (A:Expr S) (s:S)
    (h:HasType P (contexts P h₀ n) (A.rename (Expr.revIx n)) (.sort s))
    (lower:Nat):∃ m,n ≤ m ∧ lower ≤ m ∧
      contexts P h₀ (m+1) = A.rename (Expr.revIx m) :: contexts P h₀ m:=by
  obtain ⟨m,hm,he⟩:=scheduled_late A (max n lower)
  have hnm:n ≤ m:=(le_max_left _ _).trans hm
  have hlm:lower ≤ m:=(le_max_right _ _).trans hm
  have ht:HasType P (contexts P h₀ m) (A.rename (Expr.revIx m)) (.sort s) :=
    rename_mono P h₀ (A:=.sort s) h hnm
  refine ⟨m,hnm,hlm,?_⟩
  have hs:HasType P (contexts P h₀ m)
      ((scheduled m).rename (Expr.revIx m)) (.sort s):=by
    rw [he]
    exact ht
  calc
    contexts P h₀ (m+1) = (scheduled m).rename (Expr.revIx m) :: contexts P h₀ m :=
      at_scheduled P h₀ s hs
    _ = A.rename (Expr.revIx m) :: contexts P h₀ m :=
      congrArg (fun B:Expr S => B.rename (Expr.revIx m) :: contexts P h₀ m) he
noncomputable def tower:CTower P where
  context:=contexts P h₀
  valid:=valid P h₀
  length:=length P h₀
  step:=step P h₀
  saturated:=saturated P h₀
end ContextTowerConstruction
namespace CTower
variable {S:Type u} {P:Specification S} (Ω:CTower P)
def HasType (M A:Expr S):Prop :=
  ∃ n,S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (M.rename (Expr.revIx n))
    (A.rename (Expr.revIx n))
theorem at_next {n:Nat} {M A:Expr S}
    (h:S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (M.rename (Expr.revIx n))
      (A.rename (Expr.revIx n))) :
    S_wpc_barendregt_geuvers_klop.HasType P (Ω.context (n+1)) (M.rename (Expr.revIx (n+1)))
      (A.rename (Expr.revIx (n+1))):=by
  have hm:M.Scoped n:=by
    have hh:=h.scope.1.revIx
    rw [Ω.length,Expr.revIx_twice] at hh
    exact hh
  have ha:A.Scoped n:=by
    have hh:=h.scope.2.revIx
    rw [Ω.length,Expr.revIx_twice] at hh
    exact hh
  obtain ⟨D,s,ht,he⟩:=Ω.step n
  rw [he,hm.reverseIndex_succ,ha.reverseIndex_succ]
  exact .weaken h ht
theorem at_mono {n m:Nat} {M A:Expr S}
    (h:S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (M.rename (Expr.revIx n))
      (A.rename (Expr.revIx n))) (hnm:n ≤ m) :
    S_wpc_barendregt_geuvers_klop.HasType P (Ω.context m) (M.rename (Expr.revIx m))
      (A.rename (Expr.revIx m)):=by
  induction hnm with
  | refl => exact h
  | step _ ih => exact Ω.at_next ih
namespace HasType
variable {Ω:CTower P} {M A:Expr S}
theorem scope (h:Ω.HasType M A):∃ n,M.Scoped n ∧ A.Scoped n:=by
  obtain ⟨n,ht⟩:=h
  refine ⟨n,?_,?_⟩
  · have hh:=ht.scope.1.revIx
    rwa [Ω.length,Expr.revIx_twice] at hh
  · have hh:=ht.scope.2.revIx
    rwa [Ω.length,Expr.revIx_twice] at hh
theorem weakNorm (h:Ω.HasType M A) (hw:SystemWeaklyNormalizing P) :
    WeaklyNormalizing M:=by
  obtain ⟨n,ht⟩:=h
  exact (WeaklyNormalizing.revIx_iff n).mp (hw _ ht.valid _ ⟨_,Or.inl ht⟩)
theorem type_weakNorm (h:Ω.HasType M A) (hw:SystemWeaklyNormalizing P) :
    WeaklyNormalizing A:=by
  obtain ⟨n,ht⟩:=h
  exact (WeaklyNormalizing.revIx_iff n).mp (hw _ ht.valid _ ⟨_,Or.inr ht⟩)
theorem common {N B:Expr S} (h:Ω.HasType M A) (k:Ω.HasType N B) :
    ∃ n,S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (M.rename (Expr.revIx n))
      (A.rename (Expr.revIx n)) ∧
      S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (N.rename (Expr.revIx n))
      (B.rename (Expr.revIx n)):=by
  obtain ⟨n,ht⟩:=h
  obtain ⟨m,kt⟩:=k
  exact ⟨max n m,Ω.at_mono ht (le_max_left _ _),Ω.at_mono kt (le_max_right _ _)⟩
end HasType
theorem fresh_variable {A:Expr S} {s:S} (h:Ω.HasType A (.sort s)) (lower:Nat) :
    ∃ i,lower ≤ i ∧ Ω.HasType (.var i) A:=by
  obtain ⟨n,ht⟩:=h
  have hA:A.Scoped n:=by
    have hh:=ht.scope.1.revIx
    rwa [Ω.length,Expr.revIx_twice] at hh
  obtain ⟨m,hnm,hlm,he⟩:=Ω.saturated n A s ht lower
  have hAm:=hA.mono hnm
  have hm:S_wpc_barendregt_geuvers_klop.HasType P (Ω.context m) (A.rename (Expr.revIx m)) (.sort s) :=
    Ω.at_mono (A:=.sort s) ht hnm
  refine ⟨m,hlm,m+1,?_⟩
  rw [he,hAm.reverseIndex_succ]
  have hv:=S_wpc_barendregt_geuvers_klop.HasType.var hm
  simpa only [Expr.rename,Expr.revIx,Nat.lt_succ_self,ite_true,
    Nat.add_sub_cancel,Nat.sub_self] using hv
end CTower
namespace CTower.HasType
variable {S:Type u} {P:Specification S} {Ω:CTower P}
variable {M N A B:Expr S}
theorem application (hf:Ω.HasType M (.pi A B)) (ha:Ω.HasType N A) :
    Ω.HasType (.app M N) (B.instantiate N):=by
  obtain ⟨n,hf,ha⟩:=hf.common ha
  refine ⟨n,?_⟩
  simpa only [Expr.rename,Expr.instantiate_rename] using
    S_wpc_barendregt_geuvers_klop.HasType.application hf ha
theorem conversion {s:S} (hM:Ω.HasType M A) (hB:Ω.HasType B (.sort s))
    (hc:Converts A B):Ω.HasType M B:=by
  obtain ⟨n,hM,hB⟩:=hM.common hB
  exact ⟨n,.conversion hM hB (hc.rename _)⟩
theorem subject_reduces (h:Ω.HasType M A) (hr:Reduces M N):Ω.HasType N A:=by
  obtain ⟨n,h⟩:=h
  exact ⟨n,h.subject_reduces (hr.rename _)⟩
theorem regularity (h:Ω.HasType M A) :
    (∃ s,A = .sort s) ∨ (∃ s,Ω.HasType A (.sort s)):=by
  obtain ⟨n,h⟩:=h
  obtain ⟨s,he⟩ | ⟨s,hs⟩:=h.regularity
  · left
    refine ⟨s,?_⟩
    have he':=congrArg (Expr.rename (Expr.revIx n)) he
    simpa only [Expr.revIx_twice,Expr.rename] using he'
  · exact .inr ⟨s,n,hs⟩
theorem nfTerm (h:Ω.HasType M A) (hw:SystemWeaklyNormalizing P) :
    Ω.HasType M.nfTerm A :=
  h.subject_reduces (Expr.nfTerm_spec (h.weakNorm hw)).1
theorem normalize_type (h:Ω.HasType M A) (hw:SystemWeaklyNormalizing P) :
    Ω.HasType M A.nfTerm:=by
  obtain ⟨s,rfl⟩ | ⟨s,hA⟩:=h.regularity
  · simpa only [Expr.nfTerm_of_normal (Normal.sort s)] using h
  · exact .conversion h (hA.nfTerm hw)
      (Expr.nfTerm_spec (h.type_weakNorm hw)).1.converts
end CTower.HasType
namespace CTower
variable {S:Type u} {P:Specification S} (Ω:CTower P)
def TySub (Γ:List (Expr S)) (σ:Nat → Expr S):Prop :=
  ∀ n A,Lookup Γ n A → Ω.HasType (σ n) (A.subst σ)
namespace TySub
variable {Ω} {Γ:List (Expr S)} {σ:Nat → Expr S}
theorem tail {A:Expr S} (h:Ω.TySub (A :: Γ) σ) :
    Ω.TySub Γ (σ ∘ Nat.succ):=by
  intro n B hn
  have hh:=h (n+1) (B.rename Nat.succ) (.succ A hn)
  simpa only [Expr.subst_rename,Function.comp_apply] using hh
theorem common_stage (h:Ω.TySub Γ σ) :
    ∃ k,∀ n A,Lookup Γ n A →
      S_wpc_barendregt_geuvers_klop.HasType P (Ω.context k) ((σ n).rename (Expr.revIx k))
        ((A.subst σ).rename (Expr.revIx k)):=by
  induction Γ generalizing σ with
  | nil => exact ⟨0,fun _ _ hn => nomatch hn⟩
  | cons B Γ ih =>
      obtain ⟨k,hk⟩:=ih h.tail
      obtain ⟨m,hm⟩:=h 0 (B.rename Nat.succ) (.zero B Γ)
      refine ⟨max k m,?_⟩
      intro n A hn
      cases hn with
      | zero => exact Ω.at_mono hm (le_max_right k m)
      | succ B hn =>
          have hh:=Ω.at_mono (hk _ _ hn) (le_max_left k m)
          simpa only [Expr.subst_rename,Function.comp_apply] using hh
theorem cons {A a:Expr S} (h:Ω.TySub Γ σ)
    (ha:Ω.HasType a (A.subst σ)):Ω.TySub (A :: Γ) (fun n => match n with
      | 0 => a | n+1 => σ n):=by
  intro n B hn
  cases hn with
  | zero => simpa only [Expr.subst_rename,Function.comp_def] using ha
  | succ A hn => simpa only [Expr.subst_rename,Function.comp_def] using h _ _ hn
end TySub
namespace HasType
variable {Ω} {Γ:List (Expr S)} {M A:Expr S} {σ:Nat → Expr S}
theorem subst (h:S_wpc_barendregt_geuvers_klop.HasType P Γ M A) (hσ:Ω.TySub Γ σ) :
    Ω.HasType (M.subst σ) (A.subst σ):=by
  obtain ⟨k,hk⟩:=TySub.common_stage hσ
  refine ⟨k,?_⟩
  have hh:=h.subst (Ω.valid k) (fun n => (σ n).rename (Expr.revIx k)) (fun n B hn => by
    simpa only [← Expr.rename_subst] using hk n B hn)
  simpa only [← Expr.rename_subst] using hh
end HasType
namespace TySub
variable {Ω} {Γ:List (Expr S)} {σ τ:Nat → Expr S}
theorem comp {Δ:List (Expr S)} (h:Ω.TySub Δ τ)
    (hσ:S_wpc_barendregt_geuvers_klop.TySub P Γ Δ σ) :
    Ω.TySub Γ (fun n => (σ n).subst τ):=by
  intro n A hn
  simpa only [Expr.subst_subst] using HasType.subst (hσ n A hn) h
theorem identity (n:Nat):Ω.TySub (Ω.context n) (.var ∘ Expr.revIx n):=by
  intro i A hi
  have ht:=S_wpc_barendregt_geuvers_klop.HasType.lookup (Ω.valid n) hi
  refine ⟨n,?_⟩
  simpa only [Expr.subst_var_rename,Expr.rename,Function.comp_apply,
    Expr.revIx_involutive n i,Expr.revIx_twice] using ht
end TySub
end CTower
end S_wpc_barendregt_geuvers_klop
end OMA
namespace OMA
namespace S_wpc_barendregt_geuvers_klop
universe u
namespace Cands
variable {S:Type u} {P:Specification S} (Ω:CTower P)
def ActualType (T:Expr S):Prop :=
  (Normal T ∧ ∃ s,Ω.HasType T (.sort s)) ∨ ∃ s,T = .sort s
def Top (T:Expr S):Set (Expr S) :=
  {M | Ω.HasType M T ∧ StronglyNormalizing M}
inductive TestedStack:Expr S → List (Expr S) → Prop
  | nil (T):TestedStack T []
  | cons {D E n ns}:n ∈ Top Ω D →
      TestedStack (E.instantiate n).nfTerm ns → TestedStack (.pi D E) (n :: ns)
def Ground (T:Expr S):Set (Expr S) :=
  {M | Ω.HasType M T ∧ ∀ ns,TestedStack Ω T ns → StronglyNormalizing (M.apps ns)}
namespace TestedStack
variable {Ω} {T:Expr S} {ns:List (Expr S)}
theorem sn (h:TestedStack Ω T ns):StronglyNormalizingArgs ns:=by
  induction h with
  | nil => exact .nil
  | cons hn _ ih => exact .cons hn.2 ih
end TestedStack
variable {Ω} {T M:Expr S}
theorem ground_le_top:Ground Ω T ⊆ Top Ω T:=by
  intro M h
  exact ⟨h.1,h.2 [] (.nil T)⟩
theorem sort_ground_eq_top (s:S):Ground Ω (.sort s) = Top Ω (.sort s):=by
  apply Set.Subset.antisymm ground_le_top
  intro M h
  refine ⟨h.1,?_⟩
  intro ns hs
  cases hs
  exact h.2
theorem var_ground (n:Nat) (h:Ω.HasType (.var n) T):.var n ∈ Ground Ω T :=
  ⟨h,fun _ hs => StronglyNormalizing.var_apps n hs.sn⟩
theorem ground_application (hw:SystemWeaklyNormalizing P) {D E n:Expr S}
    (h:M ∈ Ground Ω (.pi D E)) (hn:n ∈ Top Ω D) :
    .app M n ∈ Ground Ω (E.instantiate n).nfTerm:=by
  refine ⟨(h.1.application hn.1).normalize_type hw,?_⟩
  intro ns hs
  exact h.2 (n :: ns) (.cons hn hs)
def ExpansionClosed (Ω:CTower P) (T:Expr S) (C:Set (Expr S)):Prop :=
  ∀ (D b n:Expr S) (ns:List (Expr S)),
    Ω.HasType ((Expr.app (.lam D b) n).apps ns) T →
    StronglyNormalizing D → StronglyNormalizing b → StronglyNormalizing n →
    StronglyNormalizingArgs ns → (b.instantiate n).apps ns ∈ C →
    (Expr.app (.lam D b) n).apps ns ∈ C
structure IsCandidate (Ω:CTower P) (T:Expr S) (C:Set (Expr S)):Prop where
  lower:Ground Ω T ⊆ C
  upper:C ⊆ Top Ω T
  expansion:ExpansionClosed Ω T C
theorem top_candidate:IsCandidate Ω T (Top Ω T) where
  lower:=ground_le_top
  upper:=Set.Subset.rfl
  expansion:=fun _ _ _ _ ht hD hb hn hns hc =>
    ⟨ht,StronglyNormalizing.head_expansion hD hb hn hns hc.2⟩
def Meet (Ω:CTower P) (T:Expr S) (Cs:Set (Set (Expr S))):Set (Expr S) :=
  {M | M ∈ Top Ω T ∧ ∀ C ∈ Cs,M ∈ C}
theorem meet_candidate {Cs:Set (Set (Expr S))}
    (hCs:∀ C ∈ Cs,IsCandidate Ω T C):IsCandidate Ω T (Meet Ω T Cs) where
  lower:=fun _ h => ⟨ground_le_top h,fun C hC => (hCs C hC).lower h⟩
  upper:=fun _ h => h.1
  expansion:=by
    intro D b n ns ht hD hb hn hns hc
    refine ⟨⟨ht,StronglyNormalizing.head_expansion hD hb hn hns hc.1.2⟩,?_⟩
    intro C hC
    exact (hCs C hC).expansion D b n ns ht hD hb hn hns (hc.2 C hC)
def Bottom (Ω:CTower P) (T:Expr S):Set (Expr S) :=
  Meet Ω T {C | IsCandidate Ω T C}
theorem bottom_candidate:IsCandidate Ω T (Bottom Ω T) :=
  meet_candidate (fun _ h => h)
theorem bottom_le {C:Set (Expr S)} (hC:IsCandidate Ω T C):Bottom Ω T ⊆ C :=
  fun _ h => h.2 C hC
def ProductTest (Ω:CTower P) (D E:Expr S) (A:Set (Expr S))
    (Cs:Expr S → Set (Set (Expr S))):Set (Expr S) :=
  {M | M ∈ Top Ω (.pi D E) ∧ ∀ n ∈ A,∀ C ∈ Cs n,Expr.app M n ∈ C}
theorem productTest_candidate (hw:SystemWeaklyNormalizing P)
    {D E:Expr S} {A:Set (Expr S)} {Cs:Expr S → Set (Set (Expr S))}
    (hA:A ⊆ Top Ω D)
    (hCs:∀ n ∈ A,∀ C ∈ Cs n,IsCandidate Ω (E.instantiate n).nfTerm C) :
    IsCandidate Ω (.pi D E) (ProductTest Ω D E A Cs) where
  lower:=by
    intro M h
    refine ⟨ground_le_top h,?_⟩
    intro n hn C hC
    exact (hCs n hn C hC).lower (ground_application hw h (hA hn))
  upper:=fun _ h => h.1
  expansion:=by
    intro D' b a ns ht hD hb ha hns hc
    refine ⟨⟨ht,StronglyNormalizing.head_expansion hD hb ha hns hc.1.2⟩,?_⟩
    intro n hn C hC
    have ht':=(ht.application (hA hn).1).normalize_type hw
    have hsn:StronglyNormalizingArgs (ns ++ [n]):=by
      apply StronglyNormalizingArgs.of_forall
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hns.of_mem hx
      · have he:x = n:=List.mem_singleton.mp hx
        exact he.symm ▸ (hA hn).2
    have hc':=hc.2 n hn C hC
    have he:(Expr.app (.lam D' b) a).apps (ns ++ [n]) =
        .app ((Expr.app (.lam D' b) a).apps ns) n:=by
      simp only [Expr.apps_append,Expr.apps]
    have he':(b.instantiate a).apps (ns ++ [n]) = .app ((b.instantiate a).apps ns) n:=by
      simp only [Expr.apps_append,Expr.apps]
    rw [← he] at ht'
    rw [← he'] at hc'
    rw [← he]
    exact (hCs n hn C hC).expansion D' b a (ns ++ [n]) ht' hD hb ha hsn hc'
end Cands
end S_wpc_barendregt_geuvers_klop
namespace S_wpc_barendregt_geuvers_klop.Cands
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) (T:Expr S)
abbrev Candidate:={X:Set (Expr S) // IsCandidate Ω T X}
noncomputable instance:InfSet (Candidate Ω T) where
  sInf Cs:=⟨Meet Ω T (Subtype.val '' Cs),meet_candidate (by
    rintro X ⟨x,_,rfl⟩
    exact x.property)⟩
noncomputable instance:CompleteLattice (Candidate Ω T):=completeLatticeOfInf _ (by
  intro Cs
  constructor
  · intro x hx M hM
    exact hM.2 x.val ⟨x,hx,rfl⟩
  · intro x hx M hM
    refine ⟨x.property.upper hM,?_⟩
    rintro X ⟨y,hy,rfl⟩
    exact hx hy hM)
def SignedCandidate (b:Bool):Type u:=if b then (Candidate Ω T)ᵒᵈ else Candidate Ω T
noncomputable instance (b:Bool):CompleteLattice (SignedCandidate Ω T b):=by
  cases b with
  | false => exact inferInstanceAs (CompleteLattice (Candidate Ω T))
  | true => exact inferInstanceAs (CompleteLattice (Candidate Ω T)ᵒᵈ)
namespace SignedCandidate
variable {Ω T} {b:Bool}
def set (X:SignedCandidate Ω T b):Set (Expr S):=by
  cases b <;> exact X.val
def wrap (X:Candidate Ω T):SignedCandidate Ω T b:=by
  cases b <;> exact X
@[simp] theorem set_wrap (X:Candidate Ω T):(wrap (b:=b) X).set = X.val:=by
  cases b <;> rfl
theorem candidate (X:SignedCandidate Ω T b):IsCandidate Ω T X.set:=by
  cases b <;> exact X.property
theorem order (X Y:SignedCandidate Ω T b) :
    X ≤ Y ↔ if b then Y.set ⊆ X.set else X.set ⊆ Y.set:=by
  cases b <;> rfl
theorem ext {X Y:SignedCandidate Ω T b} (h:X.set = Y.set):X = Y:=by
  cases b <;> exact Subtype.ext h
end SignedCandidate
end S_wpc_barendregt_geuvers_klop.Cands
end OMA
namespace OMA
namespace S_wpc_barendregt_geuvers_klop
universe u
def Profile {S:Type u} (P:Specification S) (Γ:List (Expr S))
    (T:Expr S):Set S:={s | HasType P Γ T.nfTerm (.sort s)}
def AxProfile {S:Type u} (P:Specification S) (s:S):Set S :=
  {t | P.sortAxioms s t}
def OutProfile {S:Type u} (P:Specification S) (I J:Set S):Set S :=
  {c | ∃ a ∈ I,∃ b ∈ J,P.rule a b c}
def FeasibleProfile {S:Type u} (P:Specification S) (I:Set S):Prop :=
  I.Nonempty ∧ ∃ Γ T,ValidContext P Γ ∧ Normal T ∧ Profile P Γ T = I
structure ProfileTriple {S:Type u} (P:Specification S) (I J K:Set S):Prop where
  domain:FeasibleProfile P I
  codomain:FeasibleProfile P J
  product:FeasibleProfile P K
  output:K = OutProfile P I J
inductive PriEdge {S:Type u} (P:Specification S) :
    Set S → Set S → Bool → Prop
  | inclusion {I J}:FeasibleProfile P I → FeasibleProfile P J →
      J ⊂ I → PriEdge P I J false
  | domain {I J K}:ProfileTriple P I J K → PriEdge P I K true
  | codomain {I J K}:ProfileTriple P I J K → PriEdge P J K false
inductive SignedPath {V:Type*} (E:V → V → Bool → Prop):V → V → Bool → Prop
  | nil (v):SignedPath E v v false
  | cons {u v w p q}:E u v p → SignedPath E v w q →
      SignedPath E u w (Bool.xor p q)
def Reach {V:Type*} (E:V → V → Bool → Prop) (v w:V):Prop :=
  ∃ b,SignedPath E v w b
def PositivePath {V:Type*} (E:V → V → Bool → Prop):V → V → Prop :=
  Relation.ReflTransGen (fun v w => E v w false)
def IsComp {V:Type*} (E:V → V → Bool → Prop) (C:Set V):Prop :=
  ∃ r ∈ C,∀ v,v ∈ C ↔ Reach E r v ∧ Reach E v r
namespace SignedPath
variable {V:Type*} {E:V → V → Bool → Prop}
theorem singleton {v w:V} {p:Bool} (h:E v w p):SignedPath E v w p:=by
  simpa only [Bool.xor_false] using SignedPath.cons h (.nil w)
theorem append {v w z:V} {p q:Bool}
    (h:SignedPath E v w p) (k:SignedPath E w z q) :
    SignedPath E v z (Bool.xor p q):=by
  induction h with
  | nil v => simpa using k
  | cons he ht ih => simpa only [Bool.xor_assoc] using SignedPath.cons he (ih k)
theorem parity_unique {v w:V} {p q:Bool}
    (h:SignedPath E v w p) (k:SignedPath E v w q)
    (hr:Reach E w v) (hodd:¬ SignedPath E v v true):p = q:=by
  obtain ⟨r,hr⟩:=hr
  have hpr:=h.append hr
  have hqr:=k.append hr
  cases p <;> cases q <;> cases r <;> simp_all
end SignedPath
namespace Reach
variable {V:Type*} {E:V → V → Bool → Prop} {v w z:V}
theorem refl (v:V):Reach E v v:=⟨false,.nil v⟩
theorem trans (h:Reach E v w) (k:Reach E w z):Reach E v z:=by
  obtain ⟨p,hp⟩:=h
  obtain ⟨q,hq⟩:=k
  exact ⟨_,hp.append hq⟩
theorem single {p:Bool} (h:E v w p):Reach E v w:=⟨p,.singleton h⟩
end Reach
namespace PositivePath
variable {V:Type*} {E:V → V → Bool → Prop} {v w:V}
theorem parity (h:PositivePath E v w):SignedPath E v w false:=by
  induction h with
  | refl => exact .nil _
  | tail _ he ih => exact ih.append (.singleton he)
theorem reach (h:PositivePath E v w):Reach E v w:=⟨false,h.parity⟩
end PositivePath
namespace IsComp
variable {V:Type*} {E:V → V → Bool → Prop} {C:Set V} {v w z:V}
theorem connected (h:IsComp E C) (hv:v ∈ C) (hw:w ∈ C):Reach E v w:=by
  obtain ⟨r,hr,hc⟩:=h
  exact ((hc v).1 hv).2.trans ((hc w).1 hw).1
theorem between (h:IsComp E C) (hv:v ∈ C) (hw:w ∈ C)
    (hvz:Reach E v z) (hzw:Reach E z w):z ∈ C:=by
  obtain ⟨r,hr,hc⟩:=h
  exact (hc z).2 ⟨((hc v).1 hv).1.trans hvz,hzw.trans ((hc w).1 hw).2⟩
end IsComp
def ObsLayers {S:Type u} (P:Specification S) (C:Set (Set S)) :
    Set (Set S):={I | ∃ s,{s} ∈ C ∧ (AxProfile P s).Nonempty ∧
      PositivePath (PriEdge P) (AxProfile P s) I}
inductive SecEdge {S:Type u} (P:Specification S) (C:Set (Set S)) :
    Set S → Set S → Bool → Prop
  | positive {I J}:I ∈ ObsLayers P C → J ∈ ObsLayers P C →
      PriEdge P I J false → SecEdge P C I J false
  | negative {I J K}:I ∈ ObsLayers P C → J ∈ ObsLayers P C →
      K ∈ ObsLayers P C → ProfileTriple P I J K →
      SecEdge P C I K true
def DirectLayer {S:Type u} (P:Specification S) (C:Set (Set S))
    (I:Set S):Prop:=I ∈ ObsLayers P C ∧
      ∃ J ∈ C,∃ K ∈ C,ProfileTriple P I J K
def ActL {S:Type u} (P:Specification S) (C:Set (Set S))
    (I:Set S):Prop:=∃ D,DirectLayer P C D ∧ Reach (SecEdge P C) I D
def PlainL {S:Type u} (P:Specification S) (C:Set (Set S))
    (I:Set S):Prop :=
  (∃ D,DirectLayer P C D ∧ SignedPath (SecEdge P C) I D false) ∧
  (∃ D,DirectLayer P C D ∧ SignedPath (SecEdge P C) I D true)
def FreeL {S:Type u} (P:Specification S) (C:Set (Set S))
    (I:Set S) (sign:Bool):Prop:=¬ PlainL P C I ∧
      ∃ D,DirectLayer P C D ∧ SignedPath (SecEdge P C) I D sign
def ForbiddenConfiguration {S:Type u} (P:Specification S) (C:Set (Set S)):Prop :=
  ∃ D:Set (Set S),IsComp (SecEdge P C) D ∧
    (∀ I ∈ D,PlainL P C I) ∧
    (∃ I ∈ D,∃ K ∈ D,SecEdge P C I K true) ∧
    ∃ I J K s,ProfileTriple P I J K ∧ J ∈ D ∧ K ∈ D ∧ {s} ∈ D ∧
      (AxProfile P s).Nonempty ∧ PositivePath (PriEdge P) (AxProfile P s) I
namespace PlainL
variable {S:Type u} {P:Specification S} {C:Set (Set S)} {I J:Set S}
theorem active (h:PlainL P C I):ActL P C I:=by
  obtain ⟨D,hD,hp⟩:=h.1
  exact ⟨D,hD,false,hp⟩
theorem predecessor {b:Bool} (h:PlainL P C J) (e:SecEdge P C I J b) :
    PlainL P C I:=by
  obtain ⟨⟨D,hD,hp⟩,⟨D',hD',hp'⟩⟩:=h
  cases b with
  | false => exact ⟨⟨D,hD,.cons e hp⟩,⟨D',hD',.cons e hp'⟩⟩
  | true => exact ⟨⟨D',hD',.cons e hp'⟩,⟨D,hD,.cons e hp⟩⟩
end PlainL
namespace FreeL
variable {S:Type u} {P:Specification S} {C:Set (Set S)} {I J:Set S}
theorem active {s:Bool} (h:FreeL P C I s):ActL P C I:=by
  obtain ⟨D,hD,hp⟩:=h.2
  exact ⟨D,hD,s,hp⟩
theorem sign_unique {s t:Bool} (h:FreeL P C I s) (k:FreeL P C I t):s = t:=by
  obtain ⟨hn,D,hD,hp⟩:=h
  obtain ⟨_,D',hD',hp'⟩:=k
  cases s <;> cases t
  · rfl
  · exact False.elim (hn ⟨⟨D,hD,hp⟩,⟨D',hD',hp'⟩⟩)
  · exact False.elim (hn ⟨⟨D',hD',hp'⟩,⟨D,hD,hp⟩⟩)
  · rfl
theorem edge_sign {s t b:Bool} (h:FreeL P C I s) (k:FreeL P C J t)
    (e:SecEdge P C I J b):s = Bool.xor b t:=by
  obtain ⟨D,hD,hp⟩:=k.2
  exact h.sign_unique ⟨h.1,D,hD,.cons e hp⟩
theorem direct_sign {s:Bool} (h:FreeL P C I s) (hd:DirectLayer P C I) :
    s = false:=h.sign_unique ⟨h.1,I,hd,.nil I⟩
end FreeL
namespace Expr
variable {S:Type u}
@[simp] theorem nfTerm_idem (M:Expr S):M.nfTerm.nfTerm = M.nfTerm:=by
  classical
  by_cases h:WeaklyNormalizing M
  · exact nfTerm_of_normal (nfTerm_spec h).2
  · simp only [nfTerm,dif_neg h]
theorem nfTerm_rename {M:Expr S} (h:WeaklyNormalizing M) (ρ:Nat → Nat) :
    (M.rename ρ).nfTerm = M.nfTerm.rename ρ :=
  nfTerm_eq ((nfTerm_spec h).1.rename ρ) ((nfTerm_spec h).2.rename ρ)
end Expr
namespace HasType
variable {S:Type u} {P:Specification S} {Γ:List (Expr S)}
theorem lookup_sorted (hΓ:ValidContext P Γ) {n:Nat} {A:Expr S}
    (hn:Lookup Γ n A):∃ s,HasType P Γ A (.sort s):=by
  induction hΓ generalizing n A with
  | nil => cases hn
  | cons hΓ hB ih =>
      cases hn with
      | zero => exact ⟨_,.weaken hB hB⟩
      | succ _ hn =>
          obtain ⟨s,hs⟩:=ih hn
          exact ⟨s,.weaken hs hB⟩
theorem neutral_type_sorted {M A:Expr S} (hn:Neutral M)
    (ht:HasType P Γ M A):∃ s,HasType P Γ A (.sort s):=by
  cases hn with
  | var n =>
      obtain ⟨D,hD,hc⟩:=ht.generation
      obtain ⟨s,hs⟩:=lookup_sorted ht.valid hD
      obtain ⟨t,rfl⟩ | hA:=ht.regularity
      · obtain ⟨Q,hDQ,hsQ⟩:=(show Converts D (.sort t) from .symm _ _ hc).join
        have heq:=(Normal.sort t).reduces_eq hsQ
        subst Q
        exact ⟨s,hs.subject_reduces hDQ⟩
      · exact hA
  | app _ => exact ht.application_type_sorted
end HasType
namespace Profile
variable {S:Type u} {P:Specification S} {Γ Δ:List (Expr S)}
@[simp] theorem nfTerm (T:Expr S):Profile P Γ T.nfTerm = Profile P Γ T:=by
  simp only [Profile,Expr.nfTerm_idem]
theorem of_normal {T:Expr S} (hn:Normal T) :
    Profile P Γ T = {s | HasType P Γ T (.sort s)}:=by
  simp only [Profile,Expr.nfTerm_of_normal hn]
theorem sort (hΓ:ValidContext P Γ) (s:S) :
    Profile P Γ (.sort s) = AxProfile P s:=by
  rw [of_normal (Normal.sort s)]
  ext t
  constructor
  · intro h
    obtain ⟨u,hu,hc⟩:=h.generation
    have he:=hc.sort_inj
    subst u
    exact hu
  · exact HasType.sort_of_valid hΓ
theorem neutral {M:Expr S} {s:S} (hn:Normal M) (hne:Neutral M)
    (ht:HasType P Γ M (.sort s)):Profile P Γ M = {s}:=by
  rw [of_normal hn]
  ext t
  constructor
  · intro h
    exact (ht.neutral_unique hne h).sort_inj.symm
  · intro h
    have he:t = s:=h
    subst t
    exact ht
theorem neutral_axiom {M:Expr S} {s:S} (hne:Neutral M)
    (ht:HasType P Γ M (.sort s)):(AxProfile P s).Nonempty:=by
  obtain ⟨t,ht⟩:=ht.neutral_type_sorted hne
  obtain ⟨u,hu,hc⟩:=ht.generation
  exact ⟨u,hu⟩
theorem pi {A B:Expr S} (hnA:Normal A) (hnB:Normal B) :
    Profile P Γ (.pi A B) = OutProfile P (Profile P Γ A) (Profile P (A :: Γ) B):=by
  rw [of_normal (hnA.pi hnB),of_normal hnA,of_normal hnB]
  ext s
  constructor
  · intro ht
    obtain ⟨a,b,c,hA,hB,hr,hc⟩:=ht.generation_pi
    have he:=hc.sort_inj
    subst c
    exact ⟨a,hA,b,hB,hr⟩
  · rintro ⟨a,hA,b,hB,hr⟩
    exact .product hA hB hr
theorem converts {A B:Expr S} (hA:WeaklyNormalizing A) (hB:WeaklyNormalizing B)
    (hc:Converts A B):Profile P Γ A = Profile P Γ B:=by
  simp only [Profile,Expr.nfTerm_converts hA hB hc]
theorem growth (hw:SystemWeaklyNormalizing P) {T:Expr S}
    (hT:WeaklyNormalizing T) (hΔ:ValidContext P Δ) (σ:Nat → Expr S)
    (hσ:TySub P Γ Δ σ):Profile P Γ T ⊆ Profile P Δ (T.subst σ):=by
  intro s hs
  have ht:HasType P Δ (T.nfTerm.subst σ) (.sort s) :=
    hs.subst hΔ σ hσ
  have hr:=(Expr.nfTerm_spec hT).1.subst σ
  have hrn:=(Expr.nfTerm_spec (ht.weakNorm hw)).1
  have hn:=(Expr.nfTerm_spec (ht.weakNorm hw)).2
  have heq:=Expr.nfTerm_eq (hr.trans hrn) hn
  change HasType P Δ (T.subst σ).nfTerm (.sort s)
  rw [heq]
  exact ht.nfTerm hw
theorem feasible {T:Expr S} (hT:WeaklyNormalizing T)
    (hne:(Profile P Γ T).Nonempty):FeasibleProfile P (Profile P Γ T):=by
  obtain ⟨s,hs⟩:=hne
  exact ⟨⟨s,hs⟩,Γ,T.nfTerm,hs.valid,(Expr.nfTerm_spec hT).2,nfTerm T⟩
end Profile
namespace Reach
variable {V:Type u} (E:V → V → Bool → Prop)
def component (v:V):Set V:={w | Reach E v w ∧ Reach E w v}
theorem mem_component (v:V):v ∈ component E v:=⟨.refl v,.refl v⟩
theorem component_isComponent (v:V):IsComp E (component E v) :=
  ⟨v,mem_component E v,fun _ => Iff.rfl⟩
theorem component_eq {v w:V} (h:Reach E v w) (k:Reach E w v) :
    component E v = component E w:=by
  ext z
  exact ⟨fun hz => ⟨k.trans hz.1,hz.2.trans h⟩,
    fun hz => ⟨h.trans hz.1,hz.2.trans k⟩⟩
variable [Fintype V]
open Classical
noncomputable def predecessors (v:V):Finset V:=Finset.univ.filter fun w => Reach E w v
noncomputable def rank (v:V):Nat:=(predecessors E v).card
@[simp] theorem mem_predecessors {v w:V}:w ∈ predecessors E v ↔ Reach E w v:=by
  simp [predecessors]
theorem rank_mono {v w:V} (h:Reach E v w):rank E v ≤ rank E w:=by
  apply Finset.card_le_card
  intro z hz
  exact (mem_predecessors E).mpr (((mem_predecessors E).mp hz).trans h)
theorem reverse_of_rank_eq {v w:V} (h:Reach E v w) (he:rank E v = rank E w) :
    Reach E w v:=by
  have hs:predecessors E v ⊆ predecessors E w:=by
    intro z hz
    exact (mem_predecessors E).mpr (((mem_predecessors E).mp hz).trans h)
  have he':=Finset.eq_of_subset_of_card_le hs (le_of_eq he.symm)
  apply (mem_predecessors E).mp
  rw [he']
  exact (mem_predecessors E).mpr (.refl _)
theorem component_eq_of_rank_eq {v w:V} (h:Reach E v w)
    (he:rank E v = rank E w):component E v = component E w :=
  component_eq E h (reverse_of_rank_eq E h he)
end Reach
namespace PlainL
variable {S:Type u} {P:Specification S} {C:Set (Set S)} {I J:Set S}
theorem predecessor_path (h:PlainL P C J) (hp:Reach (SecEdge P C) I J) :
    PlainL P C I:=by
  obtain ⟨b,hp⟩:=hp
  induction hp with
  | nil => exact h
  | cons he _ ih => exact (ih h).predecessor he
theorem component_plain (h:PlainL P C I) :
    ∀ J ∈ Reach.component (SecEdge P C) I,PlainL P C J:=by
  intro J hJ
  exact h.predecessor_path hJ.2
end PlainL
namespace IsComp
variable {V:Type u} {E:V → V → Bool → Prop} {C:Set V}
open Classical
noncomputable def signing (hc:IsComp E C) (v:V):Bool :=
  if h:v ∈ C then (hc.connected hc.choose_spec.1 h).choose else false
theorem signing_path (hc:IsComp E C) {v:V} (hv:v ∈ C) :
    SignedPath E hc.choose v (hc.signing v):=by
  unfold signing
  rw [dif_pos hv]
  exact (hc.connected hc.choose_spec.1 hv).choose_spec
theorem signing_cross (hc:IsComp E C)
    (hn:∀ v ∈ C,¬ SignedPath E v v true)
    {v w:V} {p:Bool} (hv:v ∈ C) (hw:w ∈ C) (hp:SignedPath E v w p) :
    hc.signing w = Bool.xor (hc.signing v) p:=by
  exact (hc.signing_path hw).parity_unique ((hc.signing_path hv).append hp)
    (hc.connected hw hc.choose_spec.1) (hn _ hc.choose_spec.1)
end IsComp
end S_wpc_barendregt_geuvers_klop
end OMA
namespace OMA
namespace S_wpc_barendregt_geuvers_klop
universe u
namespace Profile
variable {S:Type u} {P:Specification S} {Γ:List (Expr S)}
theorem nonempty_of_sorted (hw:SystemWeaklyNormalizing P) {M:Expr S} {s:S}
    (h:HasType P Γ M (.sort s)):(Profile P Γ M).Nonempty :=
  ⟨s,h.nfTerm hw⟩
theorem context_head_conversion {A A' M:Expr S} {s t:S}
    (hA:HasType P Γ A (.sort s)) (hA':HasType P Γ A' (.sort t))
    (hc:Converts A A'):Profile P (A :: Γ) M = Profile P (A' :: Γ) M:=by
  ext r
  exact ⟨fun h => HasType.context_head_conversion h hA hA' hc,
    fun h => HasType.context_head_conversion h hA' hA (.symm _ _ hc)⟩
theorem inclusion_path {I J:Set S} (hI:FeasibleProfile P I)
    (hJ:FeasibleProfile P J) (h:J ⊆ I):PositivePath (PriEdge P) I J:=by
  classical
  by_cases he:I = J
  · subst J; exact .refl
  · exact .single (.inclusion hI hJ (Set.ssubset_iff_subset_ne.mpr ⟨h,Ne.symm he⟩))
theorem triple (hw:SystemWeaklyNormalizing P) {D E:Expr S} {s:S}
    (h:HasType P Γ (.pi D E) (.sort s)) :
    ProfileTriple P (Profile P Γ D) (Profile P (D :: Γ) E) (Profile P Γ (.pi D E)):=by
  obtain ⟨a,b,c,hD,hE,_,_⟩:=h.generation_pi
  have wD:=hD.weakNorm hw
  have wE:=hE.weakNorm hw
  have hD':=hD.nfTerm hw
  have he:Profile P (D.nfTerm :: Γ) E = Profile P (D :: Γ) E :=
    (context_head_conversion hD hD' (Expr.nfTerm_spec wD).1.converts).symm
  refine ⟨feasible wD (nonempty_of_sorted hw hD),
    feasible wE (nonempty_of_sorted hw hE),
    feasible (h.weakNorm hw) (nonempty_of_sorted hw h),?_⟩
  calc
    Profile P Γ (.pi D E) = Profile P Γ (.pi D.nfTerm E.nfTerm):=by
      rw [← Expr.nfTerm_pi wD wE,Profile.nfTerm]
    _ = OutProfile P (Profile P Γ D.nfTerm)
        (Profile P (D.nfTerm :: Γ) E.nfTerm) :=
      pi (Expr.nfTerm_spec wD).2 (Expr.nfTerm_spec wE).2
    _ = OutProfile P (Profile P Γ D) (Profile P (D :: Γ) E):=by
      rw [Profile.nfTerm,Profile.nfTerm,he]
theorem instantiate_product_path (hw:SystemWeaklyNormalizing P)
    {D E n:Expr S} {s:S} (h:HasType P Γ (.pi D E) (.sort s))
    (hn:HasType P Γ n D) :
    PositivePath (PriEdge P) (Profile P Γ (E.instantiate n))
      (Profile P Γ (.pi D E)):=by
  obtain ⟨a,b,c,hD,hE,_,_⟩:=h.generation_pi
  have hout:=hE.instantiate hn
  have hg:=growth hw (hE.weakNorm hw) hn.valid _ (TySub.single hn)
  have hp:=inclusion_path
    (feasible (hout.weakNorm hw) (nonempty_of_sorted hw hout))
    (feasible (hE.weakNorm hw) (nonempty_of_sorted hw hE)) hg
  exact hp.trans (.single (.codomain (triple hw h)))
end Profile
namespace Expr
variable {S:Type u}
def head:Expr S → Expr S
  | .app f _ => head f
  | M => M
@[simp] theorem head_apps (M:Expr S) (ns:List (Expr S)):(M.apps ns).head = M.head:=by
  induction ns generalizing M with
  | nil => rfl
  | cons n ns ih => exact ih (.app M n)
end Expr
namespace HasType
variable {S:Type u} {P:Specification S} {Γ:List (Expr S)}
theorem neutral_profile_ascent (hw:SystemWeaklyNormalizing P)
    {M T:Expr S} (hn:Neutral M) (h:HasType P Γ M T) :
    ∃ n D,M.head = .var n ∧ Lookup Γ n D ∧
      PositivePath (PriEdge P) (Profile P Γ T) (Profile P Γ D):=by
  induction hn generalizing T with
  | var n =>
      obtain ⟨D,hD,hc⟩:=h.generation
      refine ⟨n,D,rfl,hD,?_⟩
      rw [Profile.converts (h.type_weakNorm hw)
        ((HasType.lookup h.valid hD).type_weakNorm hw) hc]
      exact .refl
  | @app f a hnf ih =>
      obtain ⟨D,E,hf,ha,hc⟩:=h.generation_app
      obtain ⟨s,hp⟩:=hf.product_type_sorted
      obtain ⟨n,A,hh,hl,hr⟩:=ih hf
      refine ⟨n,A,hh,hl,?_⟩
      rw [Profile.converts (h.type_weakNorm hw)
        ((HasType.application hf ha).type_weakNorm hw) hc]
      exact (Profile.instantiate_product_path hw hp ha).trans hr
theorem neutral_profile_seed (hw:SystemWeaklyNormalizing P)
    {M:Expr S} {s:S} (hn:Neutral M) (hM:Normal M)
    (h:HasType P Γ M (.sort s)) :
    Profile P Γ M = {s} ∧ (AxProfile P s).Nonempty ∧
      ∃ n D,M.head = .var n ∧ Lookup Γ n D ∧
        PositivePath (PriEdge P) (AxProfile P s) (Profile P Γ D):=by
  refine ⟨Profile.neutral hM hn h,Profile.neutral_axiom hn h,?_⟩
  simpa only [Profile.sort h.valid] using neutral_profile_ascent hw hn h
end HasType
namespace Neutral
variable {S:Type u} {M N:Expr S}
theorem rename (h:Neutral M) (ρ:Nat → Nat):Neutral (M.rename ρ):=by
  induction h with
  | var n => exact .var _
  | app h ih => exact .app ih
theorem subst_of_head (h:Neutral M) (σ:Nat → Expr S)
    (hh:∀ n,M.head = .var n → Neutral (σ n)):Neutral (M.subst σ):=by
  induction h with
  | var n => exact hh n rfl
  | app h ih => exact .app (ih hh)
theorem beta (h:Neutral M) (hr:Beta M N):Neutral N:=by
  induction h generalizing N with
  | var n => cases hr
  | @app f a h ih =>
      cases hr with
      | app_left hr => exact .app (ih hr)
      | app_right _ => exact .app h
      | head => cases h
theorem reduces (h:Neutral M) (hr:Reduces M N):Neutral N:=by
  induction hr with
  | refl => exact h
  | tail _ hr ih => exact ih.beta hr
theorem nfTerm (h:Neutral M) (hw:WeaklyNormalizing M):Neutral M.nfTerm :=
  h.reduces (Expr.nfTerm_spec hw).1
end Neutral
namespace Profile
variable {S:Type u} {P:Specification S}
theorem rename_normal {Γ Δ:List (Expr S)} {T:Expr S} {s:S}
    (hT:HasType P Γ T (.sort s)) (hn:Normal T)
    (hΔ:ValidContext P Δ) (ρ:Nat → Nat)
    (hρ:∀ n B,Lookup Γ n B → HasType P Δ (.var (ρ n)) (B.rename ρ)) :
    Profile P Δ (T.rename ρ) = Profile P Γ T:=by
  induction T generalizing Γ Δ s ρ with
  | var n =>
      rw [neutral (hn.rename ρ) (.var _) (hT.rename hΔ ρ hρ),neutral hn (.var _) hT]
  | sort t =>
      exact (sort hΔ t).trans (sort hT.valid t).symm
  | app f a ihf iha =>
      have hneutral:Neutral (.app f a):=by
        obtain ⟨t,he⟩ | h | ⟨D,E,he⟩:=hT.sorted_normal_shape hn
        · cases he
        · exact h
        · cases he
      rw [neutral (hn.rename ρ) (hneutral.rename ρ) (hT.rename hΔ ρ hρ),
        neutral hn hneutral hT]
  | lam A b ihA ihb => exact False.elim hT.lambda_cannot_have_sort_type
  | pi A B ihA ihB =>
      obtain ⟨a,b,c,hA,hB,_,_⟩:=hT.generation_pi
      have hA':=hA.rename hΔ ρ hρ
      have hr:∀ n D,Lookup (A :: Γ) n D →
          HasType P (A.rename ρ :: Δ) (.var (Expr.liftRen ρ n))
            (D.rename (Expr.liftRen ρ)):=by
        intro n D hD
        cases hD with
        | zero =>
            simpa only [Expr.liftRen,Expr.rename_comp,Function.comp_def] using HasType.var hA'
        | succ _ hD =>
            simpa only [Expr.liftRen,Expr.rename_comp,Function.comp_def,Expr.rename] using
              HasType.weaken (hρ _ _ hD) hA'
      rw [Expr.rename,pi (hn.pi_domain.rename ρ) (hn.pi_body.rename _),pi hn.pi_domain hn.pi_body,
        ihA hA hn.pi_domain hΔ ρ hρ,
        ihB hB hn.pi_body (.cons hΔ hA') _ hr]
theorem rename (hw:SystemWeaklyNormalizing P)
    {Γ Δ:List (Expr S)} {T:Expr S} {s:S}
    (hT:HasType P Γ T (.sort s)) (hΔ:ValidContext P Δ) (ρ:Nat → Nat)
    (hρ:∀ n B,Lookup Γ n B → HasType P Δ (.var (ρ n)) (B.rename ρ)) :
    Profile P Δ (T.rename ρ) = Profile P Γ T:=by
  rw [← nfTerm T,← nfTerm (T.rename ρ),Expr.nfTerm_rename (hT.weakNorm hw) ρ]
  exact rename_normal (hT.nfTerm hw) (Expr.nfTerm_spec (hT.weakNorm hw)).2 hΔ ρ hρ
theorem weaken (hw:SystemWeaklyNormalizing P) {Γ:List (Expr S)}
    {T D:Expr S} {s t:S} (hT:HasType P Γ T (.sort s))
    (hD:HasType P Γ D (.sort t)) :
    Profile P (D :: Γ) (T.rename Nat.succ) = Profile P Γ T :=
  rename hw hT (.cons hD.valid hD) Nat.succ
    (fun _ _ hn => .weaken (HasType.lookup hD.valid hn) hD)
end Profile
def SingleSource {S:Type u} (P:Specification S) (Γ:List (Expr S))
    (σ:Nat → Expr S) (I:Set S):Prop :=
  ∀ n D,Lookup Γ n D → ¬ Neutral (σ n) → Profile P Γ D = I
namespace SingleSource
variable {S:Type u} {P:Specification S} {Γ:List (Expr S)}
    {σ:Nat → Expr S} {I:Set S}
theorem single (hw:SystemWeaklyNormalizing P) {D q:Expr S} {s:S}
    (hD:HasType P Γ D (.sort s)) :
    SingleSource P (D :: Γ) (Expr.single q) (Profile P Γ D):=by
  intro n A hn hbad
  cases hn with
  | zero => exact Profile.weaken hw hD hD
  | succ _ _ => exact False.elim (hbad (.var _))
theorem lift (hw:SystemWeaklyNormalizing P) (h:SingleSource P Γ σ I)
    {D:Expr S} {s:S} (hD:HasType P Γ D (.sort s)) :
    SingleSource P (D :: Γ) (Expr.liftSub σ) I:=by
  intro n A hn hbad
  cases hn with
  | zero => exact False.elim (hbad (.var 0))
  | succ _ hn =>
      obtain ⟨t,hA⟩:=HasType.lookup_sorted hD.valid hn
      rw [Profile.weaken hw hA hD]
      exact h _ _ hn (fun hh => hbad (hh.rename Nat.succ))
end SingleSource
namespace ForbiddenConfiguration
variable {S:Type u} {P:Specification S} {C D:Set (Set S)}
theorem of_neutral_expansion (hw:SystemWeaklyNormalizing P)
    (hD:IsComp (SecEdge P C) D) (hplain:∀ I ∈ D,PlainL P C I)
    (hneg:∃ I ∈ D,∃ K ∈ D,SecEdge P C I K true)
    {I J K:Set S} (htr:ProfileTriple P I J K) (hJ:J ∈ D) (hK:K ∈ D)
    {Γ Δ:List (Expr S)} (hΔ:ValidContext P Δ) {σ:Nat → Expr S}
    (hσ:TySub P Γ Δ σ) (hsrc:SingleSource P Γ σ I)
    {M A B:Expr S} {s:S} (h:HasType P Γ M (.sort s))
    (hn:Normal M) (hne:Neutral M) (hM:Profile P Γ M ∈ D)
    (he:(M.subst σ).nfTerm = .pi A B):ForbiddenConfiguration P C:=by
  obtain ⟨hp,hax,n,F,hh,hf,hpath⟩:=h.neutral_profile_seed hw hne hn
  have hbad:¬ Neutral (σ n):=by
    intro hs
    have hM':=hne.subst_of_head σ (by
      intro m hm
      have heq:m = n:=by simpa only [hh,Expr.var.injEq] using hm.symm
      exact heq.symm ▸ hs)
    have hnorm:=hM'.nfTerm ((h.subst hΔ σ hσ).weakNorm hw)
    rw [he] at hnorm
    cases hnorm
  have hF:=hsrc n F hf hbad
  rw [hF] at hpath
  exact ⟨D,hD,hplain,hneg,I,J,K,s,htr,hJ,hK,hp ▸ hM,hax,hpath⟩
end ForbiddenConfiguration
namespace ObsLayers
variable {S:Type u} {P:Specification S} {C:Set (Set S)} {I J:Set S}
theorem positive (h:I ∈ ObsLayers P C) (hp:PositivePath (PriEdge P) I J) :
    J ∈ ObsLayers P C:=by
  obtain ⟨s,hs,hax,hpath⟩:=h
  exact ⟨s,hs,hax,hpath.trans hp⟩
theorem secondary (h:I ∈ ObsLayers P C) (hp:PositivePath (PriEdge P) I J) :
    PositivePath (SecEdge P C) I J:=by
  induction hp with
  | refl => exact .refl
  | @tail J K hp he ih =>
      exact .tail ih (.positive (positive h hp) (positive h (.tail hp he)) he)
end ObsLayers
namespace ActL
variable {S:Type u} {P:Specification S} {C:Set (Set S)} {I J:Set S}
theorem layer (h:ActL P C I):I ∈ ObsLayers P C:=by
  obtain ⟨D,hD,b,hp⟩:=h
  cases hp with
  | nil => exact hD.1
  | cons he _ => cases he with
    | positive hI _ _ => exact hI
    | negative hI _ _ _ => exact hI
theorem predecessor (h:ActL P C J) (hp:Reach (SecEdge P C) I J) :
    ActL P C I:=by
  obtain ⟨D,hD,hr⟩:=h
  exact ⟨D,hD,hp.trans hr⟩
end ActL
namespace IsComp
variable {S:Type u} {P:Specification S} {C D:Set (Set S)}
theorem codomain_interpolation (hD:IsComp (SecEdge P C) D)
    (hl:∀ X ∈ D,X ∈ ObsLayers P C)
    {I J K J':Set S} (htr:ProfileTriple P I J K) (hK:K ∈ D) (hJ':J' ∈ D)
    (hJJ':PositivePath (PriEdge P) J' J):J ∈ D:=by
  have hJH:=ObsLayers.positive (hl J' hJ') hJJ'
  exact hD.between hJ' hK (ObsLayers.secondary (hl J' hJ') hJJ').reach
    (Reach.single (.positive hJH (hl K hK) (.codomain htr)))
theorem domain_interpolation (hD:IsComp (SecEdge P C) D)
    (hl:∀ X ∈ D,X ∈ ObsLayers P C)
    (ha:∀ X ∈ D,ActL P C X)
    {I J K I' J':Set S} (htr:ProfileTriple P I J K) (hK:K ∈ D)
    (hI':I' ∈ D) (hJ':ActL P C J')
    (hII':PositivePath (PriEdge P) I' I)
    (hJJ':PositivePath (PriEdge P) J' J) :
    I ∈ D ∧ ActL P C J:=by
  have hIH:=ObsLayers.positive (hl I' hI') hII'
  have hJH:=ObsLayers.positive hJ'.layer hJJ'
  have hKH:=hl K hK
  exact ⟨hD.between hI' hK (ObsLayers.secondary (hl I' hI') hII').reach
    (Reach.single (.negative hIH hJH hKH htr)),
    (ha K hK).predecessor (Reach.single (.positive hJH hKH (.codomain htr)))⟩
end IsComp
namespace Profile
variable {S:Type u} {P:Specification S} {Γ Δ:List (Expr S)}
theorem growth_path (hw:SystemWeaklyNormalizing P) {T:Expr S} {s:S}
    (hT:HasType P Γ T (.sort s)) (hΔ:ValidContext P Δ) (σ:Nat → Expr S)
    (hσ:TySub P Γ Δ σ) :
    PositivePath (PriEdge P) (Profile P Δ (T.subst σ)) (Profile P Γ T):=by
  have ht:=hT.subst hΔ σ hσ
  exact inclusion_path (feasible (ht.weakNorm hw) (nonempty_of_sorted hw ht))
    (feasible (hT.weakNorm hw) (nonempty_of_sorted hw hT))
    (growth hw (hT.weakNorm hw) hΔ σ hσ)
end Profile
structure ContextEquivalent {S:Type u} (P:Specification S)
    (Γ Δ:List (Expr S)):Prop where
  valid_left:ValidContext P Γ
  valid_right:ValidContext P Δ
  typing:∀ (M A:Expr S),HasType P Γ M A ↔ HasType P Δ M A
namespace ContextEquivalent
variable {S:Type u} {P:Specification S} {Γ Δ:List (Expr S)}
theorem symm (h:ContextEquivalent P Γ Δ):ContextEquivalent P Δ Γ :=
  ⟨h.valid_right,h.valid_left,fun _ _ => (h.typing _ _).symm⟩
theorem profile (h:ContextEquivalent P Γ Δ) (M:Expr S) :
    Profile P Γ M = Profile P Δ M:=by
  ext s
  exact h.typing _ _
theorem cons (h:ContextEquivalent P Γ Δ) {A:Expr S} {s:S}
    (hA:HasType P Γ A (.sort s)):ContextEquivalent P (A :: Γ) (A :: Δ):=by
  have lift_dir {Γ Δ:List (Expr S)} (h:ContextEquivalent P Γ Δ)
      (hA:HasType P Γ A (.sort s)) :
      ∀ M B,HasType P (A :: Γ) M B → HasType P (A :: Δ) M B:=by
    intro M B ht
    have hA':=(h.typing _ _).1 hA
    have hs:TySub P (A :: Γ) (A :: Δ) Expr.var:=by
      intro n D hn
      rw [Expr.subst_var]
      cases hn with
      | zero => exact .var hA'
      | succ _ hn => exact .weaken ((h.typing _ _).1 (HasType.lookup h.valid_left hn)) hA'
    simpa only [Expr.subst_var] using ht.subst (.cons h.valid_right hA') _ hs
  have hA':=(h.typing _ _).1 hA
  exact ⟨.cons h.valid_left hA,.cons h.valid_right hA',
    fun M B => ⟨lift_dir h hA M B,lift_dir h.symm hA' M B⟩⟩
theorem head_conversion {A B:Expr S} {s t:S}
    (hA:HasType P Γ A (.sort s)) (hB:HasType P Γ B (.sort t))
    (hc:Converts A B):ContextEquivalent P (A :: Γ) (B :: Γ) :=
  ⟨.cons hA.valid hA,.cons hB.valid hB,fun _ _ =>
    ⟨fun h => h.context_head_conversion hA hB hc,
      fun h => h.context_head_conversion hB hA (.symm _ _ hc)⟩⟩
end ContextEquivalent
namespace PlainObservations
open Classical
variable {S:Type u}
noncomputable def potential (P:Specification S) (C D:Set (Set S))
    (Γ:List (Expr S)):Expr S → Nat
  | .pi A B => by
      classical
      exact 1 +
      (if Profile P Γ A ∈ D ∧ ActL P C (Profile P (A :: Γ) B)
       then potential P C D Γ A else 0) +
      (if Profile P (A :: Γ) B ∈ D then potential P C D (A :: Γ) B else 0)
  | _ => 1
variable {P:Specification S} {C D:Set (Set S)}
theorem potential_context {Γ Δ:List (Expr S)} {T:Expr S} {s:S}
    (hT:HasType P Γ T (.sort s)) (h:ContextEquivalent P Γ Δ) :
    potential P C D Γ T = potential P C D Δ T:=by
  induction T generalizing Γ Δ s with
  | var n | sort t | app f a | lam A b => rfl
  | pi A B ihA ihB =>
      obtain ⟨a,b,c,hA,hB,_,_⟩:=hT.generation_pi
      simp only [potential]
      rw [h.profile A,(h.cons hA).profile B,ihA hA h,ihB hB (h.cons hA)]
theorem potential_normalized_pi (hw:SystemWeaklyNormalizing P)
    {Γ:List (Expr S)} {A B:Expr S} {s:S}
    (h:HasType P Γ (.pi A B) (.sort s)) :
    potential P C D Γ (Expr.pi A B).nfTerm = 1 +
      (if Profile P Γ A ∈ D ∧ ActL P C (Profile P (A :: Γ) B)
       then potential P C D Γ A.nfTerm else 0) +
      (if Profile P (A :: Γ) B ∈ D then potential P C D (A :: Γ) B.nfTerm else 0):=by
  classical
  obtain ⟨a,b,c,hA,hB,_,_⟩:=h.generation_pi
  have wA:=hA.weakNorm hw
  have wB:=hB.weakNorm hw
  have hc:=ContextEquivalent.head_conversion hA (hA.nfTerm hw) (Expr.nfTerm_spec wA).1.converts
  have hp:=(potential_context (C:=C) (D:=D) (hB.nfTerm hw) hc).symm
  rw [Expr.nfTerm_pi wA wB,potential,← hc.profile B.nfTerm,hp,
    Profile.nfTerm,Profile.nfTerm]
theorem potential_subst_le (hw:SystemWeaklyNormalizing P)
    (hno:¬ ForbiddenConfiguration P C)
    (hD:IsComp (SecEdge P C) D) (hplain:∀ I ∈ D,PlainL P C I)
    (hneg:∃ I ∈ D,∃ K ∈ D,SecEdge P C I K true)
    {I J K:Set S} (htr:ProfileTriple P I J K) (hJ:J ∈ D) (hK:K ∈ D)
    {Γ Δ:List (Expr S)} (hΔ:ValidContext P Δ) {σ:Nat → Expr S}
    (hσ:TySub P Γ Δ σ) (hsrc:SingleSource P Γ σ I)
    {T:Expr S} {s:S} (hT:HasType P Γ T (.sort s)) (hn:Normal T)
    (hTC:Profile P Γ T ∈ D) :
    potential P C D Δ (T.subst σ).nfTerm ≤ potential P C D Γ T:=by
  classical
  have ha:∀ X ∈ D,ActL P C X:=fun X hX => (hplain X hX).active
  have hl:∀ X ∈ D,X ∈ ObsLayers P C:=fun X hX => (ha X hX).layer
  have leaf {Γ Δ:List (Expr S)} {σ:Nat → Expr S} {M:Expr S} {s:S}
      (hΔ:ValidContext P Δ) (hσ:TySub P Γ Δ σ)
      (hsrc:SingleSource P Γ σ I) (hM:HasType P Γ M (.sort s))
      (hn:Normal M) (hne:Neutral M) (hMC:Profile P Γ M ∈ D) :
      potential P C D Δ (M.subst σ).nfTerm = 1:=by
    cases he:(M.subst σ).nfTerm with
    | pi A B =>
        exact False.elim (hno (ForbiddenConfiguration.of_neutral_expansion hw hD hplain hneg
          htr hJ hK hΔ hσ hsrc hM hn hne hMC he))
    | var n | sort t | app f a | lam A b => rfl
  induction T generalizing Γ Δ σ s with
  | var n => exact le_of_eq (leaf hΔ hσ hsrc hT hn (.var n) hTC)
  | sort t => simp only [Expr.subst,Expr.nfTerm_of_normal (Normal.sort t),potential,le_refl]
  | lam A b => exact False.elim hT.lambda_cannot_have_sort_type
  | app f a ihf iha =>
      have hneutral:Neutral (.app f a):=by
        obtain ⟨t,he⟩ | h | ⟨A,B,he⟩:=hT.sorted_normal_shape hn
        · cases he
        · exact h
        · cases he
      exact le_of_eq (leaf hΔ hσ hsrc hT hn hneutral hTC)
  | pi A B ihA ihB =>
      obtain ⟨a,b,c,hA,hB,_,_⟩:=hT.generation_pi
      have hA':=hA.subst hΔ σ hσ
      have hΔ':ValidContext P (A.subst σ :: Δ):=.cons hΔ hA'
      have hσ':=hσ.lift hA'
      have hB':=hB.subst hΔ' _ hσ'
      have htr':=Profile.triple hw hT
      have hAp:=Profile.growth_path hw hA hΔ σ hσ
      have hBp:=Profile.growth_path hw hB hΔ' _ hσ'
      rw [Expr.subst,potential_normalized_pi hw (hT.subst hΔ σ hσ),potential]
      apply Nat.add_le_add
      · apply Nat.add_le_add_left
        split_ifs with hc hc'
        · exact ihA hΔ hσ hsrc hA hn.pi_domain hc'.1
        · obtain ⟨hAC,hBa⟩:=hD.domain_interpolation hl ha htr' hTC hc.1 hc.2 hAp hBp
          exact False.elim (hc' ⟨hAC,hBa⟩)
        · exact Nat.zero_le _
        · exact le_rfl
      · split_ifs with hc hc'
        · exact ihB hΔ' hσ' (hsrc.lift hw hA) hB hn.pi_body hc'
        · exact False.elim (hc' (hD.codomain_interpolation hl htr' hTC hc hBp))
        · exact Nat.zero_le _
        · exact le_rfl
theorem frame_potential_drop (hw:SystemWeaklyNormalizing P)
    (hno:¬ ForbiddenConfiguration P C)
    (hD:IsComp (SecEdge P C) D) (hplain:∀ I ∈ D,PlainL P C I)
    (hneg:∃ I ∈ D,∃ K ∈ D,SecEdge P C I K true)
    {Γ:List (Expr S)} {A B n:Expr S} {s:S}
    (hT:HasType P Γ (.pi A B) (.sort s)) (hnT:Normal (.pi A B))
    (hn:HasType P Γ n A) (hK:Profile P Γ (.pi A B) ∈ D)
    (hL:Profile P Γ (B.instantiate n) ∈ D) :
    potential P C D Γ (B.instantiate n).nfTerm ≤ potential P C D (A :: Γ) B ∧
      potential P C D (A :: Γ) B < potential P C D Γ (.pi A B):=by
  have ha:∀ X ∈ D,ActL P C X:=fun X hX => (hplain X hX).active
  have hl:∀ X ∈ D,X ∈ ObsLayers P C:=fun X hX => (ha X hX).layer
  obtain ⟨a,b,c,hA,hB,_,_⟩:=hT.generation_pi
  have htr:=Profile.triple hw hT
  have hp:=Profile.growth_path hw hB hn.valid _ (TySub.single hn)
  have hJ:=hD.codomain_interpolation hl htr hK hL hp
  refine ⟨potential_subst_le hw hno hD hplain hneg htr hJ hK hn.valid
    (TySub.single hn) (SingleSource.single hw hA) hB hnT.pi_body hJ,?_⟩
  simp only [potential,if_pos hJ]
  omega
theorem frame_domain_drop (hplain:∀ I ∈ D,PlainL P C I)
    {Γ:List (Expr S)} {A B:Expr S}
    (hI:Profile P Γ A ∈ D) (hJ:Profile P (A :: Γ) B ∈ D) :
    potential P C D Γ A < potential P C D Γ (.pi A B):=by
  have hc:Profile P Γ A ∈ D ∧ ActL P C (Profile P (A :: Γ) B) :=
    ⟨hI,(hplain _ hJ).active⟩
  simp only [potential,if_pos hc,if_pos hJ]
  omega
theorem potential_rename (hw:SystemWeaklyNormalizing P)
    {Γ Δ:List (Expr S)} {T:Expr S} {s:S}
    (hT:HasType P Γ T (.sort s)) (hΔ:ValidContext P Δ) (ρ:Nat → Nat)
    (hρ:∀ n B,Lookup Γ n B → HasType P Δ (.var (ρ n)) (B.rename ρ)) :
    potential P C D Δ (T.rename ρ) = potential P C D Γ T:=by
  induction T generalizing Γ Δ s ρ with
  | var n | sort t | app f a | lam A b => rfl
  | pi A B ihA ihB =>
      obtain ⟨a,b,c,hA,hB,_,_⟩:=hT.generation_pi
      have hA':=hA.rename hΔ ρ hρ
      have hr:∀ n E,Lookup (A :: Γ) n E →
          HasType P (A.rename ρ :: Δ) (.var (Expr.liftRen ρ n))
            (E.rename (Expr.liftRen ρ)):=by
        intro n E hE
        cases hE with
        | zero =>
            simpa only [Expr.liftRen,Expr.rename_comp,Function.comp_def] using HasType.var hA'
        | succ _ hE =>
            simpa only [Expr.liftRen,Expr.rename_comp,Function.comp_def,Expr.rename] using
              HasType.weaken (hρ _ _ hE) hA'
      simp only [Expr.rename,potential]
      rw [Profile.rename hw hA hΔ ρ hρ,
        Profile.rename hw hB (.cons hΔ hA') _ hr,
        ihA hA hΔ ρ hρ,ihB hB (.cons hΔ hA') _ hr]
end PlainObservations
namespace CTower
section
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P)
def profile (T:Expr S):Set S:={s | Ω.HasType T.nfTerm (.sort s)}
variable (hw:SystemWeaklyNormalizing P)
include hw
theorem profile_at_next {n:Nat} {T:Expr S} {s:S}
    (ht:S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.rename (Expr.revIx n)) (.sort s)) :
    Profile P (Ω.context (n+1)) (T.rename (Expr.revIx (n+1))) =
      Profile P (Ω.context n) (T.rename (Expr.revIx n)):=by
  have hs:T.Scoped n:=by
    have h:=ht.scope.1.revIx
    rwa [Ω.length,Expr.revIx_twice] at h
  obtain ⟨D,t,hD,he⟩:=Ω.step n
  rw [he,hs.reverseIndex_succ]
  exact Profile.weaken hw ht hD
theorem profile_at_mono {n m:Nat} {T:Expr S} {s:S}
    (ht:S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.rename (Expr.revIx n)) (.sort s))
    (h:n ≤ m) :
    Profile P (Ω.context m) (T.rename (Expr.revIx m)) =
      Profile P (Ω.context n) (T.rename (Expr.revIx n)):=by
  induction h with
  | refl => rfl
  | @step m h ih => exact (Ω.profile_at_next hw (Ω.at_mono (A:=.sort s) ht h)).trans ih
theorem profile_at {n:Nat} {T:Expr S} {s:S}
    (ht:S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.rename (Expr.revIx n)) (.sort s)) :
    Ω.profile T = Profile P (Ω.context n) (T.rename (Expr.revIx n)):=by
  have w:WeaklyNormalizing T:=(show Ω.HasType T (.sort s) from ⟨n,ht⟩).weakNorm hw
  ext t
  constructor
  · rintro ⟨m,hm⟩
    have hn:=Ω.at_mono (A:=.sort t) hm (le_max_left m n)
    change S_wpc_barendregt_geuvers_klop.HasType P (Ω.context (max m n))
      (T.nfTerm.rename (Expr.revIx (max m n))) (.sort t) at hn
    rw [← Expr.nfTerm_rename w] at hn
    have he:=Ω.profile_at_mono hw ht (le_max_right m n)
    exact he ▸ hn
  · intro hn
    refine ⟨n,?_⟩
    change S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.nfTerm.rename (Expr.revIx n)) (.sort t)
    rw [← Expr.nfTerm_rename w]
    exact hn
omit hw in
theorem profile_nfTerm (T:Expr S):Ω.profile T.nfTerm = Ω.profile T:=by
  simp only [profile,Expr.nfTerm_idem]
theorem profile_feasible {T:Expr S} {s:S} (ht:Ω.HasType T (.sort s)) :
    FeasibleProfile P (Ω.profile T):=by
  obtain ⟨n,hn⟩:=ht
  change S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.rename (Expr.revIx n)) (.sort s) at hn
  rw [Ω.profile_at hw hn]
  exact Profile.feasible (hn.weakNorm hw) (Profile.nonempty_of_sorted hw hn)
theorem potential_at_next (C D:Set (Set S)) {n:Nat} {T:Expr S} {s:S}
    (ht:S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.rename (Expr.revIx n)) (.sort s)) :
    PlainObservations.potential P C D (Ω.context (n+1)) (T.rename (Expr.revIx (n+1))) =
      PlainObservations.potential P C D (Ω.context n) (T.rename (Expr.revIx n)):=by
  have hs:T.Scoped n:=by
    have h:=ht.scope.1.revIx
    rwa [Ω.length,Expr.revIx_twice] at h
  obtain ⟨A,t,hA,he⟩:=Ω.step n
  rw [he,hs.reverseIndex_succ]
  exact PlainObservations.potential_rename hw ht (.cons hA.valid hA) Nat.succ
    (fun _ _ hn => .weaken (S_wpc_barendregt_geuvers_klop.HasType.lookup hA.valid hn) hA)
theorem potential_at_mono (C D:Set (Set S)) {n m:Nat} {T:Expr S} {s:S}
    (ht:S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.rename (Expr.revIx n)) (.sort s))
    (h:n ≤ m) :
    PlainObservations.potential P C D (Ω.context m) (T.rename (Expr.revIx m)) =
      PlainObservations.potential P C D (Ω.context n) (T.rename (Expr.revIx n)):=by
  induction h with
  | refl => rfl
  | @step m h ih =>
      exact (Ω.potential_at_next hw C D (Ω.at_mono (A:=.sort s) ht h)).trans ih
noncomputable def potential (C D:Set (Set S)) (T:Expr S):Nat :=
  if h:∃ n s,S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.rename (Expr.revIx n)) (.sort s)
  then PlainObservations.potential P C D (Ω.context h.choose) (T.rename (Expr.revIx h.choose))
  else 1
theorem potential_at (C D:Set (Set S)) {n:Nat} {T:Expr S} {s:S}
    (ht:S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) (T.rename (Expr.revIx n)) (.sort s)) :
    Ω.potential C D T =
      PlainObservations.potential P C D (Ω.context n) (T.rename (Expr.revIx n)):=by
  have h:∃ m t,S_wpc_barendregt_geuvers_klop.HasType P (Ω.context m) (T.rename (Expr.revIx m)) (.sort t) :=
    ⟨n,s,ht⟩
  rw [potential,dif_pos h]
  obtain ⟨t,hT⟩:=h.choose_spec
  exact (Ω.potential_at_mono hw C D hT (le_max_left h.choose n)).symm.trans
    (Ω.potential_at_mono hw C D ht (le_max_right h.choose n))
theorem frame_profiles {A B q:Expr S} {s:S}
    (hT:Ω.HasType (.pi A B) (.sort s)) (hq:Ω.HasType q A) :
    ∃ J,ProfileTriple P (Ω.profile A) J (Ω.profile (.pi A B)) ∧
      PositivePath (PriEdge P) (Ω.profile (B.instantiate q)) J:=by
  obtain ⟨n,hT,hq⟩:=hT.common hq
  change S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n)
    (.pi (A.rename (Expr.revIx n)) (B.rename (Expr.liftRen (Expr.revIx n)))) (.sort s) at hT
  obtain ⟨a,b,c,hA,hB,_,_⟩:=hT.generation_pi
  have hQ:=hB.instantiate hq
  rw [Expr.instantiate_rename] at hQ
  have htr:=Profile.triple hw hT
  have hp:=Profile.growth_path hw hB hq.valid _ (TySub.single hq)
  change PositivePath (PriEdge P)
    (Profile P (Ω.context n) ((B.rename (Expr.liftRen (Expr.revIx n))).instantiate
      (q.rename (Expr.revIx n)))) _ at hp
  rw [Expr.instantiate_rename] at hp
  refine ⟨Profile P (A.rename (Expr.revIx n) :: Ω.context n)
    (B.rename (Expr.liftRen (Expr.revIx n))),?_,?_⟩
  · rw [Ω.profile_at hw hA,Ω.profile_at hw (T:=.pi A B) hT]
    exact htr
  · rw [Ω.profile_at hw hQ]
    exact hp
omit hw in
theorem domain_sorted {A B:Expr S} {s:S}
    (hT:Ω.HasType (.pi A B) (.sort s)):∃ a,Ω.HasType A (.sort a):=by
  obtain ⟨n,hT⟩:=hT
  obtain ⟨a,b,c,hA,_,_,_⟩:=hT.generation_pi
  exact ⟨a,n,hA⟩
omit hw in
theorem frame_target_sorted {A B q:Expr S} {s:S}
    (hT:Ω.HasType (.pi A B) (.sort s)) (hq:Ω.HasType q A) :
    ∃ b,Ω.HasType (B.instantiate q) (.sort b):=by
  obtain ⟨n,hT,hq⟩:=hT.common hq
  obtain ⟨a,b,c,_,hB,_,_⟩:=hT.generation_pi
  refine ⟨b,n,?_⟩
  have h:=hB.instantiate hq
  change S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n)
    ((B.rename (Expr.liftRen (Expr.revIx n))).instantiate (q.rename (Expr.revIx n)))
    (.sort b) at h
  rw [Expr.instantiate_rename] at h
  exact h
theorem frame_target_drop {C D:Set (Set S)}
    (hno:¬ ForbiddenConfiguration P C)
    (hD:IsComp (SecEdge P C) D) (hplain:∀ I ∈ D,PlainL P C I)
    (hneg:∃ I ∈ D,∃ K ∈ D,SecEdge P C I K true)
    {A B q:Expr S} {s:S} (hT:Ω.HasType (.pi A B) (.sort s))
    (hN:Normal (.pi A B)) (hq:Ω.HasType q A)
    (hK:Ω.profile (.pi A B) ∈ D) (hL:Ω.profile (B.instantiate q) ∈ D) :
    Ω.potential C D (B.instantiate q).nfTerm < Ω.potential C D (.pi A B):=by
  obtain ⟨n,hT,hq⟩:=hT.common hq
  change S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n)
    (.pi (A.rename (Expr.revIx n)) (B.rename (Expr.liftRen (Expr.revIx n)))) (.sort s) at hT
  obtain ⟨a,b,c,hA,hB,_,_⟩:=hT.generation_pi
  have hQ:=hB.instantiate hq
  rw [Expr.instantiate_rename] at hQ
  have wQ:WeaklyNormalizing (B.instantiate q) :=
    (show Ω.HasType (B.instantiate q) (.sort b) from ⟨n,hQ⟩).weakNorm hw
  have hQN:=hQ.nfTerm hw
  rw [Expr.nfTerm_rename wQ] at hQN
  rw [Ω.potential_at hw C D hQN,Ω.potential_at hw C D (T:=.pi A B) hT,
    ← Expr.nfTerm_rename wQ,← Expr.instantiate_rename]
  rw [Ω.profile_at hw (T:=.pi A B) hT] at hK
  rw [Ω.profile_at hw hQ,← Expr.instantiate_rename] at hL
  have hh:=PlainObservations.frame_potential_drop hw hno hD hplain hneg hT
    (hN.rename _) hq hK hL
  exact lt_of_le_of_lt hh.1 hh.2
theorem frame_domain_drop {C D:Set (Set S)}
    {A B q:Expr S} {s:S} (hT:Ω.HasType (.pi A B) (.sort s)) (hq:Ω.HasType q A)
    (hK:ActL P C (Ω.profile (.pi A B)))
    (hL:ActL P C (Ω.profile (B.instantiate q)))
    (hI:Ω.profile A ∈ D) :
    Ω.potential C D A < Ω.potential C D (.pi A B):=by
  obtain ⟨n,hT,hq⟩:=hT.common hq
  change S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n)
    (.pi (A.rename (Expr.revIx n)) (B.rename (Expr.liftRen (Expr.revIx n)))) (.sort s) at hT
  obtain ⟨a,b,c,hA,hB,_,_⟩:=hT.generation_pi
  have hQ:=hB.instantiate hq
  rw [Expr.instantiate_rename] at hQ
  have hp:=Profile.growth_path hw hB hq.valid _ (TySub.single hq)
  change PositivePath (PriEdge P)
    (Profile P (Ω.context n) ((B.rename (Expr.liftRen (Expr.revIx n))).instantiate
      (q.rename (Expr.revIx n)))) _ at hp
  rw [Expr.instantiate_rename,← Ω.profile_at hw hQ] at hp
  have hJH:=ObsLayers.positive hL.layer hp
  have hJ:=hK.predecessor (Reach.single (SecEdge.positive hJH hK.layer
    (by rw [Ω.profile_at hw (T:=.pi A B) hT]; exact .codomain (Profile.triple hw hT))))
  have hc:Profile P (Ω.context n) (A.rename (Expr.revIx n)) ∈ D ∧
      ActL P C (Profile P (A.rename (Expr.revIx n) :: Ω.context n)
        (B.rename (Expr.liftRen (Expr.revIx n)))):=by
    exact ⟨Ω.profile_at hw hA ▸ hI,hJ⟩
  rw [Ω.potential_at hw C D hA,Ω.potential_at hw C D (T:=.pi A B) hT]
  simp only [Expr.rename,PlainObservations.potential,if_pos hc]
  omega
end
variable {S:Type u} {P:Specification S} (Ω:CTower P)
theorem profile_subst_growth (hw:SystemWeaklyNormalizing P) {Γ:List (Expr S)}
    {T:Expr S} {s:S} {σ:Nat → Expr S} (ht:S_wpc_barendregt_geuvers_klop.HasType P Γ T (.sort s))
    (hσ:Ω.TySub Γ σ):Profile P Γ T ⊆ Ω.profile (T.subst σ):=by
  obtain ⟨k,hk⟩:=TySub.common_stage hσ
  let σ':=fun n => (σ n).rename (Expr.revIx k)
  have hs:S_wpc_barendregt_geuvers_klop.TySub P Γ (Ω.context k) σ':=by
    intro n A hn
    simpa only [σ',← Expr.rename_subst] using hk n A hn
  have hT:=ht.subst (Ω.valid k) σ' hs
  have hp:=Profile.growth hw (ht.weakNorm hw) (Ω.valid k) σ' hs
  have he:T.subst σ' = (T.subst σ).rename (Expr.revIx k):=(Expr.rename_subst _ _ _).symm
  rw [he] at hT hp
  rwa [Ω.profile_at hw hT]
end CTower
end S_wpc_barendregt_geuvers_klop
end OMA
namespace OMA
namespace S_wpc_barendregt_geuvers_klop
universe u v
def Expected {S:Type u} (P:Specification S) (Γ:List (Expr S)) (A:Expr S):Prop :=
  (∃ s,A = .sort s) ∨ ∃ s,HasType P Γ A (.sort s)
namespace Expected
variable {S:Type u} {P:Specification S} {Γ:List (Expr S)} {A D:Expr S}
theorem of_type {M:Expr S} (h:HasType P Γ M A):Expected P Γ A:=h.regularity
theorem sorted {s:S} (h:HasType P Γ A (.sort s)):Expected P Γ A:=.inr ⟨s,h⟩
theorem wn (hw:SystemWeaklyNormalizing P) (h:Expected P Γ A):WeaklyNormalizing A:=by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact ⟨_,.refl,Normal.sort s⟩
  · exact h.weakNorm hw
theorem weaken {s:S} (h:Expected P Γ A) (hD:HasType P Γ D (.sort s)) :
    Expected P (D :: Γ) (A.rename Nat.succ):=by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact .inl ⟨s,rfl⟩
  · exact .inr ⟨s,.weaken h hD⟩
end Expected
namespace Expr
variable {S:Type u}
def extend (σ:Nat → Expr S) (n:Expr S):Nat → Expr S
  | 0 => n
  | i+1 => σ i
@[simp] theorem extend_zero (σ:Nat → Expr S) (n:Expr S):extend σ n 0 = n:=rfl
@[simp] theorem extend_succ (σ:Nat → Expr S) (n:Expr S) (i:Nat):extend σ n (i+1) = σ i:=rfl
@[simp] theorem subst_raise_extend (M n:Expr S) (σ:Nat → Expr S) :
    (M.rename Nat.succ).subst (extend σ n) = M.subst σ:=by
  rw [subst_rename]; rfl
@[simp] theorem instantiate_extended (M n:Expr S) (σ:Nat → Expr S) :
    (M.subst (liftSub σ)).instantiate n = M.subst (extend σ n):=by
  rw [instantiate,subst_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => exact subst_lift_single (σ i) n
end Expr
structure Processed {S:Type u} {P:Specification S} (Ω:CTower P)
    (U C:Set (Set S)):Prop where
  disjoint:Disjoint U C
  closed:∀ {I J},J ∈ U → Reach (PriEdge P) I J → I ∈ U
  before:∀ {I J},J ∈ C → Reach (PriEdge P) I J → I ∈ U ∨ I ∈ C
  invariant:∀ {T},Cands.ActualType Ω T → Ω.profile T ∈ U →
    Cands.Ground Ω T = Cands.Top Ω T
structure ComponentInterface {S:Type u} {P:Specification S} (Ω:CTower P)
    (hw:SystemWeaklyNormalizing P) (C:Set (Set S)) where
  Env:List (Expr S) → Type v
  images:{Γ:List (Expr S)} → Env Γ → Nat → Expr S
  typed:∀ {Γ} (e:Env Γ),Ω.TySub Γ (images e)
  inhabit:∀ {Γ} (σ:Nat → Expr S),Ω.TySub Γ σ →
    ∃ e:Env Γ,images e = σ
  Ext:{Γ:List (Expr S)} → {D:Expr S} → Env Γ → Env (D :: Γ) → Expr S → Prop
  ext_images:∀ {Γ D} {e:Env Γ} {e':Env (D :: Γ)} {n},Ext e e' n →
    images e' = Expr.extend (images e) n
  extend:∀ {Γ D s} (e:Env Γ),HasType P Γ D (.sort s) → ∀ n,
    Ω.HasType n (D.subst (images e)) → ∃ e':Env (D :: Γ),Ext e e' n
  R:{Γ:List (Expr S)} → Expr S → Env Γ → Set (Expr S)
  candidate:∀ {Γ A} (e:Env Γ),Expected P Γ A →
    Cands.IsCandidate Ω (A.subst (images e)).nfTerm (R A e)
  conversion:∀ {Γ A B} (e:Env Γ),Expected P Γ A → Expected P Γ B →
    Converts A B → R A e = R B e
  outside:∀ {Γ A} (e:Env Γ),Expected P Γ A →
    (Profile P Γ A ∉ C ∨ Ω.profile (A.subst (images e)) ∉ C) →
    R A e = Cands.Top Ω (A.subst (images e)).nfTerm
  weakening:∀ {Γ D A s} {e:Env Γ} {e':Env (D :: Γ)} {n},
    HasType P Γ D (.sort s) → Expected P Γ A → Ext e e' n →
    R (A.rename Nat.succ) e' = R A e
  product_intro:∀ {Γ D E s} (e:Env Γ),HasType P Γ (.pi D E) (.sort s) →
    Profile P Γ (.pi D E) ∈ C → Ω.profile ((Expr.pi D E).subst (images e)) ∈ C →
    ∀ h,h ∈ Cands.Top Ω ((Expr.pi D E).subst (images e)).nfTerm →
    (∀ n,n ∈ R D e → ∀ e':Env (D :: Γ),Ext e e' n → Expr.app h n ∈ R E e') →
    h ∈ R (.pi D E) e
  specialization:∀ {Γ D E s N} (e:Env Γ),HasType P Γ (.pi D E) (.sort s) →
    HasType P Γ N D → Profile P Γ (.pi D E) ∈ C →
    Ω.profile ((Expr.pi D E).subst (images e)) ∈ C →
    ∀ h,h ∈ R (.pi D E) e → N.subst (images e) ∈ R D e →
    Expr.app h (N.subst (images e)) ∈ R (E.instantiate N) e
namespace ComponentInterface
open Cands
variable {S:Type u} {P:Specification S} {Ω:CTower P}
variable {hw:SystemWeaklyNormalizing P} {U C:Set (Set S)}
variable (J:ComponentInterface.{u,v} Ω hw C)
def Admissible {Γ:List (Expr S)} (e:J.Env Γ):Prop :=
  ∀ i B,Lookup Γ i B →
    (Profile P Γ B ∈ C → J.images e i ∈ J.R B e) ∧
    (Profile P Γ B ∈ U → StronglyNormalizing (J.images e i)) ∧
    (Profile P Γ B ∉ U → Profile P Γ B ∉ C →
      J.images e i ∈ Ground Ω (B.subst (J.images e)).nfTerm)
theorem admissible_extension {Γ:List (Expr S)} {D:Expr S} {s:S}
    {e:J.Env Γ} {e':J.Env (D :: Γ)} {n:Expr S}
    (hD:HasType P Γ D (.sort s)) (he:J.Ext e e' n)
    (ha:J.Admissible (U:=U) e)
    (hnC:Profile P Γ D ∈ C → n ∈ J.R D e)
    (hnU:Profile P Γ D ∈ U → StronglyNormalizing n)
    (hnG:Profile P Γ D ∉ U → Profile P Γ D ∉ C → n ∈ Ground Ω (D.subst (J.images e)).nfTerm) :
    J.Admissible (U:=U) e':=by
  intro i B hi
  cases hi with
  | zero =>
    have hp:=Profile.weaken hw hD hD
    rw [hp,J.weakening hD (.sorted hD) he]
    simpa only [J.ext_images he,Expr.extend_zero,Expr.subst_raise_extend] using ⟨hnC,hnU,hnG⟩
  | succ D hi =>
    obtain ⟨t,hB⟩:=HasType.lookup_sorted hD.valid hi
    rw [Profile.weaken hw hB hD,J.weakening hD (.sorted hB) he]
    simpa only [J.ext_images he,Expr.extend_succ,Expr.subst_raise_extend] using ha _ _ hi
theorem fresh_extension {Γ:List (Expr S)} {D:Expr S} {s:S}
    (e:J.Env Γ) (hD:HasType P Γ D (.sort s)) (ha:J.Admissible (U:=U) e) :
    ∃ n,∃ e':J.Env (D :: Γ),J.Ext e e' (.var n) ∧ J.Admissible (U:=U) e':=by
  have ht:=CTower.HasType.subst hD (J.typed e)
  obtain ⟨n,_,hn⟩:=Ω.fresh_variable ht 0
  obtain ⟨e',he⟩:=J.extend e hD (.var n) hn
  have hng:=var_ground n (hn.normalize_type hw)
  exact ⟨n,e',he,J.admissible_extension hD he ha
    (fun _ => (J.candidate e (.sorted hD)).lower hng)
    (fun _ => (Normal.var n).stronglyNormalizing) (fun _ _ => hng)⟩
end ComponentInterface
namespace Expected
variable {S:Type u} {P:Specification S} {Ω:CTower P}
variable {Γ:List (Expr S)} {A:Expr S} {σ:Nat → Expr S}
theorem subst_wn (h:Expected P Γ A) (hw:SystemWeaklyNormalizing P)
    (hσ:Ω.TySub Γ σ):WeaklyNormalizing (A.subst σ):=by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact ⟨_,.refl,Normal.sort s⟩
  · exact (CTower.HasType.subst h hσ).weakNorm hw
theorem actual (h:Expected P Γ A) (hw:SystemWeaklyNormalizing P)
    (hσ:Ω.TySub Γ σ):Cands.ActualType Ω (A.subst σ).nfTerm:=by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact .inr ⟨s,Expr.nfTerm_of_normal (Normal.sort s)⟩
  · have ht:=CTower.HasType.subst h hσ
    exact .inl ⟨(Expr.nfTerm_spec (ht.weakNorm hw)).2,s,ht.nfTerm hw⟩
end Expected
namespace CTower
variable {S:Type u} {P:Specification S} (Ω:CTower P)
variable (hw:SystemWeaklyNormalizing P)
include hw
theorem profile_subst_path {Γ:List (Expr S)} {T:Expr S} {s:S} {σ:Nat → Expr S}
    (ht:S_wpc_barendregt_geuvers_klop.HasType P Γ T (.sort s)) (hσ:Ω.TySub Γ σ) :
    PositivePath (PriEdge P) (Ω.profile (T.subst σ)) (Profile P Γ T) :=
  Profile.inclusion_path (Ω.profile_feasible hw (HasType.subst ht hσ))
    (Profile.feasible (ht.weakNorm hw) (Profile.nonempty_of_sorted hw ht))
    (Ω.profile_subst_growth hw ht hσ)
theorem profile_instantiate_product_path {D E n:Expr S} {s:S}
    (hp:Ω.HasType (.pi D E) (.sort s)) (hn:Ω.HasType n D) :
    PositivePath (PriEdge P) (Ω.profile (E.instantiate n)) (Ω.profile (.pi D E)):=by
  obtain ⟨k,hp,hn⟩:=hp.common hn
  obtain ⟨a,b,c,_,hE,_,_⟩:=hp.generation_pi
  have hEn:=hE.instantiate hn
  change S_wpc_barendregt_geuvers_klop.HasType P (Ω.context k)
    ((E.rename (Expr.liftRen (Expr.revIx k))).instantiate (n.rename (Expr.revIx k))) (.sort b) at hEn
  rw [Expr.instantiate_rename] at hEn
  rw [Ω.profile_at hw hEn,Ω.profile_at hw hp]
  simpa only [Expr.rename,Expr.instantiate_rename] using Profile.instantiate_product_path hw hp hn
end CTower
namespace Cands
variable {S:Type u} {P:Specification S} {Ω:CTower P}
variable (hw:SystemWeaklyNormalizing P)
include hw
theorem ground_application_subst {Γ:List (Expr S)} {D E n h:Expr S} {s:S}
    {σ:Nat → Expr S} (hp:HasType P Γ (.pi D E) (.sort s))
    (hσ:Ω.TySub Γ σ)
    (hh:h ∈ Ground Ω ((Expr.pi D E).subst σ).nfTerm)
    (hn:n ∈ Top Ω (D.subst σ).nfTerm) :
    Expr.app h n ∈ Ground Ω (E.subst (Expr.extend σ n)).nfTerm:=by
  obtain ⟨a,b,c,hD,hE,_,_⟩:=hp.generation_pi
  have hraw:=CTower.HasType.subst hp hσ
  have hwraw:=hraw.weakNorm hw
  change WeaklyNormalizing (.pi (D.subst σ) (E.subst (Expr.liftSub σ))) at hwraw
  have hrawD:=CTower.HasType.subst hD hσ
  have hnr:Ω.HasType n (D.subst σ):=hn.1.conversion hrawD
    (.symm _ _ (Expr.nfTerm_spec (hrawD.weakNorm hw)).1.converts)
  have hparts:WeaklyNormalizing (D.subst σ) ∧
      WeaklyNormalizing (E.subst (Expr.liftSub σ)):=by
    obtain ⟨normal,reduction,hnormal⟩:=hwraw
    obtain ⟨domain,body,rfl,hdomain,hbody⟩:=Reduces.pi_inv reduction
    exact ⟨⟨domain,hdomain,hnormal.pi_domain⟩,⟨body,hbody,hnormal.pi_body⟩⟩
  have htarget:Ω.HasType (E.subst (Expr.extend σ n)) (.sort b) :=
    CTower.HasType.subst hE (hσ.cons hnr)
  have hnf:((Expr.pi D E).subst σ).nfTerm =
      .pi (D.subst σ).nfTerm (E.subst (Expr.liftSub σ)).nfTerm :=
    Expr.nfTerm_pi hparts.1 hparts.2
  rw [hnf] at hh
  have hout:=ground_application hw hh hn
  have hpN:=hraw.nfTerm hw
  rw [hnf] at hpN
  obtain ⟨t,ht⟩:=Ω.frame_target_sorted hpN hn.1
  have hr:Reduces (E.subst (Expr.extend σ n))
      ((E.subst (Expr.liftSub σ)).nfTerm.instantiate n):=by
    rw [← Expr.instantiate_extended]
    exact (Expr.nfTerm_spec hparts.2).1.subst (Expr.single n)
  have he:=Expr.nfTerm_converts (htarget.weakNorm hw)
    (ht.weakNorm hw) hr.converts
  rwa [he]
end Cands
namespace Processed
variable {S:Type u} {P:Specification S} {Ω:CTower P}
variable {U C:Set (Set S)} (H:Processed Ω U C) (hw:SystemWeaklyNormalizing P)
variable {Γ:List (Expr S)} {T:Expr S} {s:S} {σ:Nat → Expr S}
include H hw
theorem subst_closed (ht:HasType P Γ T (.sort s)) (hσ:Ω.TySub Γ σ)
    (hT:Profile P Γ T ∈ U):Ω.profile (T.subst σ) ∈ U :=
  H.closed hT (Ω.profile_subst_path hw ht hσ).reach
theorem subst_before (ht:HasType P Γ T (.sort s)) (hσ:Ω.TySub Γ σ)
    (hT:Profile P Γ T ∈ C):Ω.profile (T.subst σ) ∈ U ∨ Ω.profile (T.subst σ) ∈ C :=
  H.before hT (Ω.profile_subst_path hw ht hσ).reach
theorem top_ground_generic {e:Expr S}
    (ht:HasType P Γ T (.sort s)) (hσ:Ω.TySub Γ σ)
    (hT:Profile P Γ T ∈ U) (he:e ∈ Cands.Top Ω (T.subst σ).nfTerm) :
    e ∈ Cands.Ground Ω (T.subst σ).nfTerm:=by
  rw [H.invariant ((Expected.sorted ht).actual hw hσ) (by
    rw [Ω.profile_nfTerm]
    exact H.subst_closed hw ht hσ hT)]
  exact he
end Processed
namespace ComponentInterface
open Cands
variable {S:Type u} {P:Specification S} {Ω:CTower P}
variable {hw:SystemWeaklyNormalizing P} {U C:Set (Set S)}
variable (J:ComponentInterface.{u,v} Ω hw C)
def Transported {Γ:List (Expr S)} (M A:Expr S) (e:J.Env Γ):Prop :=
  M.subst (J.images e) ∈ J.R A e ∧
    (Neutral M → Profile P Γ A ∉ C →
      M.subst (J.images e) ∈ Ground Ω (A.subst (J.images e)).nfTerm)
namespace Transported
variable {J} {Γ:List (Expr S)} {M A B:Expr S} {e:J.Env Γ}
theorem sn (h:J.Transported M A e) (hA:Expected P Γ A) :
    StronglyNormalizing (M.subst (J.images e)):=(J.candidate e hA).upper h.1 |>.2
theorem convert (h:J.Transported M A e) (hA:Expected P Γ A)
    (hB:Expected P Γ B) (hc:Converts A B):J.Transported M B e:=by
  have hp:=Profile.converts (P:=P) (Γ:=Γ) (hA.wn hw) (hB.wn hw) hc
  have he:=Expr.nfTerm_converts (hA.subst_wn hw (J.typed e))
    (hB.subst_wn hw (J.typed e)) (hc.subst (J.images e))
  refine ⟨?_,?_⟩
  · rw [← J.conversion e hA hB hc]; exact h.1
  · intro hn hout
    rw [← he]
    exact h.2 hn (hp ▸ hout)
end Transported
theorem transported_of_ground {Γ:List (Expr S)} {M A:Expr S} {e:J.Env Γ}
    (hA:Expected P Γ A) (hg:M.subst (J.images e) ∈ Ground Ω (A.subst (J.images e)).nfTerm) :
    J.Transported M A e:=⟨(J.candidate e hA).lower hg,fun _ _ => hg⟩
theorem transported_at_sort {Γ:List (Expr S)} {M:Expr S} {e:J.Env Γ} {s:S}
    (ht:HasType P Γ M (.sort s)) (hs:StronglyNormalizing (M.subst (J.images e))) :
    J.Transported M (.sort s) e:=by
  apply J.transported_of_ground (.inl ⟨s,rfl⟩)
  have hh:M.subst (J.images e) ∈ Top Ω (.sort s) :=
    ⟨CTower.HasType.subst ht (J.typed e),hs⟩
  simpa only [Expr.subst,Expr.nfTerm_of_normal (Normal.sort s),sort_ground_eq_top] using hh
variable (H:Processed Ω U C)
include H
theorem transported_var {Γ:List (Expr S)} {A:Expr S} {i:Nat}
    (ht:HasType P Γ (.var i) A) (e:J.Env Γ) (ha:J.Admissible (U:=U) e) :
    J.Transported (.var i) A e:=by
  obtain ⟨B,hB,hc⟩:=ht.generation
  obtain ⟨s,hBs⟩:=HasType.lookup_sorted ht.valid hB
  have hea:=Expected.of_type ht
  apply Transported.convert (A:=B) (hA:=.sorted hBs) (hB:=hea) (hc:=.symm _ _ hc)
  have hdr:=ha i B hB
  by_cases hBU:Profile P Γ B ∈ U
  · apply J.transported_of_ground (.sorted hBs)
    exact H.top_ground_generic hw hBs (J.typed e) hBU
      ⟨(J.typed e i B hB).normalize_type hw,hdr.2.1 hBU⟩
  · by_cases hBC:Profile P Γ B ∈ C
    · exact ⟨hdr.1 hBC,fun _ hn => False.elim (hn hBC)⟩
    · exact J.transported_of_ground (.sorted hBs) (hdr.2.2 hBU hBC)
theorem transported_neutral_app {Γ:List (Expr S)} {f n D E:Expr S} {s:S}
    (hp:HasType P Γ (.pi D E) (.sort s)) (hn:HasType P Γ n D)
    (hf:Neutral f) (e:J.Env Γ)
    (hfr:J.Transported f (.pi D E) e) (hnr:J.Transported n D e) :
    J.Transported (.app f n) (E.instantiate n) e:=by
  obtain ⟨a,b,c,hD,hE,_,_⟩:=hp.generation_pi
  have hExpected:=Expected.sorted (hE.instantiate hn)
  have hnt:=(J.candidate e (.sorted hD)).upper hnr.1
  have hg (hfg:f.subst (J.images e) ∈ Ground Ω ((Expr.pi D E).subst (J.images e)).nfTerm) :
      J.Transported (.app f n) (E.instantiate n) e:=by
    apply J.transported_of_ground hExpected
    rw [← Expr.instantiate_subst,Expr.instantiate_extended]
    exact ground_application_subst hw hp (J.typed e) hfg hnt
  by_cases hK:Profile P Γ (.pi D E) ∈ C
  · by_cases hKa:Ω.profile ((Expr.pi D E).subst (J.images e)) ∈ C
    · have hr:=J.specialization e hp hn hK hKa _ hfr.1 hnr.1
      refine ⟨hr,?_⟩
      intro _ ho
      have hL:=H.before hK (Profile.instantiate_product_path hw hp hn).reach
      rcases hL with hLU | hLC
      · exact H.top_ground_generic hw (hE.instantiate hn) (J.typed e) hLU
          ((J.candidate e hExpected).upper hr)
      · exact False.elim (ho hLC)
    · apply hg
      have haK:=(H.subst_before hw hp (J.typed e) hK).resolve_right hKa
      rw [H.invariant ((Expected.sorted hp).actual hw (J.typed e)) (by
        rwa [Ω.profile_nfTerm])]
      exact (J.candidate e (.sorted hp)).upper hfr.1
  · exact hg (hfr.2 hf hK)
end ComponentInterface
end S_wpc_barendregt_geuvers_klop
namespace S_wpc_barendregt_geuvers_klop.Cands
universe u
variable {S:Type u} {P:Specification S} {Ω:CTower P}
variable (hw:SystemWeaklyNormalizing P)
include hw
theorem application_subst_type {Γ:List (Expr S)} {D E n h:Expr S} {s:S}
    {σ:Nat → Expr S} (hp:HasType P Γ (.pi D E) (.sort s))
    (hσ:Ω.TySub Γ σ)
    (hh:Ω.HasType h ((Expr.pi D E).subst σ).nfTerm)
    (hn:Ω.HasType n (D.subst σ).nfTerm) :
    Ω.HasType (.app h n) (E.subst (Expr.extend σ n)).nfTerm:=by
  obtain ⟨a,b,c,hD,hE,_,_⟩:=hp.generation_pi
  have hraw:=CTower.HasType.subst hp hσ
  have hrawD:=CTower.HasType.subst hD hσ
  have hhr:=hh.conversion hraw
    (.symm _ _ (Expr.nfTerm_spec (hraw.weakNorm hw)).1.converts)
  have hnr:=hn.conversion hrawD
    (.symm _ _ (Expr.nfTerm_spec (hrawD.weakNorm hw)).1.converts)
  have hout:=(hhr.application hnr).normalize_type hw
  simpa only [Expr.instantiate_extended] using hout
def RawProduct (Ω:CTower P) (D E:Expr S) (σ:Nat → Expr S)
    (X:Set (Expr S)) (Y:Expr S → Bool → Set (Expr S)):Set (Expr S) :=
  {h | h ∈ Top Ω ((Expr.pi D E).subst σ).nfTerm ∧
    ∀ n ∈ X,∀ b,Expr.app h n ∈ Y n b}
theorem rawProduct_candidate {Γ:List (Expr S)} {D E:Expr S} {s:S}
    {σ:Nat → Expr S} {X:Set (Expr S)} {Y:Expr S → Bool → Set (Expr S)}
    (hp:HasType P Γ (.pi D E) (.sort s)) (hσ:Ω.TySub Γ σ)
    (hX:IsCandidate Ω (D.subst σ).nfTerm X)
    (hY:∀ n ∈ X,∀ b,IsCandidate Ω (E.subst (Expr.extend σ n)).nfTerm (Y n b)) :
    IsCandidate Ω ((Expr.pi D E).subst σ).nfTerm (RawProduct Ω D E σ X Y) where
  lower:=by
    intro h hh
    refine ⟨ground_le_top hh,?_⟩
    intro n hn b
    exact (hY n hn b).lower (ground_application_subst hw hp hσ hh (hX.upper hn))
  upper:=fun _ hh => hh.1
  expansion:=by
    intro D' m a ns ht hD hm ha hns hc
    refine ⟨⟨ht,StronglyNormalizing.head_expansion hD hm ha hns hc.1.2⟩,?_⟩
    intro n hn b
    have ht':=application_subst_type hw hp hσ ht (hX.upper hn).1
    have hsn:StronglyNormalizingArgs (ns ++ [n]):=by
      apply StronglyNormalizingArgs.of_forall
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hns.of_mem hx
      · exact (List.mem_singleton.mp hx).symm ▸ (hX.upper hn).2
    have hc':=hc.2 n hn b
    have ht'':Ω.HasType ((Expr.app (.lam D' m) a).apps (ns ++ [n]))
        (E.subst (Expr.extend σ n)).nfTerm:=by
      simpa only [Expr.apps_append,Expr.apps] using ht'
    have hc'':(m.instantiate a).apps (ns ++ [n]) ∈ Y n b:=by
      simpa only [Expr.apps_append,Expr.apps] using hc'
    simpa only [Expr.apps_append,Expr.apps] using
      (hY n hn b).expansion D' m a (ns ++ [n]) ht'' hD hm ha hsn hc'' 
end S_wpc_barendregt_geuvers_klop.Cands
end OMA
namespace OMA
namespace S_wpc_barendregt_geuvers_klop
section
universe u v
namespace Neutral
variable {S:Type u} {M:Expr S} {ns:List (Expr S)}
theorem apps_head (h:Neutral (M.apps ns)):Neutral M:=by
  induction ns generalizing M with
  | nil => exact h
  | cons n ns ih =>
    have hh:=ih h
    cases hh with
    | app hh => exact hh
end Neutral
namespace ComponentInterface
open Cands
variable {S:Type u} {P:Specification S} {Ω:CTower P}
variable {hw:SystemWeaklyNormalizing P} {U C:Set (Set S)}
variable (J:ComponentInterface.{u,v} Ω hw C)
def Transports (M:Expr S):Prop :=
  ∀ (Γ:List (Expr S)) A,HasType P Γ M A →
    ∀ e:J.Env Γ,J.Admissible (U:=U) e → J.Transported M A e
theorem open_sn {Γ:List (Expr S)} {D b B:Expr S} {s:S}
    (hb:HasType P (D :: Γ) b B) (hD:HasType P Γ D (.sort s))
    (ih:J.Transports (U:=U) b) (e:J.Env Γ) (ha:J.Admissible (U:=U) e) :
    StronglyNormalizing (b.subst (Expr.liftSub (J.images e))):=by
  obtain ⟨z,e',he',ha'⟩:=J.fresh_extension e hD ha
  have hsn:=(ih _ _ hb e' ha').sn (.of_type hb)
  rw [J.ext_images he',← Expr.instantiate_extended] at hsn
  exact StronglyNormalizing.of_subst (Expr.single (.var z)) hsn
variable (H:Processed Ω U C)
include H
theorem transports_lam {Γ:List (Expr S)} {D b B:Expr S} {s:S}
    (hb:HasType P (D :: Γ) b B) (hp:HasType P Γ (.pi D B) (.sort s))
    (ihD:J.Transports (U:=U) D) (ihb:J.Transports (U:=U) b)
    (e:J.Env Γ) (ha:J.Admissible (U:=U) e) :
    J.Transported (.lam D b) (.pi D B) e:=by
  classical
  obtain ⟨a,c,d,hD,hB,_,_⟩:=hp.generation_pi
  have hDs:=(ihD _ _ hD e ha).sn (.of_type hD)
  have hbs:=J.open_sn hb hD ihb e ha
  have htop:(Expr.lam D b).subst (J.images e) ∈ Top Ω ((Expr.pi D B).subst (J.images e)).nfTerm :=
    ⟨(CTower.HasType.subst (.abstraction hb hp) (J.typed e)).normalize_type hw,hDs.lam hbs⟩
  refine ⟨?_,fun hn => by cases hn⟩
  by_cases hK:Profile P Γ (.pi D B) ∈ C
  · by_cases hKa:Ω.profile ((Expr.pi D B).subst (J.images e)) ∈ C
    · apply J.product_intro e hp hK hKa _ htop
      intro n hn e' he
      have hnt:=(J.candidate e (.sorted hD)).upper hn
      have hDomain:=CTower.HasType.subst hD (J.typed e)
      have hnr:=hnt.1.conversion hDomain
        (.symm _ _ (Expr.nfTerm_spec (hDomain.weakNorm hw)).1.converts)
      have hdBefore:=H.before hK (Reach.single (.domain (Profile.triple hw hp)))
      have hadm:J.Admissible (U:=U) e':=J.admissible_extension hD he ha
        (fun _ => hn) (fun _ => hnt.2) (fun hnu hnc => by
          rcases hdBefore with hu | hc
          · exact False.elim (hnu hu)
          · exact False.elim (hnc hc))
      have hbody:=(ihb _ _ hb e' hadm).1
      have htapp:=((CTower.HasType.subst (.abstraction hb hp) (J.typed e)).application hnr).normalize_type hw
      change Ω.HasType (.app (.lam (D.subst (J.images e)) (b.subst (Expr.liftSub (J.images e)))) n)
        ((B.subst (Expr.liftSub (J.images e))).instantiate n).nfTerm at htapp
      rw [Expr.instantiate_extended,← J.ext_images he] at htapp
      have hbmem:(b.subst (Expr.liftSub (J.images e))).instantiate n ∈ J.R B e':=by
        rwa [Expr.instantiate_extended,← J.ext_images he]
      exact (J.candidate e' (.of_type hb)).expansion _ _ _ [] htapp hDs hbs hnt.2 .nil hbmem
    · rw [J.outside e (.sorted hp) (.inr hKa)]; exact htop
  · rw [J.outside e (.sorted hp) (.inl hK)]; exact htop
theorem sn_fundamental {M:Expr S} (hs:StronglyNormalizing M) :
    J.Transports (U:=U) M:=by
  apply StronglyNormalizing.induction_descendants (Q:=J.Transports (U:=U)) _ hs
  intro M _ ihr ihp Γ A ht e ha
  cases M with
  | var i => exact J.transported_var H ht e ha
  | sort s =>
    obtain ⟨t,hat,hc⟩:=ht.generation
    have hst:=HasType.sort_of_valid ht.valid hat
    exact (J.transported_at_sort hst (Normal.sort s).stronglyNormalizing).convert
      (.inl ⟨t,rfl⟩) (.of_type ht) (.symm _ _ hc)
  | pi D E =>
    obtain ⟨a,b,c,hD,hE,hr,hc⟩:=ht.generation_pi
    have hDs:=(ihp D (Expr.ProperPart.child (.pi_domain D E)) _ _ hD e ha).sn (.of_type hD)
    have hEs:=J.open_sn hE hD (ihp E (Expr.ProperPart.child (.pi_body D E))) e ha
    exact (J.transported_at_sort (.product hD hE hr) (hDs.pi hEs)).convert
      (.inl ⟨c,rfl⟩) (.of_type ht) (.symm _ _ hc)
  | lam D b =>
    obtain ⟨B,s,hb,hp,hc⟩:=ht.generation_lam
    exact (J.transports_lam H hb hp
      (ihp D (Expr.ProperPart.child (.lam_domain D b)))
      (ihp b (Expr.ProperPart.child (.lam_body D b))) e ha).convert
      (.sorted hp) (.of_type ht) (.symm _ _ hc)
  | app f n =>
    rcases ht.app_spine with hf | ⟨D,b,n',ns,he⟩
    · obtain ⟨D,E,hft,hnt,hc⟩:=ht.generation_app
      obtain ⟨s,hp⟩:=hft.product_type_sorted
      have hfr:=ihp f (Expr.ProperPart.child (.app_left f n)) _ _ hft e ha
      have hnr:=ihp n (Expr.ProperPart.child (.app_right f n)) _ _ hnt e ha
      exact (J.transported_neutral_app H hp hnt hf e hfr hnr).convert
        (.of_type (.application hft hnt)) (.of_type ht) (.symm _ _ hc)
    · have ht':HasType P Γ ((Expr.app (.lam D b) n').apps ns) A:=he ▸ ht
      have parts:∀ N,Expr.ProperPart N ((Expr.app (.lam D b) n').apps ns) →
          J.Transports (U:=U) N:=by
        intro N hN; apply ihp N; change Expr.ProperPart N (.app f n); rwa [he]
      have hlampart:Expr.ProperPart (.lam D b) ((Expr.app (.lam D b) n').apps ns) :=
        (Expr.ProperPart.child (.app_left _ _)).trans_right (Expr.Subterm.apps_head ns)
      obtain ⟨T,hthead⟩:=ht'.apps_head
      obtain ⟨D',E',hlam,hn',_⟩:=hthead.generation_app
      obtain ⟨B,s,hb,hp,_⟩:=hlam.generation_lam
      obtain ⟨a,c,d,hD,_,_,_⟩:=hp.generation_pi
      have hDs:=(parts D (Expr.ProperPart.trans_left (Expr.Subterm.of_child (.lam_domain D b)) hlampart) _ _ hD e ha).sn (.of_type hD)
      have hbs:=J.open_sn hb hD (parts b (Expr.ProperPart.trans_left (Expr.Subterm.of_child (.lam_body D b)) hlampart)) e ha
      have hnp:=(Expr.ProperPart.child (.app_right (.lam D b) n')).trans_right (Expr.Subterm.apps_head ns)
      have hns:=(parts n' hnp _ _ hn' e ha).sn (.of_type hn')
      have hargs:StronglyNormalizingArgs (ns.map (Expr.subst (J.images e))):=by
        apply StronglyNormalizingArgs.of_forall
        intro z hz
        rcases List.mem_map.mp hz with ⟨L,hL,rfl⟩
        obtain ⟨Z,hZ⟩:=ht'.apps_arg hL
        exact (parts L (Expr.ProperPart.apps_arg hL) _ _ hZ e ha).sn (.of_type hZ)
      have hred:Beta (.app f n) ((b.instantiate n').apps ns):=by
        rw [he]; exact (Beta.head D b n').apps ns
      have hctr:=(ihr _ hred _ _ (ht.subject_reduction hred) e ha).1
      have hctr':((b.subst (Expr.liftSub (J.images e))).instantiate (n'.subst (J.images e))).apps
          (ns.map (Expr.subst (J.images e))) ∈ J.R A e:=by
        simpa only [Expr.subst_apps,Expr.instantiate_subst] using hctr
      have hty:=(CTower.HasType.subst ht' (J.typed e)).normalize_type hw
      rw [Expr.subst_apps] at hty
      have hexp:=(J.candidate e (.of_type ht)).expansion _ _ _ _ hty hDs hbs hns hargs hctr'
      constructor
      · rw [he,Expr.subst_apps]
        exact hexp
      · intro hn
        rw [he] at hn
        have hh:=hn.apps_head
        cases hh with
        | app hn => cases hn
end ComponentInterface
namespace StronglyNormalizing
variable {S:Type u} {M:Expr S}
theorem revIx (h:StronglyNormalizing M) (k:Nat) :
    StronglyNormalizing (M.rename (Expr.revIx k)):=by
  apply of_rename (Expr.revIx k)
  simpa only [Expr.revIx_twice] using h
end StronglyNormalizing
namespace Cands
variable {S:Type u} {P:Specification S} (Ω:CTower P)
inductive StackAt (k:Nat):Expr S → List (Expr S) → Prop
  | nil (T):StackAt k T []
  | cons {D E n ns} :
      HasType P (Ω.context k) (n.rename (Expr.revIx k)) (D.rename (Expr.revIx k)) →
      StronglyNormalizing n → StackAt k (E.instantiate n).nfTerm ns →
      StackAt k (.pi D E) (n :: ns)
namespace StackAt
variable {Ω} {k j:Nat} {T:Expr S} {ns:List (Expr S)}
theorem mono (h:StackAt Ω k T ns) (hkj:k ≤ j):StackAt Ω j T ns:=by
  induction h with
  | nil T => exact .nil T
  | cons hn hsn _ ih => exact .cons (Ω.at_mono hn hkj) hsn ih
theorem tested (h:StackAt Ω k T ns):TestedStack Ω T ns:=by
  induction h with
  | nil T => exact .nil T
  | cons hn hs _ ih => exact .cons ⟨⟨k,hn⟩,hs⟩ ih
end StackAt
namespace TestedStack
variable {Ω} {T:Expr S} {ns:List (Expr S)}
theorem common_stage (h:TestedStack Ω T ns):∃ k,StackAt Ω k T ns:=by
  induction h with
  | nil T => exact ⟨0,.nil T⟩
  | cons hn _ ih =>
    obtain ⟨k,hk⟩:=ih
    obtain ⟨j,hj⟩:=hn.1
    exact ⟨max j k,.cons (Ω.at_mono hj (le_max_left j k)) hn.2 (hk.mono (le_max_right j k))⟩
end TestedStack
end Cands
namespace ComponentInterface
section
open Cands
variable {S:Type u} {P:Specification S} {Ω:CTower P}
variable {hw:SystemWeaklyNormalizing P} {U C:Set (Set S)}
variable (J:ComponentInterface.{u,v} Ω hw C)
theorem identity_admissible {k:Nat} {e:J.Env (Ω.context k)}
    (he:J.images e = Expr.var ∘ Expr.revIx k):J.Admissible (U:=U) e:=by
  intro i B hi
  obtain ⟨s,hB⟩:=HasType.lookup_sorted (Ω.valid k) hi
  have ht:=(J.typed e i B hi).normalize_type hw
  have hG:J.images e i ∈ Ground Ω (B.subst (J.images e)).nfTerm:=by
    rw [he] at ht ⊢
    exact var_ground _ ht
  exact ⟨fun _ => (J.candidate e (.sorted hB)).lower hG,
    fun _ => (ground_le_top hG).2,fun _ _ => hG⟩
@[simp] theorem identity_actual {k:Nat} {e:J.Env (Ω.context k)}
    (he:J.images e = Expr.var ∘ Expr.revIx k) (T:Expr S) :
    (T.rename (Expr.revIx k)).subst (J.images e) = T:=by
  rw [he,Expr.subst_var_rename,Expr.revIx_twice]
end
open Cands
variable {S:Type u} {P:Specification S} {Ω:CTower P}
variable {hw:SystemWeaklyNormalizing P} {U C:Set (Set S)}
variable (J:ComponentInterface.{u,v} Ω hw C) (H:Processed Ω U C)
include J H
theorem run_stack {k:Nat} {e:J.Env (Ω.context k)}
    (he:J.images e = Expr.var ∘ Expr.revIx k)
    {T:Expr S} {ns:List (Expr S)} (hstack:StackAt Ω k T ns) :
    ∀ {s},HasType P (Ω.context k) (T.rename (Expr.revIx k)) (.sort s) →
    Normal T → Ω.profile T ∈ U ∨ Ω.profile T ∈ C →
    ∀ h,h ∈ J.R (T.rename (Expr.revIx k)) e → StronglyNormalizing (h.apps ns):=by
  induction hstack with
  | nil T =>
      intro s ht hN _ h hr
      exact (J.candidate e (.sorted ht)).upper hr |>.2
  | @cons D E n ns hn hsn hstack ih =>
      intro s ht hN hprofile h hr
      have hactual:ActualType Ω (.pi D E):=.inl ⟨hN,s,⟨k,ht⟩⟩
      rcases hprofile with hU | hC
      · have htop:=(J.candidate e (.sorted ht)).upper hr
        rw [J.identity_actual he,Expr.nfTerm_of_normal hN] at htop
        have hg:h ∈ Ground Ω (.pi D E):=by
          rw [H.invariant hactual hU]; exact htop
        exact hg.2 (n :: ns) (.cons ⟨⟨k,hn⟩,hsn⟩ hstack.tested)
      · obtain ⟨a,b,c,hD,hE,_,_⟩:=ht.generation_pi
        have hnR:=(J.sn_fundamental H (hsn.revIx k) _ _ hn e
          (J.identity_admissible he)).1
        have hr':=J.specialization e ht hn (by
          change Profile P (Ω.context k) ((Expr.pi D E).rename (Expr.revIx k)) ∈ C
          rwa [← Ω.profile_at hw ht])
          (by
            change Ω.profile (((Expr.pi D E).rename (Expr.revIx k)).subst (J.images e)) ∈ C
            rwa [J.identity_actual he]) h hr hnR
        change Expr.app h ((n.rename (Expr.revIx k)).subst (J.images e)) ∈
          J.R ((E.rename (Expr.liftRen (Expr.revIx k))).instantiate
            (n.rename (Expr.revIx k))) e at hr'
        rw [J.identity_actual he,Expr.instantiate_rename] at hr'
        have htarget:HasType P (Ω.context k) ((E.instantiate n).rename (Expr.revIx k)) (.sort b):=by
          have hti:=hE.instantiate hn
          change HasType P (Ω.context k) ((E.rename (Expr.liftRen (Expr.revIx k))).instantiate
            (n.rename (Expr.revIx k))) (.sort b) at hti
          rwa [Expr.instantiate_rename] at hti
        have htargetΩ:Ω.HasType (E.instantiate n) (.sort b):=⟨k,htarget⟩
        have hwtarget:=htargetΩ.weakNorm hw
        have htargetN:HasType P (Ω.context k) ((E.instantiate n).nfTerm.rename (Expr.revIx k)) (.sort b):=by
          rw [← Expr.nfTerm_rename hwtarget]
          exact htarget.nfTerm hw
        have hconv:Converts ((E.instantiate n).rename (Expr.revIx k))
            ((E.instantiate n).nfTerm.rename (Expr.revIx k)) :=
          (Expr.nfTerm_spec hwtarget).1.converts.rename _
        rw [J.conversion e (.sorted htarget) (.sorted htargetN) hconv] at hr'
        have hprofile':Ω.profile (E.instantiate n).nfTerm ∈ U ∨
            Ω.profile (E.instantiate n).nfTerm ∈ C:=by
          rw [Ω.profile_nfTerm]
          exact H.before hC (Ω.profile_instantiate_product_path hw ⟨k,ht⟩ ⟨k,hn⟩).reach
        exact ih htargetN (Expr.nfTerm_spec hwtarget).2 hprofile' (.app h n) hr'
theorem advance {T:Expr S} (hT:ActualType Ω T) (hC:Ω.profile T ∈ C) :
    Ground Ω T = Top Ω T:=by
  apply Set.Subset.antisymm ground_le_top
  intro h hh
  rcases hT with ⟨hN,s,ks,ht⟩ | ⟨s,rfl⟩
  · refine ⟨hh.1,?_⟩
    intro ns hstack
    obtain ⟨kn,hs⟩:=hstack.common_stage
    obtain ⟨kh,hhT⟩:=hh.1
    let k:=max ks (max kn kh)
    have hkT:ks ≤ k:=le_max_left _ _
    have hkN:kn ≤ k:=le_trans (le_max_left _ _) (le_max_right _ _)
    have hkH:kh ≤ k:=le_trans (le_max_right _ _) (le_max_right _ _)
    have ht':=Ω.at_mono ht hkT
    have hh':=Ω.at_mono hhT hkH
    obtain ⟨e,he⟩:=J.inhabit (.var ∘ Expr.revIx k) (.identity k)
    have hr:=(J.sn_fundamental H (hh.2.revIx k) _ _ hh' e
      (J.identity_admissible he)).1
    rw [J.identity_actual he] at hr
    exact J.run_stack H he (hs.mono hkN) ht' hN (.inr hC) h hr
  · rwa [sort_ground_eq_top]
end ComponentInterface
end
universe u v
open Classical Cands
namespace Beta
variable {S:Type u}
theorem rename_source {M N:Expr S} {ρ:Nat → Nat} (h:Beta (M.rename ρ) N) :
    ∃ M',Beta M M' ∧ N = M'.rename ρ:=by
  induction M generalizing ρ N with
  | var n => cases h
  | sort s => cases h
  | pi A B ihA ihB =>
    cases h with
    | pi_domain hh =>
      obtain ⟨A',ha,rfl⟩:=ihA hh
      exact ⟨_,.pi_domain ha,rfl⟩
    | pi_body hh =>
      obtain ⟨B',hb,rfl⟩:=ihB hh
      exact ⟨_,.pi_body hb,rfl⟩
  | lam A b ihA ihb =>
    cases h with
    | lam_domain hh =>
      obtain ⟨A',ha,rfl⟩:=ihA hh
      exact ⟨_,.lam_domain ha,rfl⟩
    | lam_body hh =>
      obtain ⟨b',hb,rfl⟩:=ihb hh
      exact ⟨_,.lam_body hb,rfl⟩
  | app f a ihf iha =>
    cases f <;> cases h
    all_goals first
      | (rename_i hh
         obtain ⟨f',hf,rfl⟩:=ihf hh
         exact ⟨_,.app_left hf,rfl⟩)
      | (rename_i hh
         obtain ⟨a',ha,rfl⟩:=iha hh
         exact ⟨_,.app_right ha,rfl⟩)
      | exact ⟨_,.head _ _ _,Expr.instantiate_rename _ _ _⟩
end Beta
namespace StronglyNormalizing
variable {S:Type u} {M:Expr S}
theorem rename (h:StronglyNormalizing M) (ρ:Nat → Nat) :
    StronglyNormalizing (M.rename ρ):=by
  induction h with
  | intro M _ ih =>
    apply Acc.intro
    intro N hn
    obtain ⟨M',hm,rfl⟩:=hn.rename_source
    exact ih M' hm
end StronglyNormalizing
namespace CTower
variable {S:Type u} {P:Specification S} (Ω:CTower P)
theorem variable_substitution {Γ:List (Expr S)} (hΓ:ValidContext P Γ) :
    ∃ ρ:Nat → Nat,Ω.TySub Γ (Expr.var ∘ ρ):=by
  induction hΓ with
  | nil => exact ⟨id,fun _ _ h => nomatch h⟩
  | @cons Γ A s hΓ hA ih =>
    obtain ⟨ρ,hρ⟩:=ih
    have ht:=HasType.subst hA hρ
    obtain ⟨n,_,hn⟩:=Ω.fresh_variable ht 0
    refine ⟨fun i => match i with | 0 => n | i+1 => ρ i,?_⟩
    convert hρ.cons hn using 1
    funext i; cases i <;> rfl
end CTower
theorem all_ground_eq_top {S:Type u} [Fintype S] {P:Specification S}
    (Ω:CTower P) (hw:SystemWeaklyNormalizing P)
    (interfaces:∀ C,IsComp (PriEdge P) C →
      Nonempty (ComponentInterface.{u,v} Ω hw C)) :
    ∀ {T},ActualType Ω T → Ground Ω T = Top Ω T:=by
  intro T hT
  let E:=PriEdge P
  have h:∀ n,∀ T:Expr S,Reach.rank E (Ω.profile T) = n → ActualType Ω T →
      Ground Ω T = Top Ω T:=by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hr hT
      let V:=Ω.profile T
      let C:=Reach.component E V
      let U:={I | Reach.rank E I < n}
      have hC:IsComp E C:=Reach.component_isComponent E V
      have rankC {I} (hi:I ∈ C):Reach.rank E I = n:=by
        exact (Nat.le_antisymm (Reach.rank_mono E hi.2) (Reach.rank_mono E hi.1)).trans hr
      have hp:Processed Ω U C:=by
        refine ⟨?_,?_,?_,?_⟩
        · apply Set.disjoint_left.mpr
          intro I hI hc
          have:Reach.rank E I < n:=hI
          rw [rankC hc] at this
          exact Nat.lt_irrefl _ this
        · intro I J hj hij
          exact lt_of_le_of_lt (Reach.rank_mono E hij) hj
        · intro I J hj hij
          have hle:Reach.rank E I ≤ n:=(Reach.rank_mono E hij).trans (le_of_eq (rankC hj))
          rcases lt_or_eq_of_le hle with hlt | heq
          · exact .inl hlt
          · exact .inr ⟨hj.1.trans (Reach.reverse_of_rank_eq E hij (heq.trans (rankC hj).symm)),
              hij.trans hj.2⟩
        · intro A hA hAu
          exact ih _ hAu A rfl hA
      obtain ⟨J⟩:=interfaces C hC
      exact J.advance hp hT (Reach.mem_component E V)
  exact h _ T rfl hT
theorem application_sn_of_ground {S:Type u} {P:Specification S}
    (Ω:CTower P) (hw:SystemWeaklyNormalizing P)
    (hground:∀ {T},ActualType Ω T → Ground Ω T = Top Ω T)
    {Γ:List (Expr S)} {f a D E:Expr S}
    (hf:HasType P Γ f (.pi D E)) (ha:HasType P Γ a D)
    (hsf:StronglyNormalizing f) (hsa:StronglyNormalizing a) :
    StronglyNormalizing (.app f a):=by
  obtain ⟨ρ,hρ⟩:=Ω.variable_substitution hf.valid
  have hf':=CTower.HasType.subst hf hρ
  have ha':=CTower.HasType.subst ha hρ
  simp only [Expr.subst_var_rename] at hf' ha'
  obtain ⟨s,hpi⟩:=hf.product_type_sorted
  have hpi':=CTower.HasType.subst hpi hρ
  simp only [Expr.subst_var_rename,Expr.rename] at hpi'
  obtain ⟨a',b',c',hD,hE,hr,_⟩:=hpi.generation_pi
  have hDw:=(CTower.HasType.subst hD hρ).weakNorm hw
  simp only [Expr.subst_var_rename] at hDw
  have hPw:=hpi'.weakNorm hw
  have hDN:Normal (D.rename ρ).nfTerm:=(Expr.nfTerm_spec hDw).2
  have hPN:=(Expr.nfTerm_spec hPw).2
  have hpNF:((Expr.pi D E).rename ρ).nfTerm =
      .pi (D.rename ρ).nfTerm (E.rename (Expr.liftRen ρ)).nfTerm:=by
    apply Expr.nfTerm_pi hDw
    obtain ⟨target,reduces,normal⟩:=hPw
    obtain ⟨domain,body,rfl,_,bodyReduces⟩:=Reduces.pi_inv reduces
    exact ⟨body,bodyReduces,normal.pi_body⟩
  have htype:ActualType Ω ((Expr.pi D E).rename ρ).nfTerm :=
    .inl ⟨hPN,s,hpi'.nfTerm hw⟩
  have hfg:f.rename ρ ∈ Ground Ω ((Expr.pi D E).rename ρ).nfTerm:=by
    rw [hground htype]
    exact ⟨hf'.normalize_type hw,hsf.rename ρ⟩
  rw [hpNF] at hfg
  have hag:a.rename ρ ∈ Top Ω (D.rename ρ).nfTerm:=⟨ha'.normalize_type hw,hsa.rename ρ⟩
  have hs:=(ground_le_top (ground_application hw hfg hag)).2
  exact StronglyNormalizing.of_rename ρ hs
end S_wpc_barendregt_geuvers_klop
end OMA
namespace OMA
namespace S_wpc_barendregt_geuvers_klop.SignedInterpretation
section
universe u
open Classical Cands
variable {S:Type u} {P:Specification S} (Ω:CTower P)
variable {C:Set (Set S)} (hC:IsComp (PriEdge P) C)
variable (hw:SystemWeaklyNormalizing P)
variable (hno:∀ I ∈ C,¬ SignedPath (PriEdge P) I I true)
abbrev Vector:=(T:Expr S) → SignedCandidate Ω T (hC.signing (Ω.profile T))
noncomputable def value (v:Vector Ω hC) (T:Expr S):Set (Expr S) :=
  if Ω.profile T ∈ C then (v T).set else Top Ω T
theorem value_candidate (v:Vector Ω hC) (T:Expr S) :
    IsCandidate Ω T (value Ω hC v T):=by
  unfold value; split
  · exact (v T).candidate
  · exact top_candidate
theorem value_forward {v w:Vector Ω hC} (hv:v ≤ w) {T:Expr S}
    (hs:Ω.profile T ∈ C → hC.signing (Ω.profile T) = false) :
    value Ω hC v T ⊆ value Ω hC w T:=by
  unfold value; split
  · have hh:=(SignedCandidate.order (v T) (w T)).mp (hv T)
    simpa only [hs ‹_›,Bool.false_eq_true,ite_false] using hh
  · exact Set.Subset.rfl
theorem value_backward {v w:Vector Ω hC} (hv:v ≤ w) {T:Expr S}
    (hs:Ω.profile T ∈ C → hC.signing (Ω.profile T) = true) :
    value Ω hC w T ⊆ value Ω hC v T:=by
  unfold value; split
  · have hh:=(SignedCandidate.order (v T) (w T)).mp (hv T)
    simpa only [hs ‹_›,ite_true] using hh
  · exact Set.Subset.rfl
noncomputable def stepCandidate (v:Vector Ω hC) (T:Expr S):Candidate Ω T :=
  match T with
  | .pi D E =>
    if Normal (.pi D E) ∧ (∃ s,Ω.HasType (.pi D E) (.sort s)) ∧ Ω.profile (.pi D E) ∈ C then
      ⟨ProductTest Ω D E (value Ω hC v D) (fun n => {value Ω hC v (E.instantiate n).nfTerm}),
        productTest_candidate hw (value_candidate Ω hC v D).upper (by
          intro n _ X hX
          rcases Set.mem_singleton_iff.mp hX with rfl
          exact value_candidate Ω hC v _)⟩
    else ⟨Top Ω (.pi D E),top_candidate⟩
  | T => ⟨Top Ω T,top_candidate⟩
noncomputable def step (v:Vector Ω hC):Vector Ω hC :=
  fun T => SignedCandidate.wrap (stepCandidate Ω hC hw v T)
include hno in
theorem step_monotone:Monotone (step Ω hC hw):=by
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
    by_cases H:Normal (.pi D E) ∧ (∃ s,Ω.HasType (.pi D E) (.sort s)) ∧ Ω.profile (.pi D E) ∈ C
    · simp only [if_pos H]
      obtain ⟨hn,⟨s,ht⟩,hpC⟩:=H
      have hd:∀ hD:Ω.profile D ∈ C,
          hC.signing (Ω.profile (.pi D E)) = Bool.xor (hC.signing (Ω.profile D)) true:=by
        intro hD
        obtain ⟨a,b,c,hD',hE,hr,hconv⟩:=ht.choose_spec.generation_pi
        have hf:=Profile.triple hw ht.choose_spec
        have hglob:ProfileTriple P (Ω.profile D)
            (Profile P (D.rename (Expr.revIx ht.choose) :: Ω.context ht.choose)
              (E.rename (Expr.liftRen (Expr.revIx ht.choose)))) (Ω.profile (.pi D E)):=by
          rw [Ω.profile_at hw hD',Ω.profile_at hw ht.choose_spec]
          exact hf
        exact hC.signing_cross hno hD hpC (.singleton (.domain hglob))
      have he:∀ n,Ω.HasType n D → Ω.profile (E.instantiate n).nfTerm ∈ C →
          hC.signing (Ω.profile (E.instantiate n).nfTerm) = hC.signing (Ω.profile (.pi D E)):=by
        intro n hn hnc
        rw [Ω.profile_nfTerm] at hnc ⊢
        simpa only [Bool.xor_false] using
          (hC.signing_cross hno hnc hpC (Ω.profile_instantiate_product_path hw ht hn).parity).symm
      have flip (a b:Bool) (h:a = Bool.xor b true):b = !a:=by
        cases a <;> cases b <;> cases h <;> rfl
      cases hs:hC.signing (Ω.profile (.pi D E)) with
      | false =>
        simp only [Bool.false_eq_true,ite_false]
        intro h hh
        refine ⟨hh.1,?_⟩
        intro n hn X hX
        rcases Set.mem_singleton_iff.mp hX with rfl
        have hn':n ∈ value Ω hC v D:=value_backward Ω hC hv (by
          intro hc
          simpa only [hs,Bool.not_false,Bool.not_true] using flip _ _ (hd hc)) hn
        have hout:=hh.2 n hn' _ (Set.mem_singleton _)
        exact value_forward Ω hC hv (fun hc => (he n (value_candidate Ω hC w D |>.upper hn).1 hc).trans hs) hout
      | true =>
        simp only [ite_true]
        intro h hh
        refine ⟨hh.1,?_⟩
        intro n hn X hX
        rcases Set.mem_singleton_iff.mp hX with rfl
        have hn':n ∈ value Ω hC w D:=value_forward Ω hC hv (by
          intro hc
          simpa only [hs,Bool.not_false,Bool.not_true] using flip _ _ (hd hc)) hn
        have hout:=hh.2 n hn' _ (Set.mem_singleton _)
        exact value_backward Ω hC hv (fun hc => (he n (value_candidate Ω hC v D |>.upper hn).1 hc).trans hs) hout
    · simp only [if_neg H]
      cases hC.signing (Ω.profile (.pi D E)) <;> exact Set.Subset.rfl
noncomputable def operator:Vector Ω hC →o Vector Ω hC :=
  ⟨step Ω hC hw,step_monotone Ω hC hw hno⟩
noncomputable def fixed:Vector Ω hC:=(operator Ω hC hw hno).lfp
noncomputable def actual (T:Expr S):Set (Expr S):=value Ω hC (fixed Ω hC hw hno) T
theorem actual_candidate (T:Expr S):IsCandidate Ω T (actual Ω hC hw hno T) :=
  value_candidate Ω hC _ T
theorem actual_outside {T:Expr S} (ho:Ω.profile T ∉ C):actual Ω hC hw hno T = Top Ω T:=by
  simp only [actual,value,ho,ite_false]
theorem actual_product {D E:Expr S} {s:S} (hn:Normal (.pi D E))
    (ht:Ω.HasType (.pi D E) (.sort s)) (hc:Ω.profile (.pi D E) ∈ C) :
    actual Ω hC hw hno (.pi D E) =
      ProductTest Ω D E (actual Ω hC hw hno D) (fun n => {actual Ω hC hw hno (E.instantiate n).nfTerm}):=by
  have he:=congrArg (fun v:Vector Ω hC => (v (.pi D E)).set) (operator Ω hC hw hno).map_lfp
  change (step Ω hC hw (fixed Ω hC hw hno) (.pi D E)).set = _ at he
  dsimp only [step,SignedCandidate.set_wrap,stepCandidate] at he
  rw [if_pos (show Normal (.pi D E) ∧ (∃ s,Ω.HasType (.pi D E) (.sort s)) ∧
    Ω.profile (.pi D E) ∈ C from ⟨hn,⟨s,ht⟩,hc⟩)] at he
  simpa only [actual,value,hc,ite_true,SignedCandidate.set_wrap,fixed] using he.symm
end
universe u
open Classical Cands
variable {S:Type u} {P:Specification S} (Ω:CTower P)
variable {C:Set (Set S)} (hC:IsComp (PriEdge P) C)
variable (hw:SystemWeaklyNormalizing P)
variable (hno:∀ I ∈ C,¬ SignedPath (PriEdge P) I I true)
abbrev ValEnv (Γ:List (Expr S)):={σ:Nat → Expr S // Ω.TySub Γ σ}
noncomputable def R {Γ:List (Expr S)} (A:Expr S) (e:ValEnv Ω Γ):Set (Expr S) :=
  if Profile P Γ A ∈ C then actual Ω hC hw hno (A.subst e.val).nfTerm
  else Top Ω (A.subst e.val).nfTerm
theorem R_candidate {Γ:List (Expr S)} (A:Expr S) (e:ValEnv Ω Γ) :
    IsCandidate Ω (A.subst e.val).nfTerm (R Ω hC hw hno A e):=by
  unfold R; split
  · exact actual_candidate Ω hC hw hno _
  · exact top_candidate
theorem R_outside {Γ:List (Expr S)} (A:Expr S) (e:ValEnv Ω Γ)
    (ho:Profile P Γ A ∉ C ∨ Ω.profile (A.subst e.val) ∉ C) :
    R Ω hC hw hno A e = Top Ω (A.subst e.val).nfTerm:=by
  unfold R; split
  · exact actual_outside Ω hC hw hno (by
      rw [Ω.profile_nfTerm]; exact ho.resolve_left (not_not.mpr ‹_›))
  · rfl
theorem R_conversion {Γ:List (Expr S)} {A B:Expr S}
    (e:ValEnv Ω Γ) (hA:Expected P Γ A) (hB:Expected P Γ B) (hc:Converts A B) :
    R Ω hC hw hno A e = R Ω hC hw hno B e:=by
  have hwa:WeaklyNormalizing A:=by
    rcases hA with ⟨s,rfl⟩ | ⟨s,h⟩
    · exact ⟨_,.refl,Normal.sort s⟩
    · exact h.weakNorm hw
  have hwb:WeaklyNormalizing B:=by
    rcases hB with ⟨s,rfl⟩ | ⟨s,h⟩
    · exact ⟨_,.refl,Normal.sort s⟩
    · exact h.weakNorm hw
  have hp:=Profile.converts (P:=P) (Γ:=Γ) hwa hwb hc
  have hn:=Expr.nfTerm_converts (hA.subst_wn hw e.property) (hB.subst_wn hw e.property) (hc.subst e.val)
  simp only [R,hp,hn]
theorem actual_sort (s:S):actual Ω hC hw hno (.sort s) = Top Ω (.sort s):=by
  by_cases hc:Ω.profile (.sort s) ∈ C
  · have he:=congrArg (fun v:Vector Ω hC => (v (.sort s)).set) (operator Ω hC hw hno).map_lfp
    change (step Ω hC hw (fixed Ω hC hw hno) (.sort s)).set = _ at he
    simpa only [step,stepCandidate,SignedCandidate.set_wrap,actual,value,hc,ite_true,fixed] using he.symm
  · exact actual_outside Ω hC hw hno hc
theorem R_sort {Γ:List (Expr S)} (s:S) (e:ValEnv Ω Γ) :
    R Ω hC hw hno (.sort s) e = Top Ω (.sort s):=by
  simp only [R,Expr.subst,Expr.nfTerm_of_normal (Normal.sort s),actual_sort,ite_self]
theorem R_weakening {Γ:List (Expr S)} {D A n:Expr S} {s:S}
    {e:ValEnv Ω Γ} {f:ValEnv Ω (D :: Γ)}
    (hD:HasType P Γ D (.sort s)) (hA:Expected P Γ A)
    (he:f.val = Expr.extend e.val n) :
    R Ω hC hw hno (A.rename Nat.succ) f = R Ω hC hw hno A e:=by
  rcases hA with ⟨a,rfl⟩ | ⟨a,hA⟩
  · exact (R_sort Ω hC hw hno a f).trans (R_sort Ω hC hw hno a e).symm
  · simp only [R,Profile.weaken hw hA hD,he,Expr.subst_raise_extend]
theorem R_before {Γ:List (Expr S)} {A:Expr S} {s:S}
    (hA:HasType P Γ A (.sort s)) (e:ValEnv Ω Γ)
    (hp:∃ K ∈ C,Reach (PriEdge P) (Profile P Γ A) K) :
    R Ω hC hw hno A e = actual Ω hC hw hno (A.subst e.val).nfTerm:=by
  unfold R; split
  · rfl
  · rename_i hn
    refine (actual_outside Ω hC hw hno ?_).symm
    rw [Ω.profile_nfTerm]
    intro ha
    obtain ⟨K,hK,hp⟩:=hp
    exact hn (hC.between ha hK (Ω.profile_subst_path hw hA e.property).reach hp)
theorem actual_raw_product {Γ:List (Expr S)} {D E:Expr S} {s:S}
    (hp:HasType P Γ (.pi D E) (.sort s)) (e:ValEnv Ω Γ)
    (ha:Ω.profile ((Expr.pi D E).subst e.val) ∈ C) (h:Expr S) :
    h ∈ actual Ω hC hw hno ((Expr.pi D E).subst e.val).nfTerm ↔
    h ∈ Top Ω ((Expr.pi D E).subst e.val).nfTerm ∧
      ∀ n,n ∈ actual Ω hC hw hno (D.subst e.val).nfTerm →
        Expr.app h n ∈ actual Ω hC hw hno (E.subst (Expr.extend e.val n)).nfTerm:=by
  obtain ⟨a,b,c,hD,hE,_,_⟩:=hp.generation_pi
  have hraw:=CTower.HasType.subst hp e.property
  have hwraw:=hraw.weakNorm hw
  change WeaklyNormalizing (.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))) at hwraw
  have hparts:WeaklyNormalizing (D.subst e.val) ∧
      WeaklyNormalizing (E.subst (Expr.liftSub e.val)):=by
    obtain ⟨normal,reduction,hnormal⟩:=hwraw
    obtain ⟨domain,body,rfl,hdomain,hbody⟩:=Reduces.pi_inv reduction
    exact ⟨⟨domain,hdomain,hnormal.pi_domain⟩,⟨body,hbody,hnormal.pi_body⟩⟩
  have hnf:=Expr.nfTerm_pi hparts.1 hparts.2
  have hpN:=hraw.nfTerm hw
  change Ω.HasType (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).nfTerm (.sort s) at hpN
  rw [hnf] at hpN
  have hNC:Ω.profile (.pi (D.subst e.val).nfTerm (E.subst (Expr.liftSub e.val)).nfTerm) ∈ C:=by
    rw [← hnf,Ω.profile_nfTerm]; exact ha
  have hnormal:Normal (.pi (D.subst e.val).nfTerm (E.subst (Expr.liftSub e.val)).nfTerm) :=
    .pi (Expr.nfTerm_spec hparts.1).2 (Expr.nfTerm_spec hparts.2).2
  have hbody (n:Expr S) (hn:n ∈ actual Ω hC hw hno (D.subst e.val).nfTerm) :
      (E.subst (Expr.extend e.val n)).nfTerm =
        ((E.subst (Expr.liftSub e.val)).nfTerm.instantiate n).nfTerm:=by
    have hnt:=(actual_candidate Ω hC hw hno _).upper hn |>.1
    have hrawD:=CTower.HasType.subst hD e.property
    have hnr:=hnt.conversion hrawD
      (.symm _ _ (Expr.nfTerm_spec (hrawD.weakNorm hw)).1.converts)
    have htarget:=CTower.HasType.subst hE (e.property.cons hnr)
    obtain ⟨t,ht⟩:=Ω.frame_target_sorted hpN hnt
    have hr:Reduces (E.subst (Expr.extend e.val n))
        ((E.subst (Expr.liftSub e.val)).nfTerm.instantiate n):=by
      rw [← Expr.instantiate_extended]
      exact (Expr.nfTerm_spec hparts.2).1.subst (Expr.single n)
    exact Expr.nfTerm_converts (htarget.weakNorm hw) (ht.weakNorm hw) hr.converts
  change h ∈ actual Ω hC hw hno (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).nfTerm ↔ _
  change h ∈ actual Ω hC hw hno (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).nfTerm ↔
    h ∈ Top Ω (Expr.pi (D.subst e.val) (E.subst (Expr.liftSub e.val))).nfTerm ∧ _
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
theorem product_intro {Γ:List (Expr S)} {D E:Expr S} {s:S}
    (e:ValEnv Ω Γ) (hp:HasType P Γ (.pi D E) (.sort s))
    (hg:Profile P Γ (.pi D E) ∈ C) (ha:Ω.profile ((Expr.pi D E).subst e.val) ∈ C)
    (h:Expr S) (ht:h ∈ Top Ω ((Expr.pi D E).subst e.val).nfTerm)
    (hb:∀ n,n ∈ R Ω hC hw hno D e → ∀ f:ValEnv Ω (D :: Γ),
      f.val = Expr.extend e.val n → Expr.app h n ∈ R Ω hC hw hno E f) :
    h ∈ R Ω hC hw hno (.pi D E) e:=by
  obtain ⟨a,b,c,hD,hE,_,_⟩:=hp.generation_pi
  have hf:=Profile.triple hw hp
  have hd:=R_before Ω hC hw hno hD e ⟨_,hg,.single (.domain hf)⟩
  simp only [R,hg,ite_true]
  apply (actual_raw_product Ω hC hw hno hp e ha h).mpr
  refine ⟨ht,?_⟩
  intro n hn
  have hnt:=(actual_candidate Ω hC hw hno _).upper hn |>.1
  have hrawD:=CTower.HasType.subst hD e.property
  have hnr:=hnt.conversion hrawD
    (.symm _ _ (Expr.nfTerm_spec (hrawD.weakNorm hw)).1.converts)
  let f:ValEnv Ω (D :: Γ):=⟨Expr.extend e.val n,e.property.cons hnr⟩
  have he:=R_before Ω hC hw hno hE f ⟨_,hg,.single (.codomain hf)⟩
  have hh:=hb n (hd.symm ▸ hn) f rfl
  exact he ▸ hh
theorem specialization {Γ:List (Expr S)} {D E N:Expr S} {s:S}
    (e:ValEnv Ω Γ) (hp:HasType P Γ (.pi D E) (.sort s)) (hN:HasType P Γ N D)
    (hg:Profile P Γ (.pi D E) ∈ C) (ha:Ω.profile ((Expr.pi D E).subst e.val) ∈ C)
    (h:Expr S) (hh:h ∈ R Ω hC hw hno (.pi D E) e)
    (hn:N.subst e.val ∈ R Ω hC hw hno D e) :
    Expr.app h (N.subst e.val) ∈ R Ω hC hw hno (E.instantiate N) e:=by
  obtain ⟨a,b,c,hD,hE,_,_⟩:=hp.generation_pi
  have hf:=Profile.triple hw hp
  have hd:=R_before Ω hC hw hno hD e ⟨_,hg,.single (.domain hf)⟩
  have he:=R_before Ω hC hw hno (hE.instantiate hN) e
    ⟨_,hg,(Profile.instantiate_product_path hw hp hN).reach⟩
  simp only [R,hg,ite_true] at hh
  have hout:=(actual_raw_product Ω hC hw hno hp e ha h).mp hh |>.2 _ (hd ▸ hn)
  rw [he,← Expr.instantiate_subst,Expr.instantiate_extended]
  exact hout
noncomputable def componentInterface:ComponentInterface Ω hw C where
  Env:=ValEnv Ω
  images:=Subtype.val
  typed:=Subtype.property
  inhabit σ hσ:=⟨⟨σ,hσ⟩,rfl⟩
  Ext e f n:=f.val = Expr.extend e.val n
  ext_images he:=he
  extend e _ _ hn:=⟨⟨_,e.property.cons hn⟩,rfl⟩
  R:=R Ω hC hw hno
  candidate e _:=R_candidate Ω hC hw hno _ e
  conversion e ha hb hc:=R_conversion Ω hC hw hno e ha hb hc
  outside e _ ho:=R_outside Ω hC hw hno _ e ho
  weakening hd he hx:=R_weakening Ω hC hw hno hd he hx
  product_intro e hp hg ha h ht hb:=product_intro Ω hC hw hno e hp hg ha h ht hb
  specialization e hp hn hg ha h hh hN:=specialization Ω hC hw hno e hp hn hg ha h hh hN
end S_wpc_barendregt_geuvers_klop.SignedInterpretation
end OMA
namespace OMA
namespace S_wpc_barendregt_geuvers_klop.OneChildInterpretation
section
universe u
open Classical Cands
variable {S:Type u} {P:Specification S} (Ω:CTower P) (C:Set (Set S))
abbrev Bits:=Nat → Bool
def extendBit (θ:Bits) (b:Bool):Bits
  | 0 => b
  | n+1 => θ n
def head:Expr S → Option Nat
  | .var n => some n
  | .app f _ => head f
  | _ => none
noncomputable def eval (Γ:List (Expr S)) (A:Expr S) (σ:Nat → Expr S) (θ:Bits):Set (Expr S) :=
  if Profile P Γ A ∈ C ∧ Ω.profile (A.subst σ) ∈ C then
    match A with
    | .pi D E => RawProduct Ω D E σ (eval Γ D σ θ)
        (fun n b => eval (D :: Γ) E (Expr.extend σ n) (extendBit θ b))
    | A => match head A with
      | none => Top Ω (A.subst σ).nfTerm
      | some i => if θ i then Top Ω (A.subst σ).nfTerm else Bottom Ω (A.subst σ).nfTerm
  else Top Ω (A.subst σ).nfTerm
@[simp] theorem head_rename (A:Expr S) (ρ:Nat → Nat) :
    head (A.rename ρ) = (head A).map ρ:=by
  induction A with
  | app f n ihf ihn => exact ihf
  | var i => rfl
  | sort s => rfl
  | lam D m ihD ihm => rfl
  | pi D E ihD ihE => rfl
theorem head_subst {A:Expr S} {i:Nat} (hi:head A = some i) (σ:Nat → Expr S) :
    head (A.subst σ) = head (σ i):=by
  induction A with
  | var j => cases hi; rfl
  | app f n ihf ihn => exact ihf hi
  | sort s => cases hi
  | pi D E ihD ihE => cases hi
  | lam D m ihD ihm => cases hi
theorem head_beta {A B:Expr S} {i:Nat} (hi:head A = some i) (hr:Beta A B) :
    head B = some i:=by
  induction hr with
  | head D m n => cases hi
  | app_left hr ih => exact ih hi
  | app_right hr ih => exact hi
  | lam_domain hr ih => cases hi
  | lam_body hr ih => cases hi
  | pi_domain hr ih => cases hi
  | pi_body hr ih => cases hi
theorem head_reduces {A B:Expr S} {i:Nat} (hi:head A = some i) (hr:Reduces A B) :
    head B = some i:=by
  induction hr with
  | refl => exact hi
  | tail hr hs ih => exact head_beta ih hs
theorem head_nfTerm {A:Expr S} {i:Nat} (hi:head A = some i) (hw:WeaklyNormalizing A) :
    head A.nfTerm = some i:=head_reduces hi (Expr.nfTerm_spec hw).1
theorem eval_pi (Γ:List (Expr S)) (D E:Expr S) (σ:Nat → Expr S) (θ:Bits) :
    eval Ω C Γ (.pi D E) σ θ =
      if Profile P Γ (.pi D E) ∈ C ∧ Ω.profile ((Expr.pi D E).subst σ) ∈ C then
        RawProduct Ω D E σ (eval Ω C Γ D σ θ)
          (fun n b => eval Ω C (D :: Γ) E (Expr.extend σ n) (extendBit θ b))
      else Top Ω ((Expr.pi D E).subst σ).nfTerm:=rfl
theorem eval_head {Γ:List (Expr S)} {A:Expr S} {σ:Nat → Expr S} {θ:Bits} {i:Nat}
    (hg:Profile P Γ A ∈ C) (ha:Ω.profile (A.subst σ) ∈ C) (hi:head A = some i) :
    eval Ω C Γ A σ θ = if θ i then Top Ω (A.subst σ).nfTerm else Bottom Ω (A.subst σ).nfTerm:=by
  cases A <;> simp only [eval,if_pos (And.intro hg ha)]
  all_goals first | (cases hi <;> rfl) | (rw [hi])
theorem eval_sort (Γ:List (Expr S)) (s:S) (σ:Nat → Expr S) (θ:Bits) :
    eval Ω C Γ (.sort s) σ θ = Top Ω (.sort s):=by
  simp only [eval,head,ite_self,Expr.subst,Expr.nfTerm_of_normal (Normal.sort s)]
variable (hw:SystemWeaklyNormalizing P)
include hw
theorem eval_candidate {Γ:List (Expr S)} {A:Expr S} {s:S}
    {σ:Nat → Expr S} (hA:HasType P Γ A (.sort s)) (hσ:Ω.TySub Γ σ) (θ:Bits) :
    IsCandidate Ω (A.subst σ).nfTerm (eval Ω C Γ A σ θ):=by
  induction A generalizing Γ s σ θ with
  | pi D E ihD ihE =>
    rw [eval]
    split
    · obtain ⟨a,b,c,hD,hE,_,_⟩:=hA.generation_pi
      have hX:=ihD hD hσ θ
      apply rawProduct_candidate hw hA hσ hX
      intro n hn bit
      have hrawD:=CTower.HasType.subst hD hσ
      have ht:=(hX.upper hn).1.conversion hrawD
        (.symm _ _ (Expr.nfTerm_spec (hrawD.weakNorm hw)).1.converts)
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
    · cases hh:head (.app f n) with
      | none => exact top_candidate
      | some i =>
        change IsCandidate Ω (Expr.subst σ (.app f n)).nfTerm
          (if θ i then Top Ω (Expr.subst σ (.app f n)).nfTerm else Bottom Ω (Expr.subst σ (.app f n)).nfTerm)
        split <;> first | exact top_candidate | exact bottom_candidate
    · exact top_candidate
omit hw in
theorem eval_outside {Γ:List (Expr S)} {A:Expr S} {σ:Nat → Expr S} {θ:Bits}
    (ho:Profile P Γ A ∉ C ∨ Ω.profile (A.subst σ) ∉ C) :
    eval Ω C Γ A σ θ = Top Ω (A.subst σ).nfTerm:=by
  have hn:¬ (Profile P Γ A ∈ C ∧ Ω.profile (A.subst σ) ∈ C) :=
    fun h => ho.elim (fun hn => hn h.1) (fun hn => hn h.2)
  cases A <;> simp only [eval,if_neg hn]
def dropSupport:Option (Nat × Bool) → Option (Nat × Bool)
  | some (0,_) => none
  | some (n+1,p) => some (n,p)
  | none => none
def flipSupport:Option (Nat × Bool) → Option (Nat × Bool) :=
  Option.map (fun (n,p) => (n,!p))
noncomputable def support (Γ:List (Expr S)) (A:Expr S):Option (Nat × Bool) :=
  if Profile P Γ A ∈ C then
    match A with
    | .pi D E => if Profile P Γ D ∈ C then flipSupport (support Γ D)
        else dropSupport (support (D :: Γ) E)
    | A => (head A).map (fun i => (i,false))
  else none
structure ValEnv (Γ:List (Expr S)) where
  images:Nat → Expr S
  typed:Ω.TySub Γ images
  bits:Bits
noncomputable def R {Γ:List (Expr S)} (A:Expr S) (e:ValEnv Ω Γ):Set (Expr S) :=
  eval Ω C Γ A.nfTerm e.images e.bits
theorem normal_subst_eq {Γ:List (Expr S)} {A:Expr S}
    (hA:Expected P Γ A) (e:ValEnv Ω Γ) :
    (A.nfTerm.subst e.images).nfTerm = (A.subst e.images).nfTerm:=by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · rw [Expr.nfTerm_of_normal (Normal.sort s)]
  · exact Expr.nfTerm_converts
      ((CTower.HasType.subst (hA.nfTerm hw) e.typed).weakNorm hw)
      ((CTower.HasType.subst hA e.typed).weakNorm hw)
      (.symm _ _ ((Expr.nfTerm_spec (hA.weakNorm hw)).1.converts.subst e.images))
theorem R_candidate {Γ:List (Expr S)} {A:Expr S} (hA:Expected P Γ A) (e:ValEnv Ω Γ) :
    IsCandidate Ω (A.subst e.images).nfTerm (R Ω C A e):=by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · simp only [R,Expr.nfTerm_of_normal (Normal.sort s),eval,head,ite_self]
    exact top_candidate
  · rw [← normal_subst_eq Ω hw (.sorted hA) e]
    exact eval_candidate Ω C hw (hA.nfTerm hw) e.typed e.bits
theorem R_conversion {Γ:List (Expr S)} {A B:Expr S}
    (hA:Expected P Γ A) (hB:Expected P Γ B) (hc:Converts A B) (e:ValEnv Ω Γ) :
    R Ω C A e = R Ω C B e:=by
  simp only [R,Expr.nfTerm_converts (hA.wn hw) (hB.wn hw) hc]
end
section
universe u
open Classical Cands
variable {S:Type u} {P:Specification S} (Ω:CTower P) (C:Set (Set S))
variable (hw:SystemWeaklyNormalizing P)
theorem eval_recontext {Γ Δ:List (Expr S)} {A:Expr S} {s:S}
    (hA:HasType P Γ A (.sort s)) (hc:ContextEquivalent P Γ Δ)
    (σ:Nat → Expr S) (θ:Bits):eval Ω C Γ A σ θ = eval Ω C Δ A σ θ:=by
  induction A generalizing Γ Δ s σ θ with
  | pi D E ihD ihE =>
    obtain ⟨a,b,c,hD,hE,_,_⟩:=hA.generation_pi
    have hp:Profile P Γ (.pi D E) = Profile P Δ (.pi D E):=Set.ext (fun s => hc.typing _ _)
    rw [eval_pi,eval_pi,hp]
    congr 1
    apply congrArg₂ (RawProduct Ω D E σ) (ihD hD hc σ θ)
    funext n bit
    exact ihE hE (hc.cons hD) _ _
  | var i =>
    have hp:Profile P Γ (.var i) = Profile P Δ (.var i):=Set.ext (fun s => hc.typing _ _)
    simp only [eval,hp]
  | sort s => rw [eval_sort,eval_sort]
  | app f n ihf ihn =>
    have hp:Profile P Γ (.app f n) = Profile P Δ (.app f n):=Set.ext (fun s => hc.typing _ _)
    simp only [eval,hp]
  | lam D m ihD ihm => exact False.elim hA.lambda_cannot_have_sort_type
include hw in
theorem eval_rename {Γ Δ:List (Expr S)} {A:Expr S} {s:S}
    (hA:HasType P Γ A (.sort s)) (hΔ:ValidContext P Δ)
    (ρ:Nat → Nat) (hρ:TyTree.DeclRenaming Γ Δ ρ)
    (σ τ:Nat → Expr S) (θ ψ:Bits) (hσ:τ ∘ ρ = σ) (hθ:ψ ∘ ρ = θ) :
    eval Ω C Γ A σ θ = eval Ω C Δ (A.rename ρ) τ ψ:=by
  induction A generalizing Γ Δ s ρ σ τ θ ψ with
  | pi D E ihD ihE =>
    obtain ⟨a,b,c,hD,hE,_,_⟩:=hA.generation_pi
    have hp:=Profile.rename hw hA hΔ ρ (hρ.typed hΔ)
    have he (M:Expr S):(M.rename ρ).subst τ = M.subst σ:=by rw [Expr.subst_rename,hσ]
    rw [eval_pi]
    change _ = eval Ω C Δ (.pi (D.rename ρ) (E.rename (Expr.liftRen ρ))) τ ψ
    rw [eval_pi]
    have hraw:(Expr.pi (D.rename ρ) (E.rename (Expr.liftRen ρ))).subst τ = (Expr.pi D E).subst σ:=he (.pi D E)
    have hX:=ihD hD hΔ ρ hρ σ τ θ ψ hσ hθ
    have hY:(fun n bit => eval Ω C (D :: Γ) E (Expr.extend σ n) (extendBit θ bit)) =
        (fun n bit => eval Ω C (D.rename ρ :: Δ) (E.rename (Expr.liftRen ρ))
          (Expr.extend τ n) (extendBit ψ bit)):=by
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
    have hp:=Profile.rename hw hA hΔ ρ (hρ.typed hΔ)
    have he:(.var (ρ i):Expr S).subst τ = Expr.subst σ (.var i):=congrFun hσ i
    change Profile P Δ (.var (ρ i)) = _ at hp
    simp only [eval,Expr.rename,hp,he,head]
    rw [show ψ (ρ i) = θ i from congrFun hθ i]
  | lam D m ihD ihm => exact False.elim hA.lambda_cannot_have_sort_type
  | app f n ihf ihn =>
    have hp:=Profile.rename hw hA hΔ ρ (hρ.typed hΔ)
    have he:((Expr.app f n).rename ρ).subst τ = (Expr.app f n).subst σ:=by rw [Expr.subst_rename,hσ]
    simp only [Expr.rename] at hp he ⊢
    simp only [eval,hp,he,head,head_rename]
    cases hh:head f with
    | none => rfl
    | some i => simp only [Option.map_some]; rw [show ψ (ρ i) = θ i from congrFun hθ i]
namespace ValEnv
variable {Ω}
def Ext {Γ:List (Expr S)} {D:Expr S} (e:ValEnv Ω Γ) (f:ValEnv Ω (D :: Γ)) (n:Expr S):Prop :=
  f.images = Expr.extend e.images n ∧ ∀ i,f.bits (i+1) = e.bits i
end ValEnv
theorem R_sort {Γ:List (Expr S)} (s:S) (e:ValEnv Ω Γ) :
    R Ω C (.sort s) e = Top Ω (.sort s):=by
  rw [R,Expr.nfTerm_of_normal (Normal.sort s),eval_sort]
include hw in
theorem R_weakening {Γ:List (Expr S)} {D A n:Expr S} {s:S}
    {e:ValEnv Ω Γ} {f:ValEnv Ω (D :: Γ)}
    (hD:HasType P Γ D (.sort s)) (hA:Expected P Γ A) (he:e.Ext f n) :
    R Ω C (A.rename Nat.succ) f = R Ω C A e:=by
  rcases hA with ⟨a,rfl⟩ | ⟨a,hA⟩
  · exact (R_sort Ω C a f).trans (R_sort Ω C a e).symm
  · rw [R,R,Expr.nfTerm_rename (hA.weakNorm hw)]
    symm
    apply eval_rename Ω C hw (hA.nfTerm hw) (.cons hD.valid hD) Nat.succ (TyTree.DeclRenaming.weaken D)
    · rw [he.1]; rfl
    · exact funext (fun i => he.2 i)
end
section
universe u
open Classical Cands
variable {S:Type u} {P:Specification S} (Ω:CTower P) (C:Set (Set S))
variable (hw:SystemWeaklyNormalizing P)
include hw
theorem normal_product {Γ:List (Expr S)} {D E:Expr S} {s:S}
    (hp:HasType P Γ (.pi D E) (.sort s)) (σ:Nat → Expr S)
    (hσ:Ω.TySub Γ σ) (θ:Bits) :
    eval Ω C Γ (Expr.pi D E).nfTerm σ θ =
      if Profile P Γ (.pi D E) ∈ C ∧ Ω.profile ((Expr.pi D E).subst σ) ∈ C then
        RawProduct Ω D E σ (eval Ω C Γ D.nfTerm σ θ)
          (fun n b => eval Ω C (D :: Γ) E.nfTerm (Expr.extend σ n) (extendBit θ b))
      else Top Ω ((Expr.pi D E).subst σ).nfTerm:=by
  obtain ⟨a,b,c,hD,hE,hr,_⟩:=hp.generation_pi
  have hDN:=hD.nfTerm hw
  have hEN:=hE.nfTerm hw
  have cD:=(Expr.nfTerm_spec (hD.weakNorm hw)).1.converts
  have cE:=(Expr.nfTerm_spec (hE.weakNorm hw)).1.converts
  let ctx:=ContextEquivalent.head_conversion hD hDN cD
  have hEN':=(ctx.typing _ _).mp hEN
  have hpn:HasType P Γ (.pi D.nfTerm E.nfTerm) (.sort c):=.product hDN hEN' hr
  have nc:=Converts.pi cD cE
  have he:Profile P Γ (.pi D E) = Profile P Γ (.pi D.nfTerm E.nfTerm) :=
    Profile.converts (hp.weakNorm hw) (hpn.weakNorm hw) nc
  have hrw:=(CTower.HasType.subst hp hσ).weakNorm hw
  have hnw:=(CTower.HasType.subst hpn hσ).weakNorm hw
  have hnf:=Expr.nfTerm_converts hrw hnw (nc.subst σ)
  have hae:Ω.profile ((Expr.pi D E).subst σ) = Ω.profile ((Expr.pi D.nfTerm E.nfTerm).subst σ):=by
    rw [←Ω.profile_nfTerm ((Expr.pi D E).subst σ),←Ω.profile_nfTerm ((Expr.pi D.nfTerm E.nfTerm).subst σ),hnf]
  rw [Expr.nfTerm_pi (hD.weakNorm hw) (hE.weakNorm hw),eval_pi,←he,←hae]
  split
  · unfold RawProduct
    rw [←hnf]
    simp_rw [←eval_recontext Ω C hEN ctx]
  · exact congrArg (Top Ω) hnf.symm
theorem R_outside {Γ:List (Expr S)} {A:Expr S} (hA:Expected P Γ A)
    (e:ValEnv Ω Γ) (ho:Profile P Γ A ∉ C ∨ Ω.profile (A.subst e.images) ∉ C) :
    R Ω C A e = Top Ω (A.subst e.images).nfTerm:=by
  have hnf:=normal_subst_eq Ω hw hA e
  rw [R,eval_outside Ω C,hnf]
  rcases ho with ho | ho
  · exact .inl (by rwa [Profile.nfTerm])
  · exact .inr (by
      rw [←Ω.profile_nfTerm (A.nfTerm.subst e.images),hnf,Ω.profile_nfTerm]
      exact ho)
theorem product_iff {Γ:List (Expr S)} {D E:Expr S} {s:S}
    (hp:HasType P Γ (.pi D E) (.sort s)) (hg:Profile P Γ (.pi D E) ∈ C)
    (e:ValEnv Ω Γ) (ha:Ω.profile ((Expr.pi D E).subst e.images) ∈ C) (h:Expr S) :
    h ∈ R Ω C (.pi D E) e ↔
      h ∈ Top Ω ((Expr.pi D E).subst e.images).nfTerm ∧
      ∀ n,n ∈ R Ω C D e → ∀ f:ValEnv Ω (D :: Γ),e.Ext f n → Expr.app h n ∈ R Ω C E f:=by
  rw [R,normal_product Ω C hw hp e.images e.typed e.bits,if_pos ⟨hg,ha⟩]
  obtain ⟨a,b,c,hD,hE,_,_⟩:=hp.generation_pi
  constructor
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hn f he
    have hb:f.bits = extendBit e.bits (f.bits 0):=by
      funext i; cases i with
      | zero => rfl
      | succ i => exact he.2 i
    change Expr.app h n ∈ eval Ω C (D :: Γ) E.nfTerm f.images f.bits
    rw [he.1,hb]
    exact hbody n hn (f.bits 0)
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hn bit
    have hrawD:=CTower.HasType.subst hD e.typed
    have hnt:=((R_candidate Ω C hw (.sorted hD) e).upper hn).1.conversion hrawD
      (.symm _ _ (Expr.nfTerm_spec (hrawD.weakNorm hw)).1.converts)
    let f:ValEnv Ω (D :: Γ):=⟨Expr.extend e.images n,e.typed.cons hnt,extendBit e.bits bit⟩
    exact hbody n hn f ⟨rfl,fun _ => rfl⟩
end
section
universe u
open Classical
variable {S:Type u} {P:Specification S} (C:Set (Set S))
def CompatibleBits (r:Option (Nat × Bool)) (dir:Bool) (σ:Nat → Expr S) (θ ψ:Bits):Prop :=
  ∀ i p,r = some (i,p) → (∃ j,σ i = .var j ∧ θ i = ψ j) ∨ θ i = Bool.xor dir p
def Below {α:Type*} (dir:Bool) (X Y:Set α):Prop:=if dir then Y ⊆ X else X ⊆ Y
theorem support_outside {Γ:List (Expr S)} {A:Expr S} (h:Profile P Γ A ∉ C) :
    support (P:=P) C Γ A = none:=by cases A <;> simp only [support,if_neg h]
theorem support_head {Γ:List (Expr S)} {A:Expr S} {i:Nat}
    (hg:Profile P Γ A ∈ C) (hi:head A = some i):support (P:=P) C Γ A = some (i,false):=by
  cases A <;> simp only [support,if_pos hg]
  all_goals first | (cases hi <;> rfl) | (rw [hi]; rfl)
theorem bits_domain {Γ:List (Expr S)} {D E:Expr S} {dir:Bool}
    {σ:Nat → Expr S} {θ ψ:Bits} (hg:Profile P Γ (.pi D E) ∈ C)
    (hb:CompatibleBits (support (P:=P) C Γ (.pi D E)) dir σ θ ψ) :
    CompatibleBits (support (P:=P) C Γ D) (!dir) σ θ ψ:=by
  intro i p hi
  by_cases hd:Profile P Γ D ∈ C
  · have hp:support (P:=P) C Γ (.pi D E) = some (i,!p):=by
      rw [support,if_pos hg,if_pos hd,flipSupport,hi]; rfl
    rcases hb i (!p) hp with h | h
    · exact .inl h
    · right
      have he:Bool.xor dir (!p) = Bool.xor (!dir) p:=by cases dir <;> cases p <;> rfl
      exact h.trans he
  · rw [support_outside C hd] at hi
    cases hi
theorem bits_body (hw:SystemWeaklyNormalizing P)
    (hno:∀ {I J K},ProfileTriple P I J K → I ∈ C → J ∈ C → K ∈ C → False)
    {Γ:List (Expr S)} {D E:Expr S} {s:S} {dir:Bool}
    {σ:Nat → Expr S} {θ ψ:Bits} (hp:HasType P Γ (.pi D E) (.sort s))
    (hg:Profile P Γ (.pi D E) ∈ C)
    (hb:CompatibleBits (support (P:=P) C Γ (.pi D E)) dir σ θ ψ) (bit:Bool) :
    CompatibleBits (support (P:=P) C (D :: Γ) E) dir (Expr.liftSub σ) (extendBit θ bit) (extendBit ψ bit):=by
  intro i p hi
  by_cases hd:Profile P Γ D ∈ C
  · have he:Profile P (D :: Γ) E ∉ C:=fun he => hno (Profile.triple hw hp) hd he hg
    rw [support_outside C he] at hi
    cases hi
  · cases i with
    | zero => exact .inl ⟨0,rfl,rfl⟩
    | succ i =>
      have hh:support (P:=P) C Γ (.pi D E) = some (i,p):=by
        rw [support,if_pos hg,if_neg hd,hi]; rfl
      rcases hb i p hh with ⟨j,hj,he⟩ | he
      · left
        exact ⟨j+1,by rw [Expr.liftSub_succ,hj]; rfl,he⟩
      · exact .inr he
noncomputable def chosenBit (Γ:List (Expr S)) (A:Expr S):Bool :=
  match support (P:=P) C Γ A with
  | some (0,p) => p
  | _ => true
theorem bits_single (Γ:List (Expr S)) (A N:Expr S) (θ:Bits) :
    CompatibleBits (support (P:=P) C Γ A) false (Expr.single N) (extendBit θ (chosenBit (P:=P) C Γ A)) θ:=by
  intro i p hi
  cases i with
  | zero =>
    right
    simp only [extendBit,chosenBit,hi,Bool.false_xor]
  | succ i => exact .inl ⟨i,rfl,rfl⟩
end
section
universe u
open Classical Cands
variable {S:Type u} {P:Specification S} (Ω:CTower P) (C:Set (Set S))
variable (hw:SystemWeaklyNormalizing P)
include hw
theorem subst_profile_path {Γ Δ:List (Expr S)} {A:Expr S} {s:S}
    (hA:HasType P Γ A (.sort s)) (hΔ:ValidContext P Δ) (δ:Nat → Expr S)
    (hδ:TySub P Γ Δ δ) :
    PositivePath (PriEdge P) (Profile P Δ (A.subst δ)) (Profile P Γ A) :=
  Profile.inclusion_path
    (Profile.feasible ((hA.subst hΔ δ hδ).weakNorm hw) (Profile.nonempty_of_sorted hw (hA.subst hΔ δ hδ)))
    (Profile.feasible (hA.weakNorm hw) (Profile.nonempty_of_sorted hw hA))
    (Profile.growth hw (hA.weakNorm hw) hΔ δ hδ)
theorem neutral_compare {Γ Δ:List (Expr S)} {A:Expr S} {s:S}
    (hA:HasType P Γ A (.sort s)) (hΔ:ValidContext P Δ) (δ:Nat → Expr S)
    (hδ:TySub P Γ Δ δ) (e:ValEnv Ω Δ) (θ:Bits) (dir:Bool) {i:Nat}
    (hi:head A = some i) (hg:Profile P Γ A ∈ C)
    (hp:Profile P Δ (A.subst δ) ∈ C)
    (ha:Ω.profile (A.subst (fun i => (δ i).subst e.images)) ∈ C)
    (hb:CompatibleBits (support (P:=P) C Γ A) dir δ θ e.bits) :
    Below dir (eval Ω C Γ A (fun i => (δ i).subst e.images) θ) (R Ω C (A.subst δ) e):=by
  have ht:=hA.subst hΔ δ hδ
  have hcomp:((A.subst δ).subst e.images) = A.subst (fun i => (δ i).subst e.images):=Expr.subst_subst _ _ _
  have hc:=R_candidate Ω C hw (.sorted ht) e
  rw [hcomp] at hc
  rw [eval_head Ω C hg ha hi]
  rcases hb i false (support_head C hg hi) with ⟨j,hj,hbit⟩ | hbit
  · have hhead:head (A.subst δ).nfTerm = some j :=
      head_nfTerm (by rw [head_subst hi,hj]; rfl) (ht.weakNorm hw)
    have hnf:=normal_subst_eq Ω hw (.sorted ht) e
    have ha':Ω.profile (((A.subst δ).nfTerm).subst e.images) ∈ C:=by
      rw [←Ω.profile_nfTerm (((A.subst δ).nfTerm).subst e.images),hnf,Ω.profile_nfTerm,hcomp]
      exact ha
    have he:R Ω C (A.subst δ) e =
        if e.bits j then Top Ω (A.subst (fun i => (δ i).subst e.images)).nfTerm
        else Bottom Ω (A.subst (fun i => (δ i).subst e.images)).nfTerm:=by
      rw [R,eval_head Ω C (by rwa [Profile.nfTerm]) ha' hhead,hnf,hcomp]
    rw [he,hbit]
    cases dir <;> exact Set.Subset.rfl
  · simp only [Bool.xor_false] at hbit
    rw [hbit]
    cases dir with
    | false => exact bottom_le hc
    | true => exact hc.upper
omit hw in
@[simp] theorem head_apps (M:Expr S) (ns:List (Expr S)):head (M.apps ns) = head M:=by
  induction ns generalizing M with
  | nil => rfl
  | cons n ns ih => exact ih _
omit hw in
theorem normal_app_head {Γ:List (Expr S)} {f n:Expr S} {s:S}
    (ht:HasType P Γ (.app f n) (.sort s)) (hn:Normal (.app f n)) :
    ∃ i,head (.app f n) = some i:=by
  have hneutral {M:Expr S} (h:Neutral M):∃ i,head M = some i:=by
    induction h with
    | var i => exact ⟨i,rfl⟩
    | app h ih => exact ih
  obtain ⟨s,he⟩ | h | ⟨D,E,he⟩:=ht.sorted_normal_shape hn
  · cases he
  · exact hneutral h
  · cases he
variable (hC:IsComp (PriEdge P) C)
variable (hno:∀ {I J K},ProfileTriple P I J K → I ∈ C → J ∈ C → K ∈ C → False)
include hC hno hw
theorem compare_subst {Γ Δ:List (Expr S)} {A:Expr S} {s:S}
    (hA:HasType P Γ A (.sort s)) (hN:Normal A)
    (hrel:∃ K ∈ C,Reach (PriEdge P) (Profile P Γ A) K)
    (hΔ:ValidContext P Δ) (δ:Nat → Expr S) (hδ:TySub P Γ Δ δ)
    (e:ValEnv Ω Δ) (θ:Bits) (dir:Bool)
    (hb:CompatibleBits (support (P:=P) C Γ A) dir δ θ e.bits) :
    Below dir (eval Ω C Γ A (fun i => (δ i).subst e.images) θ) (R Ω C (A.subst δ) e):=by
  induction A generalizing Γ Δ s δ θ dir with
  | var i =>
    have ht:=hA.subst hΔ δ hδ
    have he:(((Expr.var i).subst δ).subst e.images) = (Expr.var i).subst (fun i => (δ i).subst e.images):=Expr.subst_subst _ _ _
    have hpa:=Ω.profile_subst_path hw ht e.typed
    have hpg:=subst_profile_path hw hA hΔ δ hδ
    by_cases ha:Ω.profile ((Expr.var i).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg:Profile P Γ (Expr.var i) ∈ C:=by
      obtain ⟨K,hK,hpath⟩:=hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp:Profile P Δ ((Expr.var i).subst δ) ∈ C:=by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach
    exact neutral_compare Ω C hw hA hΔ δ hδ e θ dir rfl hg hp ha hb
  | app f n ihf ihn =>
    have ht:=hA.subst hΔ δ hδ
    have he:(((Expr.app f n).subst δ).subst e.images) = (Expr.app f n).subst (fun i => (δ i).subst e.images):=Expr.subst_subst _ _ _
    have hpa:=Ω.profile_subst_path hw ht e.typed
    have hpg:=subst_profile_path hw hA hΔ δ hδ
    by_cases ha:Ω.profile ((Expr.app f n).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg:Profile P Γ (Expr.app f n) ∈ C:=by
      obtain ⟨K,hK,hpath⟩:=hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp:Profile P Δ ((Expr.app f n).subst δ) ∈ C:=by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach
    obtain ⟨i,hi⟩:=normal_app_head hA hN
    exact neutral_compare Ω C hw hA hΔ δ hδ e θ dir hi hg hp ha hb
  | sort a =>
    have ht:=hA.subst hΔ δ hδ
    have he:(((Expr.sort a).subst δ).subst e.images) = (Expr.sort a).subst (fun i => (δ i).subst e.images):=Expr.subst_subst _ _ _
    have hpa:=Ω.profile_subst_path hw ht e.typed
    have hpg:=subst_profile_path hw hA hΔ δ hδ
    by_cases ha:Ω.profile ((Expr.sort a).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg:Profile P Γ (Expr.sort a) ∈ C:=by
      obtain ⟨K,hK,hpath⟩:=hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp:Profile P Δ ((Expr.sort a).subst δ) ∈ C:=by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach
    rw [eval_sort,Expr.subst,R_sort]
    cases dir <;> exact Set.Subset.rfl
  | lam D m ihD ihm =>
    have ht:=hA.subst hΔ δ hδ
    have he:(((Expr.lam D m).subst δ).subst e.images) = (Expr.lam D m).subst (fun i => (δ i).subst e.images):=Expr.subst_subst _ _ _
    have hpa:=Ω.profile_subst_path hw ht e.typed
    have hpg:=subst_profile_path hw hA hΔ δ hδ
    by_cases ha:Ω.profile ((Expr.lam D m).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg:Profile P Γ (Expr.lam D m) ∈ C:=by
      obtain ⟨K,hK,hpath⟩:=hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp:Profile P Δ ((Expr.lam D m).subst δ) ∈ C:=by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach
    exact False.elim hA.lambda_cannot_have_sort_type
  | pi D E ihD ihE =>
    have ht:=hA.subst hΔ δ hδ
    have he:(((Expr.pi D E).subst δ).subst e.images) = (Expr.pi D E).subst (fun i => (δ i).subst e.images):=Expr.subst_subst _ _ _
    have hpa:=Ω.profile_subst_path hw ht e.typed
    have hpg:=subst_profile_path hw hA hΔ δ hδ
    by_cases ha:Ω.profile ((Expr.pi D E).subst (fun i => (δ i).subst e.images)) ∈ C
    swap
    · rw [eval_outside Ω C (.inr ha),R_outside Ω C hw (.sorted ht) e (.inr (by rwa [he])),he]
      cases dir <;> exact Set.Subset.rfl
    have hg:Profile P Γ (Expr.pi D E) ∈ C:=by
      obtain ⟨K,hK,hpath⟩:=hrel
      rw [he] at hpa
      exact hC.between ha hK (hpa.reach.trans hpg.reach) hpath
    have hp:Profile P Δ ((Expr.pi D E).subst δ) ∈ C:=by
      rw [he] at hpa
      exact hC.between ha hg hpa.reach hpg.reach
    obtain ⟨a,b,c,hD,hE,hr,_⟩:=hA.generation_pi
    have hDn:=hN.pi_domain
    have hEn:=hN.pi_body
    have tr:=Profile.triple hw hA
    have relD:∃ K ∈ C,Reach (PriEdge P) (Profile P Γ D) K:=⟨_,hg,.single (.domain tr)⟩
    have relE:∃ K ∈ C,Reach (PriEdge P) (Profile P (D :: Γ) E) K:=⟨_,hg,.single (.codomain tr)⟩
    have hδD:=hD.subst hΔ δ hδ
    have dom:=ihD hD hDn relD hΔ δ hδ e θ (!dir) (bits_domain C hg hb)
    have body (n:Expr S) (hn:n ∈ R Ω C (D.subst δ) e) (bit:Bool) :
        Below dir (eval Ω C (D :: Γ) E (Expr.extend (fun i => (δ i).subst e.images) n) (extendBit θ bit))
          (eval Ω C (D.subst δ :: Δ) (E.subst (Expr.liftSub δ)).nfTerm
            (Expr.extend e.images n) (extendBit e.bits bit)):=by
      have hrawD:=CTower.HasType.subst hδD e.typed
      have hnt:=((R_candidate Ω C hw (.sorted hδD) e).upper hn).1.conversion hrawD
        (.symm _ _ (Expr.nfTerm_spec (hrawD.weakNorm hw)).1.converts)
      let f:ValEnv Ω (D.subst δ :: Δ):=⟨Expr.extend e.images n,e.typed.cons hnt,extendBit e.bits bit⟩
      have hbody:=ihE hE hEn relE (.cons hΔ hδD) (Expr.liftSub δ) (hδ.lift hδD)
        f (extendBit θ bit) dir (bits_body C hw hno hA hg hb bit)
      have hei:(fun i => (Expr.liftSub δ i).subst f.images) = Expr.extend (fun i => (δ i).subst e.images) n:=by
        funext i
        cases i with
        | zero => rfl
        | succ i => exact Expr.subst_raise_extend (δ i) n e.images
      rw [hei] at hbody
      exact hbody
    rw [eval_pi,if_pos ⟨hg,ha⟩,R,Expr.subst,normal_product Ω C hw ht _ e.typed e.bits,if_pos ⟨hp,by change Ω.profile (((Expr.pi D E).subst δ).subst e.images) ∈ C; rwa [he]⟩]
    change Below dir (RawProduct Ω D E _ _ _) (RawProduct Ω (D.subst δ) (E.subst (Expr.liftSub δ)) e.images _ _)
    have hraw:((Expr.pi (D.subst δ) (E.subst (Expr.liftSub δ))).subst e.images).nfTerm =
        ((Expr.pi D E).subst (fun i => (δ i).subst e.images)).nfTerm:=congrArg Expr.nfTerm he
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
open Classical Cands
variable {S:Type u} {P:Specification S} (Ω:CTower P) (C:Set (Set S))
variable (hw:SystemWeaklyNormalizing P) (hC:IsComp (PriEdge P) C)
variable (hno:∀ {I J K},ProfileTriple P I J K → I ∈ C → J ∈ C → K ∈ C → False)
include hw hC hno
theorem specialization {Γ:List (Expr S)} {D E N:Expr S} {s:S}
    (e:ValEnv Ω Γ) (hp:HasType P Γ (.pi D E) (.sort s))
    (hN:HasType P Γ N D) (hg:Profile P Γ (.pi D E) ∈ C)
    (ha:Ω.profile ((Expr.pi D E).subst e.images) ∈ C) (h:Expr S)
    (hh:h ∈ R Ω C (.pi D E) e) (hn:N.subst e.images ∈ R Ω C D e) :
    Expr.app h (N.subst e.images) ∈ R Ω C (E.instantiate N) e:=by
  obtain ⟨a,b,c,hD,hE,hr,_⟩:=hp.generation_pi
  let bit:=chosenBit (P:=P) C (D :: Γ) E.nfTerm
  let f:ValEnv Ω (D :: Γ):=⟨Expr.extend e.images (N.subst e.images),
    e.typed.cons (CTower.HasType.subst hN e.typed),extendBit e.bits bit⟩
  have hm:=((product_iff Ω C hw hp hg e ha h).mp hh).2 (N.subst e.images) hn f ⟨rfl,fun _ => rfl⟩
  have hrel:∃ K ∈ C,Reach (PriEdge P) (Profile P (D :: Γ) E.nfTerm) K:=by
    rw [Profile.nfTerm]
    exact ⟨_,hg,.single (.codomain (Profile.triple hw hp))⟩
  have hc:=compare_subst Ω C hw hC hno (hE.nfTerm hw)
    (Expr.nfTerm_spec (hE.weakNorm hw)).2 hrel hD.valid (Expr.single N)
    (TySub.single hN) e f.bits false (bits_single C (D :: Γ) E.nfTerm N e.bits)
  have he:(fun i => (Expr.single N i).subst e.images) = f.images:=by
    funext i; cases i <;> rfl
  rw [he] at hc
  have hout:=hc hm
  have ht:=hE.instantiate hN
  have ht':=(hE.nfTerm hw).instantiate hN
  have cE:=(Expr.nfTerm_spec (hE.weakNorm hw)).1.converts.subst (Expr.single N)
  exact (R_conversion Ω C hw (.sorted ht) (.sorted ht') cE e).symm ▸ hout
noncomputable def componentInterface:ComponentInterface Ω hw C where
  Env:=ValEnv Ω
  images:=ValEnv.images
  typed:=ValEnv.typed
  inhabit σ hσ:=⟨⟨σ,hσ,fun _ => false⟩,rfl⟩
  Ext:=ValEnv.Ext
  ext_images he:=he.1
  extend e _ n hn:=⟨⟨Expr.extend e.images n,e.typed.cons hn,extendBit e.bits false⟩,rfl,fun _ => rfl⟩
  R:=R Ω C
  candidate e hA:=R_candidate Ω C hw hA e
  conversion e ha hb hc:=R_conversion Ω C hw ha hb hc e
  outside e ht ho:=R_outside Ω C hw ht e ho
  weakening hd he hx:=R_weakening Ω C hw hd he hx
  product_intro e hp hg ha h ht hb:=(product_iff Ω C hw hp hg e ha h).mpr ⟨ht,hb⟩
  specialization e hp hN hg ha h hh hn:=specialization Ω C hw hC hno e hp hN hg ha h hh hn
end S_wpc_barendregt_geuvers_klop.OneChildInterpretation
end OMA
namespace OMA
namespace S_wpc_barendregt_geuvers_klop
universe u
namespace FreeObs
variable (Q V B O:Type u)
inductive Payload (Y:Type u):Type u
  | none:Payload Y
  | opposite:Y → Payload Y
  | plain:V → Payload Y
abbrev Frame (Y:Type u):Type u:=Q × Payload V Y
abbrev ContinueStack (Y:Type u):Type u:=List (Frame Q V Y)
abbrev ExitStack (Y:Type u):Type u:=ContinueStack Q V Y × Frame Q V Y
structure Table (Y:Type u):Type u where
  continuing:ContinueStack Q V Y → B
  exiting:ExitStack Q V Y → O
namespace Payload
variable {V:Type u} {X Y Z:Type u}
def map (f:X → Y):Payload V X → Payload V Y
  | none => none
  | opposite x => opposite (f x)
  | plain v => plain v
@[simp] theorem map_id (p:Payload V X):map id p = p:=by cases p <;> rfl
@[simp] theorem map_comp (f:X → Y) (g:Y → Z) (p:Payload V X) :
    map g (map f p) = map (g ∘ f) p:=by cases p <;> rfl
theorem map_injective {f:X → Y} (hf:Function.Injective f) :
    Function.Injective (map (V:=V) f):=by
  intro p q he
  cases p <;> cases q <;> simp_all [map,hf.eq_iff]
theorem map_surjective {f:X → Y} (hf:Function.Surjective f) :
    Function.Surjective (map (V:=V) f):=by
  intro p
  cases p with
  | none => exact ⟨.none,rfl⟩
  | plain v => exact ⟨.plain v,rfl⟩
  | opposite y => obtain ⟨x,rfl⟩:=hf y; exact ⟨.opposite x,rfl⟩
end Payload
variable {Q V B O} {X Y Z:Type u}
def mapFrame (f:X → Y) (a:Frame Q V X):Frame Q V Y :=
  (a.1,Payload.map f a.2)
def mapContinue (f:X → Y):ContinueStack Q V X → ContinueStack Q V Y :=
  List.map (mapFrame f)
def mapExit (f:X → Y) (a:ExitStack Q V X):ExitStack Q V Y :=
  (mapContinue f a.1,mapFrame f a.2)
@[simp] theorem mapFrame_id (a:Frame Q V X):mapFrame id a = a:=by
  cases a; simp [mapFrame]
@[simp] theorem mapFrame_comp (f:X → Y) (g:Y → Z) (a:Frame Q V X) :
    mapFrame g (mapFrame f a) = mapFrame (g ∘ f) a:=by
  simp [mapFrame]
@[simp] theorem mapContinue_id (a:ContinueStack Q V X):mapContinue id a = a:=by
  induction a with
  | nil => rfl
  | cons a as ih => simpa only [mapContinue,List.map_cons,mapFrame_id] using congrArg (List.cons a) ih
@[simp] theorem mapContinue_comp (f:X → Y) (g:Y → Z) (a:ContinueStack Q V X) :
    mapContinue g (mapContinue f a) = mapContinue (g ∘ f) a:=by
  simp only [mapContinue,List.map_map]
  congr 1
  funext a
  exact mapFrame_comp f g a
@[simp] theorem mapExit_id (a:ExitStack Q V X):mapExit id a = a:=by
  cases a; simp [mapExit]
@[simp] theorem mapExit_comp (f:X → Y) (g:Y → Z) (a:ExitStack Q V X) :
    mapExit g (mapExit f a) = mapExit (g ∘ f) a:=by
  simp [mapExit]
theorem mapFrame_injective {f:X → Y} (hf:Function.Injective f) :
    Function.Injective (mapFrame (Q:=Q) (V:=V) f):=by
  intro p q he
  change (p.1,Payload.map f p.2) = (q.1,Payload.map f q.2) at he
  exact Prod.ext (congrArg (fun z:Q × Payload V Y => z.1) he)
    (Payload.map_injective hf (congrArg (fun z:Q × Payload V Y => z.2) he))
theorem mapFrame_surjective {f:X → Y} (hf:Function.Surjective f) :
    Function.Surjective (mapFrame (Q:=Q) (V:=V) f):=by
  intro p
  obtain ⟨v,hv⟩:=Payload.map_surjective hf p.2
  exact ⟨(p.1,v),Prod.ext rfl hv⟩
theorem mapContinue_injective {f:X → Y} (hf:Function.Injective f) :
    Function.Injective (mapContinue (Q:=Q) (V:=V) f) :=
  List.map_injective_iff.mpr (mapFrame_injective hf)
theorem mapContinue_surjective {f:X → Y} (hf:Function.Surjective f) :
    Function.Surjective (mapContinue (Q:=Q) (V:=V) f) :=
  List.map_surjective_iff.mpr (mapFrame_surjective hf)
theorem mapExit_injective {f:X → Y} (hf:Function.Injective f) :
    Function.Injective (mapExit (Q:=Q) (V:=V) f):=by
  intro p q he
  exact Prod.ext (mapContinue_injective hf (congrArg Prod.fst he))
    (mapFrame_injective hf (congrArg Prod.snd he))
theorem mapExit_surjective {f:X → Y} (hf:Function.Surjective f) :
    Function.Surjective (mapExit (Q:=Q) (V:=V) f):=by
  intro p
  obtain ⟨s,hs⟩:=mapContinue_surjective hf p.1
  obtain ⟨a,ha⟩:=mapFrame_surjective hf p.2
  exact ⟨(s,a),Prod.ext hs ha⟩
namespace Table
theorem ext {a b:Table Q V B O X} (hc:a.continuing=b.continuing) (he:a.exiting=b.exiting):a=b:=by cases a; cases b; congr
def relabel (f:X → Y) (t:Table Q V B O Y):Table Q V B O X where
  continuing:=t.continuing ∘ mapContinue f
  exiting:=t.exiting ∘ mapExit f
@[simp] theorem relabel_id (t:Table Q V B O X):relabel id t = t:=by
  apply Table.ext <;> funext x <;> simp [relabel]
@[simp] theorem relabel_comp (f:X → Y) (g:Y → Z) (t:Table Q V B O Z) :
    relabel f (relabel g t) = relabel (g ∘ f) t:=by
  apply Table.ext <;> funext x <;> simp [relabel]
def default (b:B) (o:O):Table Q V B O X where
  continuing:=fun _ => b
  exiting:=fun _ => o
@[simp] theorem relabel_default (f:X → Y) (b:B) (o:O) :
    relabel (Q:=Q) (V:=V) f (default b o) = default b o:=rfl
theorem relabel_injective {f:X → Y} (hf:Function.Surjective f) :
    Function.Injective (relabel (Q:=Q) (V:=V) (B:=B) (O:=O) f):=by
  intro a b h
  apply Table.ext
  · funext s
    obtain ⟨t,rfl⟩:=mapContinue_surjective hf s
    exact congrFun (congrArg Table.continuing h) t
  · funext s
    obtain ⟨t,rfl⟩:=mapExit_surjective hf s
    exact congrFun (congrArg Table.exiting h) t
theorem relabel_surjective {f:X → Y} (hf:Function.Injective f) (b:B) (o:O) :
    Function.Surjective (relabel (Q:=Q) (V:=V) (B:=B) (O:=O) f):=by
  intro t
  obtain ⟨c,hc⟩:=(mapContinue_injective hf).surjective_comp_right' (fun _ => b) t.continuing
  obtain ⟨e,he⟩:=(mapExit_injective hf).surjective_comp_right' (fun _ => o) t.exiting
  exact ⟨⟨c,e⟩,Table.ext hc he⟩
theorem relabel_range_iff {f:X → Y} (hf:Function.Surjective f) (t:Table Q V B O X) :
    (∃ s,relabel f s = t) ↔
      (∀ a b,mapContinue f a = mapContinue f b → t.continuing a = t.continuing b) ∧
      (∀ a b,mapExit f a = mapExit f b → t.exiting a = t.exiting b):=by
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨fun _ _ he => congrArg s.continuing he,fun _ _ he => congrArg s.exiting he⟩
  · rintro ⟨hc,he⟩
    classical
    let c:ContinueStack Q V Y → ContinueStack Q V X:=fun a => (mapContinue_surjective hf a).choose
    let e:ExitStack Q V Y → ExitStack Q V X:=fun a => (mapExit_surjective hf a).choose
    have ch:∀ a,mapContinue f (c a) = a:=fun a => (mapContinue_surjective hf a).choose_spec
    have eh:∀ a,mapExit f (e a) = a:=fun a => (mapExit_surjective hf a).choose_spec
    refine ⟨⟨t.continuing ∘ c,t.exiting ∘ e⟩,?_⟩
    apply Table.ext
    · funext a
      exact hc _ _ (ch _)
    · funext a
      exact he _ _ (eh _)
def slice (t:Table Q V B O X) (a:Frame Q V X):Table Q V B O X where
  continuing:=fun ns => t.continuing (a :: ns)
  exiting:=fun ns => t.exiting (a :: ns.1,ns.2)
@[simp] theorem slice_relabel (f:X → Y) (t:Table Q V B O Y) (a:Frame Q V X) :
    (relabel f t).slice a = relabel f (t.slice (mapFrame f a)):=rfl
end Table
variable (Q V B O) in
abbrev Stage:ℕ → Type u
  | 0 => PEmpty
  | n + 1 => Table Q V B O (Table Q V B O (Stage n))
variable (Q V B O) in
def step:∀ n,Stage Q V B O n → Stage Q V B O (n + 1)
  | 0 => PEmpty.elim
  | n + 1 => Table.relabel (Table.relabel (step n))
variable (b:B) (o:O)
include b o in
theorem step_injective (n:ℕ):Function.Injective (step Q V B O n):=by
  induction n with
  | zero => intro x; exact x.elim
  | succ n ih => exact Table.relabel_injective (Table.relabel_surjective ih b o)
variable (Q V B O) in
def inclusion (n m:ℕ) (h:n ≤ m):Stage Q V B O n → Stage Q V B O m :=
  Nat.leRecOn h (fun {k} => step Q V B O k)
@[simp] theorem inclusion_self (n:ℕ) (x:Stage Q V B O n) :
    inclusion Q V B O n n le_rfl x = x:=Nat.leRecOn_self x
@[simp] theorem inclusion_succ (n:ℕ) (x:Stage Q V B O n) :
    inclusion Q V B O n (n+1) (Nat.le_succ n) x = step Q V B O n x :=
  Nat.leRecOn_succ' x
theorem inclusion_trans {n m k:ℕ} (h:n ≤ m) (h':m ≤ k) (x:Stage Q V B O n) :
    inclusion Q V B O m k h' (inclusion Q V B O n m h x) =
      inclusion Q V B O n k (h.trans h') x:=(Nat.leRecOn_trans h h' x).symm
instance stageDirectedSystem:DirectedSystem (Stage Q V B O) (inclusion Q V B O · · ·) where
  map_self:=fun {_} x => inclusion_self _ x
  map_map:=fun {_ _ _} h h' x => inclusion_trans h h' x
include b o in
theorem inclusion_injective {n m:ℕ} (h:n ≤ m) :
    Function.Injective (inclusion Q V B O n m h):=by
  induction m,h using Nat.le_induction with
  | base => intro x y he; simpa only [inclusion_self] using he
  | succ m hm ih =>
    intro x y he
    simp only [inclusion,Nat.leRecOn_succ hm] at he
    exact ih (step_injective b o m he)
local instance functionFunLike (α β:Type u):FunLike (α → β) α β where
  coe:=fun f => f
  coe_injective:=fun _ _ h => h
local instance stageCoeDirectedSystem:DirectedSystem (Stage Q V B O)
    (fun i j h => @DFunLike.coe (Stage Q V B O i → Stage Q V B O j) _ _
      (functionFunLike _ _) (inclusion Q V B O i j h)):=stageDirectedSystem
variable (Q V B O) in
abbrev Minus:=DirectLimit (Stage Q V B O) (inclusion Q V B O)
variable (Q V B O) in
abbrev Plus:=Table Q V B O (Minus Q V B O)
variable (Q V B O) in
def embed (n:ℕ) (x:Stage Q V B O n):Minus Q V B O:=⟦⟨n,x⟩⟧
include b o in
theorem embed_injective (n:ℕ):Function.Injective (embed Q V B O n) :=
  DirectLimit.mk_injective _ (fun _ _ h => inclusion_injective b o h) n
@[simp] theorem embed_inclusion {n m:ℕ} (h:n ≤ m) (x:Stage Q V B O n) :
    embed Q V B O m (inclusion Q V B O n m h x) = embed Q V B O n x :=
  DirectLimit.mk_apply n m x h
@[simp] theorem embed_step (n:ℕ) (x:Stage Q V B O n) :
    embed Q V B O (n+1) (step Q V B O n x) = embed Q V B O n x:=by
  rw [← inclusion_succ]; exact embed_inclusion _ _
theorem exists_embed (x:Minus Q V B O):∃ n y,embed Q V B O n y = x:=by
  obtain ⟨n,y,rfl⟩:=DirectLimit.exists_eq_mk _ x
  exact ⟨n,y,rfl⟩
theorem exists_embed_succ (x:Minus Q V B O):∃ n y,embed Q V B O (n+1) y = x:=by
  obtain ⟨n,y,rfl⟩:=exists_embed x
  exact ⟨n,step Q V B O n y,embed_step n y⟩
variable (Q V B O) in
def restrict (n:ℕ):Plus Q V B O → Table Q V B O (Stage Q V B O n) :=
  Table.relabel (embed Q V B O n)
include b o in
theorem restrict_surjective (n:ℕ):Function.Surjective (restrict Q V B O n) :=
  Table.relabel_surjective (embed_injective b o n) b o
@[simp] theorem restrict_compat (n:ℕ) (p:Plus Q V B O) :
    Table.relabel (step Q V B O n) (restrict Q V B O (n+1) p) = restrict Q V B O n p:=by
  rw [restrict,Table.relabel_comp]
  congr 1
  funext x
  exact embed_step n x
theorem restrict_inclusion {n m:ℕ} (h:n ≤ m) (p:Plus Q V B O) :
    Table.relabel (inclusion Q V B O n m h) (restrict Q V B O m p) = restrict Q V B O n p:=by
  rw [restrict,Table.relabel_comp]
  congr 1
  funext x
  exact embed_inclusion h x
variable (Q V B O) in
def stageBehavior:∀ n,Stage Q V B O n → Table Q V B O (Plus Q V B O)
  | 0 => PEmpty.elim
  | n+1 => Table.relabel (restrict Q V B O n)
include b o in
theorem stageBehavior_injective (n:ℕ):Function.Injective (stageBehavior Q V B O n):=by
  cases n with
  | zero => intro x; exact x.elim
  | succ n => exact Table.relabel_injective (restrict_surjective b o n)
theorem stageBehavior_step (n:ℕ) (x:Stage Q V B O n) :
    stageBehavior Q V B O (n+1) (step Q V B O n x) = stageBehavior Q V B O n x:=by
  cases n with
  | zero => exact x.elim
  | succ n =>
    change Table.relabel _ (Table.relabel _ x) = _
    rw [Table.relabel_comp]
    congr 1
    funext p
    exact restrict_compat n p
theorem stageBehavior_inclusion {n m:ℕ} (h:n ≤ m) (x:Stage Q V B O n) :
    stageBehavior Q V B O m (inclusion Q V B O n m h x) = stageBehavior Q V B O n x:=by
  induction m,h using Nat.le_induction with
  | base => rw [inclusion_self]
  | succ m hm ih =>
    simp only [inclusion,Nat.leRecOn_succ hm,stageBehavior_step]
    exact ih
variable (Q V B O) in
def behavior:Minus Q V B O → Table Q V B O (Plus Q V B O) :=
  DirectLimit.lift (inclusion Q V B O) (stageBehavior Q V B O)
    (fun _ _ h x => (stageBehavior_inclusion h x).symm)
@[simp] theorem behavior_embed (n:ℕ) (x:Stage Q V B O n) :
    behavior Q V B O (embed Q V B O n x) = stageBehavior Q V B O n x:=rfl
include b o in
theorem behavior_injective:Function.Injective (behavior Q V B O) :=
  DirectLimit.lift_injective _ _ _ (stageBehavior_injective b o)
variable (Q V) in
def plusDefault (b:B) (o:O):Plus Q V B O:=Table.default b o
variable (Q V) in
def minusDefault (b:B) (o:O):Minus Q V B O :=
  embed Q V B O 1 (Table.default b o)
@[simp] theorem behavior_default :
    behavior Q V B O (minusDefault Q V b o) = Table.default b o:=rfl
theorem slice_range (x:Minus Q V B O) (a:Frame Q V (Plus Q V B O)) :
    ∃ y,behavior Q V B O y = (behavior Q V B O x).slice a:=by
  obtain ⟨n,x,rfl⟩:=exists_embed_succ x
  refine ⟨embed Q V B O (n+1) (x.slice (mapFrame (restrict Q V B O n) a)),?_⟩
  exact (Table.slice_relabel _ x a).symm
noncomputable def minusSlice (x:Minus Q V B O) (a:Frame Q V (Plus Q V B O)):Minus Q V B O :=
  (slice_range x a).choose
@[simp] theorem behavior_minusSlice (x:Minus Q V B O) (a:Frame Q V (Plus Q V B O)) :
    behavior Q V B O (minusSlice x a) = (behavior Q V B O x).slice a:=(slice_range x a).choose_spec
end FreeObs
end S_wpc_barendregt_geuvers_klop
namespace S_wpc_barendregt_geuvers_klop.PlainSpaces
universe u
structure Schema (N:Type u) where
  Key:N → Type u
  target:(n:N) → Key n → N
  domain:(n:N) → Key n → Option N
namespace Schema
variable {N:Type u} (F:Schema N)
inductive Path:N → Type u
  | nil (n:N):Path n
  | cons {n:N} (a:F.Key n) (p:Path (F.target n a)):Path n
inductive Slot:{n:N} → F.Path n → N → Type u
  | head {n:N} {a:F.Key n} {p:F.Path (F.target n a)} {d:N}
      (h:F.domain n a = some d):Slot (.cons a p) d
  | tail {n:N} {a:F.Key n} {p:F.Path (F.target n a)} {d:N}
      (s:Slot p d):Slot (.cons a p) d
inductive Dependency:N → N → Prop
  | head {n:N} (a:F.Key n) {d:N} (h:F.domain n a = some d):Dependency d n
  | tail {n d:N} (a:F.Key n) (h:Dependency d (F.target n a)):Dependency d n
namespace Slot
variable {F}
theorem dependency {n d:N} {p:F.Path n} (s:F.Slot p d):F.Dependency d n:=by
  induction s with
  | head h => exact .head _ h
  | tail s ih => exact .tail _ ih
end Slot
abbrev Params (K:N → Type u) {n:N} (p:F.Path n):Type u :=
  (d:N) → F.Slot p d → K d
abbrev FrameParams (K:N → Type u) {n:N} (a:F.Key n):Type u :=
  (d:N) → F.domain n a = some d → K d
abbrev Table (K:N → Type u) (B:Type u) (n:N):Type u :=
  (p:F.Path n) → F.Params K p → B
noncomputable def Space (hw:WellFounded F.Dependency) (B:Type u):N → Type u :=
  hw.fix fun n rec => (p:F.Path n) → ((d:N) → (s:F.Slot p d) → rec d s.dependency) → B
theorem space_eq (hw:WellFounded F.Dependency) (B:Type u) (n:N) :
    F.Space hw B n = F.Table (F.Space hw B) B n :=
  hw.fix_eq _ n
noncomputable def unfold (hw:WellFounded F.Dependency) (B:Type u) (n:N) :
    F.Space hw B n ≃ F.Table (F.Space hw B) B n :=
  Equiv.cast (F.space_eq hw B n)
namespace Params
variable {F} {K:N → Type u} {n:N}
def nil:F.Params K (.nil n):=fun _ s => nomatch s
def head {a:F.Key n} {p:F.Path (F.target n a)}
    (xs:F.Params K (.cons a p)):F.FrameParams K a :=
  fun _ h => xs _ (.head h)
def tail {a:F.Key n} {p:F.Path (F.target n a)}
    (xs:F.Params K (.cons a p)):F.Params K p :=
  fun _ h => xs _ (.tail h)
def cons {a:F.Key n} {p:F.Path (F.target n a)}
    (x:F.FrameParams K a) (xs:F.Params K p):F.Params K (.cons a p)
  | _,.head h => x _ h
  | _,.tail s => xs _ s
@[simp] theorem head_cons {a:F.Key n} {p:F.Path (F.target n a)}
    (x:F.FrameParams K a) (xs:F.Params K p):(cons x xs).head = x:=rfl
@[simp] theorem tail_cons {a:F.Key n} {p:F.Path (F.target n a)}
    (x:F.FrameParams K a) (xs:F.Params K p):(cons x xs).tail = xs:=rfl
@[simp] theorem cons_head_tail {a:F.Key n} {p:F.Path (F.target n a)}
    (xs:F.Params K (.cons a p)):cons xs.head xs.tail = xs:=by
  funext d s
  cases s <;> rfl
theorem nil_unique (xs:F.Params K (.nil n)):xs = nil:=by
  funext d s
  cases s
end Params
noncomputable def prefixEquiv (hw:WellFounded F.Dependency) (B:Type u) (n:N) :
    F.Space hw B n ≃ B × ((a:F.Key n) → F.FrameParams (F.Space hw B) a →
      F.Space hw B (F.target n a)) where
  toFun t :=
    ⟨F.unfold hw B n t (.nil n) Params.nil,
     fun a x => (F.unfold hw B (F.target n a)).symm
       (fun p xs => F.unfold hw B n t (.cons a p) (Params.cons x xs))⟩
  invFun t:=(F.unfold hw B n).symm (fun p xs => match p with
    | .nil _ => t.1
    | .cons a p => F.unfold hw B (F.target n a) (t.2 a xs.head) p xs.tail)
  left_inv t:=by
    apply (F.unfold hw B n).injective
    simp only [Equiv.apply_symm_apply]
    funext p xs
    cases p with
    | nil n => rw [Params.nil_unique xs]
    | cons a p => simp only [Params.cons_head_tail]
  right_inv t:=by
    apply Prod.ext
    · simp only [Equiv.apply_symm_apply]
    · funext a x
      apply (F.unfold hw B (F.target n a)).injective
      simp only [Equiv.apply_symm_apply]
      funext p xs
      rfl
noncomputable def distinguished (hw:WellFounded F.Dependency) {B:Type u} (b:B) (n:N) :
    F.Space hw B n:=(F.unfold hw B n).symm (fun _ _ => b)
@[simp] theorem distinguished_base (hw:WellFounded F.Dependency) {B:Type u}
    (b:B) (n:N):(F.prefixEquiv hw B n (F.distinguished hw b n)).1 = b:=by
  simp only [prefixEquiv,distinguished,Equiv.coe_fn_mk,Equiv.apply_symm_apply]
@[simp] theorem distinguished_next (hw:WellFounded F.Dependency) {B:Type u}
    (b:B) (n:N) (a:F.Key n) (x:F.FrameParams (F.Space hw B) a) :
    (F.prefixEquiv hw B n (F.distinguished hw b n)).2 a x =
      F.distinguished hw b (F.target n a):=by
  simp only [prefixEquiv,distinguished,Equiv.coe_fn_mk,Equiv.apply_symm_apply]
end Schema
end S_wpc_barendregt_geuvers_klop.PlainSpaces
namespace S_wpc_barendregt_geuvers_klop.FreeObs
universe u
variable {Q V B O:Type u}
def InStage (n:ℕ) (x:Minus Q V B O):Prop :=
  ∃ y:Stage Q V B O n,embed Q V B O n y = x
def Agree (n:ℕ) (p q:Plus Q V B O):Prop :=
  restrict Q V B O n p = restrict Q V B O n q
namespace InStage
theorem mono {n m:ℕ} (h:n ≤ m) {x:Minus Q V B O} (hx:InStage n x) :
    InStage m x:=by
  obtain ⟨y,rfl⟩:=hx
  exact ⟨inclusion Q V B O n m h y,embed_inclusion h y⟩
theorem not_zero (x:Minus Q V B O):¬ InStage 0 x:=by
  rintro ⟨a,_⟩
  exact a.elim
theorem exists_stage (x:Minus Q V B O):∃ n,InStage n x :=
  exists_embed x
end InStage
namespace Agree
theorem mono {n m:ℕ} (h:n ≤ m) {p q:Plus Q V B O} (hpq:Agree m p q) :
    Agree n p q:=by
  unfold Agree at *
  rw [← restrict_inclusion h p,← restrict_inclusion h q,hpq]
theorem refl (n:ℕ) (p:Plus Q V B O):Agree n p p:=rfl
theorem symm {n:ℕ} {p q:Plus Q V B O} (h:Agree n p q):Agree n q p:=Eq.symm h
theorem trans {n:ℕ} {p q r:Plus Q V B O}
    (h:Agree n p q) (h':Agree n q r):Agree n p r:=Eq.trans h h'
end Agree
theorem inStage_succ_iff (b:B) (o:O) (n:ℕ) (x:Minus Q V B O) :
    InStage (n+1) x ↔
      (∀ a a',mapContinue (restrict Q V B O n) a = mapContinue (restrict Q V B O n) a' →
          (behavior Q V B O x).continuing a = (behavior Q V B O x).continuing a') ∧
      (∀ a a',mapExit (restrict Q V B O n) a = mapExit (restrict Q V B O n) a' →
          (behavior Q V B O x).exiting a = (behavior Q V B O x).exiting a'):=by
  constructor
  · rintro ⟨y,rfl⟩
    exact (Table.relabel_range_iff (restrict_surjective b o n) _).mp ⟨y,rfl⟩
  · intro h
    obtain ⟨y,hy⟩:=(Table.relabel_range_iff (restrict_surjective b o n) _).mpr h
    exact ⟨y,behavior_injective b o (by exact hy)⟩
theorem exists_inStage_behavior (b:B) (o:O) (n:ℕ)
    (t:Table Q V B O (Plus Q V B O))
    (hc:∀ a a',mapContinue (restrict Q V B O n) a = mapContinue (restrict Q V B O n) a' →
      t.continuing a = t.continuing a')
    (he:∀ a a',mapExit (restrict Q V B O n) a = mapExit (restrict Q V B O n) a' →
      t.exiting a = t.exiting a') :
    ∃ x,InStage (n+1) x ∧ behavior Q V B O x = t:=by
  obtain ⟨y,hy⟩:=(Table.relabel_range_iff (restrict_surjective b o n) t).mpr ⟨hc,he⟩
  exact ⟨embed Q V B O (n+1) y,⟨y,rfl⟩,hy⟩
theorem inStage_minusSlice (b:B) (o:O) {n:ℕ} {x:Minus Q V B O} (hx:InStage n x)
    (a:Frame Q V (Plus Q V B O)):InStage n (minusSlice x a):=by
  cases n with
  | zero => exact False.elim (InStage.not_zero x hx)
  | succ n =>
      obtain ⟨y,rfl⟩:=hx
      refine ⟨y.slice (mapFrame (restrict Q V B O n) a),?_⟩
      apply behavior_injective b o
      rw [behavior_minusSlice]
      exact (Table.slice_relabel _ y a).symm
def lambdaTable (base:B)
    (body:Frame Q V (Plus Q V B O) → Minus Q V B O)
    (exit:Frame Q V (Plus Q V B O) → O):Table Q V B O (Plus Q V B O) where
  continuing
    | [] => base
    | a :: as => (behavior Q V B O (body a)).continuing as
  exiting
    | ([],a) => exit a
    | (a :: as,e) => (behavior Q V B O (body a)).exiting (as,e)
theorem lambdaTable_representable (b:B) (o:O) (n:ℕ) (base:B)
    (body:Frame Q V (Plus Q V B O) → Minus Q V B O)
    (exit:Frame Q V (Plus Q V B O) → O)
    (hb:∀ a,InStage (n+1) (body a))
    (hc:∀ a a',mapFrame (restrict Q V B O n) a = mapFrame (restrict Q V B O n) a' →
      body a = body a')
    (he:∀ a a',mapFrame (restrict Q V B O n) a = mapFrame (restrict Q V B O n) a' →
      exit a = exit a') :
    ∃ x,InStage (n+1) x ∧ behavior Q V B O x = lambdaTable base body exit:=by
  apply exists_inStage_behavior b o n
  · intro as as' ha
    cases as with
    | nil =>
        cases as' with
        | nil => rfl
        | cons a as' => cases ha
    | cons a as =>
        cases as' with
        | nil => cases ha
        | cons a' as' =>
            have hh:=List.cons.inj ha
            change (behavior Q V B O (body a)).continuing as =
              (behavior Q V B O (body a')).continuing as'
            rw [← hc a a' hh.1]
            exact ((inStage_succ_iff b o n (body a)).mp (hb a)).1 as as' hh.2
  · rintro ⟨as,e⟩ ⟨as',e'⟩ ha
    have hh:=Prod.mk.inj ha
    cases as with
    | nil =>
        cases as' with
        | nil => exact he e e' hh.2
        | cons a as' => cases hh.1
    | cons a as =>
        cases as' with
        | nil => cases hh.1
        | cons a' as' =>
            have hs:=List.cons.inj hh.1
            change (behavior Q V B O (body a)).exiting (as,e) =
              (behavior Q V B O (body a')).exiting (as',e')
            rw [← hc a a' hs.1]
            apply ((inStage_succ_iff b o n (body a)).mp (hb a)).2
            exact Prod.ext hs.2 hh.2
def FrameBound (n:Nat) (a:Frame Q V (Minus Q V B O)):Prop :=
  ∀ x,a.2 = .opposite x → InStage n x
def ContinueBound (n:Nat) (as:ContinueStack Q V (Minus Q V B O)):Prop :=
  ∀ a ∈ as,FrameBound n a
def ExitBound (n:Nat) (a:ExitStack Q V (Minus Q V B O)):Prop :=
  ContinueBound n a.1 ∧ FrameBound n a.2
namespace FrameBound
variable {n m:Nat} {a:Frame Q V (Minus Q V B O)}
theorem mono (h:n ≤ m) (ha:FrameBound n a):FrameBound m a :=
  fun x hx => (ha x hx).mono h
theorem exists_preimage (ha:FrameBound n a) :
    ∃ a':Frame Q V (Stage Q V B O n),mapFrame (embed Q V B O n) a' = a:=by
  rcases a with ⟨q,p⟩
  cases p with
  | none => exact ⟨(q,.none),rfl⟩
  | plain v => exact ⟨(q,.plain v),rfl⟩
  | opposite x =>
      obtain ⟨y,hy⟩:=ha x rfl
      exact ⟨(q,.opposite y),congrArg (fun x => (q,Payload.opposite x)) hy⟩
theorem embed (n:Nat) (a:Frame Q V (Stage Q V B O n)) :
    FrameBound n (mapFrame (FreeObs.embed Q V B O n) a):=by
  rcases a with ⟨q,p⟩
  cases p with
  | none => intro x h; cases h
  | plain v => intro x h; cases h
  | opposite x =>
      intro y hy
      have he:FreeObs.embed Q V B O n x = y:=Payload.opposite.inj hy
      exact ⟨x,he⟩
end FrameBound
namespace ContinueBound
variable {n m:Nat} {as:ContinueStack Q V (Minus Q V B O)}
theorem mono (h:n ≤ m) (ha:ContinueBound n as):ContinueBound m as :=
  fun a hm => (ha a hm).mono h
theorem exists_preimage (ha:ContinueBound n as) :
    ∃ as':ContinueStack Q V (Stage Q V B O n),mapContinue (embed Q V B O n) as' = as:=by
  induction as with
  | nil => exact ⟨[],rfl⟩
  | cons a as ih =>
      obtain ⟨a',ha'⟩:=(ha a (List.mem_cons_self)).exists_preimage
      obtain ⟨as',has'⟩:=ih (fun a h => ha a (List.mem_cons_of_mem _ h))
      exact ⟨a' :: as',congrArg₂ List.cons ha' has'⟩
theorem embed (n:Nat) (as:ContinueStack Q V (Stage Q V B O n)) :
    ContinueBound n (mapContinue (FreeObs.embed Q V B O n) as):=by
  intro a ha
  obtain ⟨x,hx,rfl⟩:=List.mem_map.mp ha
  exact FrameBound.embed n x
theorem cons (a:Frame Q V (Minus Q V B O)) (ha:FrameBound n a)
    (has:ContinueBound n as):ContinueBound n (a :: as):=by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ha
  · exact has x hx
end ContinueBound
namespace Agree
variable {n m:Nat} {p q:Plus Q V B O}
theorem continuing (h:Agree n p q) {as:ContinueStack Q V (Minus Q V B O)}
    (ha:ContinueBound n as):p.continuing as = q.continuing as:=by
  obtain ⟨as',rfl⟩:=ha.exists_preimage
  exact congrArg (fun t:Table Q V B O (Stage Q V B O n) => t.continuing as') h
theorem exiting (h:Agree n p q) {as:ExitStack Q V (Minus Q V B O)}
    (ha:ExitBound n as):p.exiting as = q.exiting as:=by
  obtain ⟨as',has'⟩:=ha.1.exists_preimage
  obtain ⟨a',ha'⟩:=ha.2.exists_preimage
  have hh:=congrArg (fun t:Table Q V B O (Stage Q V B O n) => t.exiting (as',a')) h
  change p.exiting (mapContinue _ as',mapFrame _ a') = q.exiting (mapContinue _ as',mapFrame _ a') at hh
  simpa only [has',ha'] using hh
theorem of_observations
    (hc:∀ as,ContinueBound n as → p.continuing as = q.continuing as)
    (he:∀ as,ExitBound n as → p.exiting as = q.exiting as):Agree n p q:=by
  apply Table.ext
  · funext as
    exact hc _ (ContinueBound.embed n as)
  · funext as
    exact he _ ⟨ContinueBound.embed n as.1,FrameBound.embed n as.2⟩
theorem slice (h:Agree n p q) (hmn:m ≤ n)
    (a:Frame Q V (Minus Q V B O)) (ha:FrameBound n a):Agree m (p.slice a) (q.slice a):=by
  apply of_observations
  · intro as has
    exact h.continuing (ContinueBound.cons a ha (has.mono hmn))
  · intro as has
    exact h.exiting ⟨ContinueBound.cons a ha (has.1.mono hmn),has.2.mono hmn⟩
theorem all_levels_eq (h:∀ n,Agree n p q):p = q:=by
  have bound_frame (a:Frame Q V (Minus Q V B O)):∃ n,FrameBound n a:=by
    rcases a with ⟨key,payload⟩
    cases payload with
    | none => exact ⟨0,fun _ hh => by cases hh⟩
    | plain v => exact ⟨0,fun _ hh => by cases hh⟩
    | opposite x =>
        obtain ⟨n,hn⟩:=InStage.exists_stage x
        exact ⟨n,fun y hy => Payload.opposite.inj hy ▸ hn⟩
  have bound_stack (as:ContinueStack Q V (Minus Q V B O)):∃ n,ContinueBound n as:=by
    induction as with
    | nil => exact ⟨0,fun _ hh => by cases hh⟩
    | cons a as ih =>
        obtain ⟨n,hn⟩:=bound_frame a
        obtain ⟨m,hm⟩:=ih
        exact ⟨max n m,ContinueBound.cons a (hn.mono (le_max_left _ _)) (hm.mono (le_max_right _ _))⟩
  apply Table.ext
  · funext as
    obtain ⟨n,hn⟩:=bound_stack as
    exact (h n).continuing hn
  · funext as
    obtain ⟨n,hn⟩:=bound_stack as.1
    obtain ⟨m,hm⟩:=bound_frame as.2
    exact (h (max n m)).exiting ⟨hn.mono (le_max_left _ _),hm.mono (le_max_right _ _)⟩
end Agree
variable (b:B) (o:O)
include b o
theorem minusSlice_eq_of_restrict {n:Nat} {x:Minus Q V B O} (hx:InStage (n+1) x)
    {a a':Frame Q V (Plus Q V B O)}
    (ha:mapFrame (restrict Q V B O n) a = mapFrame (restrict Q V B O n) a') :
    minusSlice x a = minusSlice x a':=by
  apply behavior_injective b o
  rw [behavior_minusSlice,behavior_minusSlice]
  apply Table.ext
  · funext as
    apply ((inStage_succ_iff b o n x).mp hx).1
    exact congrArg (fun a => a :: mapContinue (restrict Q V B O n) as) ha
  · funext as
    apply ((inStage_succ_iff b o n x).mp hx).2
    exact Prod.ext (congrArg (fun a => a :: mapContinue (restrict Q V B O n) as.1) ha) rfl
theorem minusExit_eq_of_restrict {n:Nat} {x:Minus Q V B O} (hx:InStage (n+1) x)
    {a a':Frame Q V (Plus Q V B O)}
    (ha:mapFrame (restrict Q V B O n) a = mapFrame (restrict Q V B O n) a') :
    (behavior Q V B O x).exiting ([],a) = (behavior Q V B O x).exiting ([],a'):=by
  apply ((inStage_succ_iff b o n x).mp hx).2
  exact Prod.ext rfl ha
omit b o
def plusLambdaTable (base:B) (body:Frame Q V (Minus Q V B O) → Plus Q V B O)
    (exit:Frame Q V (Minus Q V B O) → O):Plus Q V B O where
  continuing
    | [] => base
    | a :: as => (body a).continuing as
  exiting
    | ([],a) => exit a
    | (a :: as,e) => (body a).exiting (as,e)
end S_wpc_barendregt_geuvers_klop.FreeObs
end OMA
namespace OMA
namespace S_wpc_barendregt_geuvers_klop
universe u
namespace ActPlain
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P)
variable (C:Set (Set S))
structure Node where
  type:Expr S
  normal:Normal type
  sorted:∃ s,Ω.HasType type (.sort s)
  plain:PlainL P C (Ω.profile type)
structure Key (T:Node Ω C) where
  domain:Expr S
  body:Expr S
  product:T.type = .pi domain body
  argument:Expr S
  normal:Normal argument
  typed:Ω.HasType argument domain
  active:ActL P C (Ω.profile (body.instantiate argument))
variable {Ω C}
variable (hw:SystemWeaklyNormalizing P)
namespace Key
variable {T:Node Ω C} (a:Key Ω C T)
theorem sorted:∃ s,Ω.HasType (.pi a.domain a.body) (.sort s):=by
  simpa only [← a.product] using T.sorted
include hw
theorem target_reach:Reach (SecEdge P C)
    (Ω.profile (a.body.instantiate a.argument)) (Ω.profile T.type):=by
  obtain ⟨s,hs⟩:=a.sorted
  obtain ⟨J,hj,hp⟩:=Ω.frame_profiles hw hs a.typed
  have hJ:=ObsLayers.positive a.active.layer hp
  exact (ObsLayers.secondary a.active.layer hp).reach.trans (.single (.positive hJ T.plain.active.layer
    (a.product ▸ PriEdge.codomain hj)))
theorem open_active:∃ J,ProfileTriple P (Ω.profile a.domain) J (Ω.profile T.type) ∧
    ActL P C J:=by
  obtain ⟨s,hs⟩:=a.sorted
  obtain ⟨J,hj,hp⟩:=Ω.frame_profiles hw hs a.typed
  have hJ:=ObsLayers.positive a.active.layer hp
  have he:SecEdge P C J (Ω.profile T.type) false :=
    .positive hJ T.plain.active.layer (a.product ▸ PriEdge.codomain hj)
  exact ⟨J,a.product ▸ hj,T.plain.active.predecessor (.single he)⟩
theorem domain_edge (ha:ActL P C (Ω.profile a.domain)) :
    SecEdge P C (Ω.profile a.domain) (Ω.profile T.type) true:=by
  obtain ⟨J,hj,hJ⟩:=a.open_active hw
  exact .negative ha.layer hJ.layer T.plain.active.layer hj
noncomputable def target:Node Ω C where
  type:=(a.body.instantiate a.argument).nfTerm
  normal:=by
    obtain ⟨s,hs⟩:=a.sorted
    obtain ⟨b,hb⟩:=Ω.frame_target_sorted hs a.typed
    exact (Expr.nfTerm_spec (hb.weakNorm hw)).2
  sorted:=by
    obtain ⟨s,hs⟩:=a.sorted
    obtain ⟨b,hb⟩:=Ω.frame_target_sorted hs a.typed
    exact ⟨b,hb.nfTerm hw⟩
  plain:=by
    rw [Ω.profile_nfTerm]
    exact T.plain.predecessor_path (a.target_reach hw)
noncomputable def domainNode (ha:ActL P C (Ω.profile a.domain)):Node Ω C where
  type:=a.domain
  normal:=by
    have hh:=T.normal
    rw [a.product] at hh
    exact hh.pi_domain
  sorted:=by
    obtain ⟨s,hs⟩:=a.sorted
    exact Ω.domain_sorted hs
  plain:=T.plain.predecessor (a.domain_edge hw ha)
@[simp] theorem target_profile:Ω.profile (a.target hw).type =
    Ω.profile (a.body.instantiate a.argument):=Ω.profile_nfTerm _
@[simp] theorem domainNode_type (ha:ActL P C (Ω.profile a.domain)) :
    (a.domainNode hw ha).type = a.domain:=rfl
end Key
noncomputable def schema:PlainSpaces.Schema (Node Ω C) where
  Key:=Key Ω C
  target:=fun _ a => a.target hw
  domain:=fun _ a => if ha:ActL P C (Ω.profile a.domain)
    then some (a.domainNode hw ha) else none
variable {hw}
namespace Schema
theorem target_reach {n:Node Ω C} (a:(schema hw).Key n) :
    Reach (SecEdge P C) (Ω.profile ((schema hw).target n a).type) (Ω.profile n.type):=by
  simpa only [schema,Key.target,CTower.profile_nfTerm] using a.target_reach hw
theorem domain_eq {n d:Node Ω C} {a:(schema hw).Key n}
    (he:(schema hw).domain n a = some d) :
    ∃ ha:ActL P C (Ω.profile a.domain),d = a.domainNode hw ha:=by
  change (if ha:ActL P C (Ω.profile a.domain) then some (a.domainNode hw ha) else none) = some d at he
  split at he
  · rename_i ha
    exact ⟨ha,(Option.some.inj he).symm⟩
  · cases he
theorem dependency_path {n d:Node Ω C} (hd:(schema hw).Dependency d n) :
    ∃ I K,SecEdge P C I K true ∧ Reach (SecEdge P C) (Ω.profile d.type) I ∧
      Reach (SecEdge P C) K (Ω.profile n.type):=by
  induction hd with
  | @head n a d he =>
    obtain ⟨ha,rfl⟩:=domain_eq he
    exact ⟨Ω.profile a.domain,Ω.profile n.type,a.domain_edge hw ha,.refl _,.refl _⟩
  | @tail n d a hd ih =>
    obtain ⟨I,K,he,hi,hk⟩:=ih
    exact ⟨I,K,he,hi,hk.trans (target_reach a)⟩
theorem dependency_reach {n d:Node Ω C} (hd:(schema hw).Dependency d n) :
    Reach (SecEdge P C) (Ω.profile d.type) (Ω.profile n.type):=by
  obtain ⟨I,K,he,hi,hk⟩:=dependency_path hd
  exact hi.trans ((Reach.single he).trans hk)
theorem dependency_negative {n d:Node Ω C} (hd:(schema hw).Dependency d n)
    {D:Set (Set S)} (hD:IsComp (SecEdge P C) D)
    (hn:Ω.profile n.type ∈ D) (hd':Ω.profile d.type ∈ D) :
    ∃ I ∈ D,∃ K ∈ D,SecEdge P C I K true:=by
  obtain ⟨I,K,he,hi,hk⟩:=dependency_path hd
  exact ⟨I,hD.between hd' hn hi ((Reach.single he).trans hk),K,
    hD.between hd' hn (hi.trans (.single he)) hk,he⟩
variable (hw)
theorem dependency_drop (hno:¬ ForbiddenConfiguration P C)
    {n d:Node Ω C} (hd:(schema hw).Dependency d n)
    {D:Set (Set S)} (hD:IsComp (SecEdge P C) D)
    (hplain:∀ I ∈ D,PlainL P C I)
    (hn:Ω.profile n.type ∈ D) (hd':Ω.profile d.type ∈ D) :
    Ω.potential C D d.type < Ω.potential C D n.type:=by
  induction hd with
  | @head n a d he =>
    obtain ⟨ha,rfl⟩:=domain_eq he
    obtain ⟨s,hs⟩:=a.sorted
    have hh:=Ω.frame_domain_drop hw hs a.typed
      (a.product ▸ n.plain.active) a.active hd'
    simpa only [Key.domainNode,← a.product] using hh
  | @tail n d a hd ih =>
    have htarget:Ω.profile ((schema hw).target n a).type ∈ D :=
      hD.between hd' hn (dependency_reach hd) (target_reach a)
    have hneg:=dependency_negative hd hD htarget hd'
    have hh:=ih htarget hd'
    obtain ⟨s,hs⟩:=a.sorted
    have hnN:Normal (.pi a.domain a.body):=a.product ▸ n.normal
    have hdrop:=Ω.frame_target_drop hw hno hD hplain hneg hs hnN a.typed
      (a.product ▸ hn) (by simpa only [schema,Key.target,CTower.profile_nfTerm] using htarget)
    exact hh.trans (by simpa only [schema,Key.target,← a.product] using hdrop)
end Schema
variable [Fintype S]
noncomputable def measure (n:Node Ω C):Nat × Nat :=
  (Reach.rank (SecEdge P C) (Ω.profile n.type),
   Ω.potential C (Reach.component (SecEdge P C) (Ω.profile n.type)) n.type)
theorem dependency_wellFounded (hno:¬ ForbiddenConfiguration P C) :
    WellFounded (schema (Ω:=Ω) (C:=C) hw).Dependency:=by
  apply ((Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.onFun (f:=measure (Ω:=Ω) (C:=C))).mono
  intro d n hd
  have hr:=Schema.dependency_reach hd
  have hle:=Reach.rank_mono (SecEdge P C) hr
  change Prod.Lex (· < ·) (· < ·)
    (Reach.rank (SecEdge P C) (Ω.profile d.type),
      Ω.potential C (Reach.component (SecEdge P C) (Ω.profile d.type)) d.type)
    (Reach.rank (SecEdge P C) (Ω.profile n.type),
      Ω.potential C (Reach.component (SecEdge P C) (Ω.profile n.type)) n.type)
  rcases lt_or_eq_of_le hle with hlt | he
  · exact .left _ _ hlt
  · have hc:=Reach.component_eq_of_rank_eq (SecEdge P C) hr he
    have hdn:Ω.profile d.type ∈ Reach.component (SecEdge P C) (Ω.profile n.type) :=
      ⟨Reach.reverse_of_rank_eq (SecEdge P C) hr he,hr⟩
    have hdrop:=Schema.dependency_drop hw hno hd
      (Reach.component_isComponent (SecEdge P C) (Ω.profile n.type))
      n.plain.component_plain (Reach.mem_component _ _) hdn
    rw [he,hc]
    exact .right _ hdrop
noncomputable def Space (hno:¬ ForbiddenConfiguration P C) (B:Type u)
    (n:Node Ω C):Type u :=
  (schema hw).Space (dependency_wellFounded hno) B n
noncomputable def prefixEquiv (hno:¬ ForbiddenConfiguration P C) (B:Type u)
    (n:Node Ω C):Space (hw:=hw) hno B n ≃
      B × ((a:(schema hw).Key n) →
        (schema hw).FrameParams (Space (hw:=hw) hno B) a →
        Space (hw:=hw) hno B ((schema hw).target n a)) :=
  (schema hw).prefixEquiv (dependency_wellFounded hno) B n
end ActPlain
end S_wpc_barendregt_geuvers_klop
end OMA
namespace OMA
namespace S_wpc_barendregt_geuvers_klop
universe u
namespace PriEdge
variable {S:Type u} {P:Specification S} {I J:Set S} {b:Bool}
theorem target_feasible (h:PriEdge P I J b):FeasibleProfile P J:=by
  cases h with
  | inclusion _ h _ => exact h
  | domain h => exact h.product
  | codomain h => exact h.product
end PriEdge
namespace ObsLayers
variable {S:Type u} {P:Specification S} {C:Set (Set S)} {I:Set S}
theorem nonempty (h:I ∈ ObsLayers P C):I.Nonempty:=by
  obtain ⟨s,hs,hn,hp⟩:=h
  cases hp with
  | refl => exact hn
  | tail _ he => exact he.target_feasible.1
end ObsLayers
namespace ActL
variable {S:Type u} {P:Specification S} {C:Set (Set S)} {I:Set S}
theorem nonempty (h:ActL P C I):I.Nonempty:=ObsLayers.nonempty h.layer
theorem classify (h:ActL P C I) :
    PlainL P C I ∨ FreeL P C I false ∨ FreeL P C I true:=by
  classical
  by_cases hp:PlainL P C I
  · exact .inl hp
  · obtain ⟨D,hd,b,hb⟩:=h
    cases b with
    | false => exact .inr (.inl ⟨hp,D,hd,hb⟩)
    | true => exact .inr (.inr ⟨hp,D,hd,hb⟩)
end ActL
namespace ObsVals
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P)
abbrev Candidate (T:Expr S):={A:Set (Expr S) // Cands.IsCandidate Ω T A}
abbrev ActualType:={T:Expr S // Cands.ActualType Ω T}
abbrev Base:=(T:ActualType Ω) → Candidate Ω T.val
def topBase:Base Ω:=fun T => ⟨Cands.Top Ω T.val,Cands.top_candidate⟩
noncomputable def Base.update (b:Base Ω) (T:ActualType Ω) (A:Candidate Ω T.val):Base Ω :=
  Function.update b T A
@[simp] theorem Base.update_same (b:Base Ω) (T:ActualType Ω) (A:Candidate Ω T.val) :
    Base.update Ω b T A T = A:=by simp [Base.update]
@[simp] theorem Base.update_other (b:Base Ω) (T U:ActualType Ω) (A:Candidate Ω T.val)
    (h:U ≠ T):Base.update Ω b T A U = b U:=by simp [Base.update,h]
variable [Fintype S] (C:Set (Set S)) {hw:SystemWeaklyNormalizing P}
variable (hno:¬ ForbiddenConfiguration P C)
abbrev PlainValue:=(T:ActPlain.Node Ω C) × ActPlain.Space (hw:=hw) hno (Base Ω) T
abbrev Plus:=FreeObs.Plus (Expr S) (PlainValue (hw:=hw) Ω C hno) (Base Ω) (Option (PlainValue (hw:=hw) Ω C hno))
abbrev Minus:=FreeObs.Minus (Expr S) (PlainValue (hw:=hw) Ω C hno) (Base Ω) (Option (PlainValue (hw:=hw) Ω C hno))
inductive RawValue:Type u
  | plain:PlainValue (hw:=hw) Ω C hno → RawValue
  | plus:Plus (hw:=hw) Ω C hno → RawValue
  | minus:Minus (hw:=hw) Ω C hno → RawValue
def Fits (T:Expr S):RawValue (hw:=hw) Ω C hno → Prop
  | .plain x => x.1.type = T
  | .plus _ => FreeL P C (Ω.profile T) false
  | .minus _ => FreeL P C (Ω.profile T) true
abbrev Value (T:Expr S):={v:RawValue (hw:=hw) Ω C hno // Fits (hw:=hw) Ω C hno T v}
structure ActTy where
  type:Expr S
  normal:Normal type
  sorted:∃ s,Ω.HasType type (.sort s)
  active:ActL P C (Ω.profile type)
namespace ActTy
variable {Ω C hno}
noncomputable abbrev ofActual (T:ActualType Ω) (ha:ActL P C (Ω.profile T.val)) :
    ActTy Ω C where
  type:=T.val
  normal:=by rcases T.property with h | ⟨s,h⟩; exact h.1; exact h ▸ Normal.sort s
  sorted:=by
    obtain ⟨s,hs⟩:=ha.nonempty
    have hn:Normal T.val:=by
      rcases T.property with h | ⟨s,h⟩; exact h.1; exact h ▸ Normal.sort s
    exact ⟨s,by simpa only [CTower.profile,Set.mem_ofPred_eq,
      Expr.nfTerm_of_normal hn] using hs⟩
  active:=ha
def actual (T:ActTy Ω C):ActualType Ω:=⟨T.type,.inl ⟨T.normal,T.sorted⟩⟩
end ActTy
noncomputable def plainDefault (T:ActPlain.Node Ω C):ActPlain.Space (hw:=hw) hno (Base Ω) T :=
  (ActPlain.schema hw).distinguished (ActPlain.dependency_wellFounded hno) (topBase Ω) T
noncomputable def distinguished (T:ActTy Ω C):Value (hw:=hw) Ω C hno T.type:=by
  by_cases hp:PlainL P C (Ω.profile T.type)
  · let n:ActPlain.Node Ω C:=⟨T.type,T.normal,T.sorted,hp⟩
    exact ⟨.plain ⟨n,plainDefault (hw:=hw) Ω C hno n⟩,rfl⟩
  · by_cases hf:FreeL P C (Ω.profile T.type) false
    · exact ⟨.plus (FreeObs.plusDefault _ _ (topBase Ω) none),hf⟩
    · have hm:FreeL P C (Ω.profile T.type) true:=by
        rcases T.active.classify with h | h | h
        · exact False.elim (hp h)
        · exact False.elim (hf h)
        · exact h
      exact ⟨.minus (FreeObs.minusDefault _ _ (topBase Ω) none),hm⟩
noncomputable def RawValue.base:RawValue (hw:=hw) Ω C hno → Base Ω
  | .plain p => (ActPlain.prefixEquiv hno (Base Ω) p.1 p.2).1
  | .plus p => p.continuing []
  | .minus m => (FreeObs.behavior _ _ _ _ m).continuing []
noncomputable def withBase (T:ActTy Ω C) (b:Base Ω):Value (hw:=hw) Ω C hno T.type:=by
  by_cases hp:PlainL P C (Ω.profile T.type)
  · let n:ActPlain.Node Ω C:=⟨T.type,T.normal,T.sorted,hp⟩
    let e:=ActPlain.prefixEquiv (hw:=hw) hno (Base Ω) n
    exact ⟨.plain ⟨n,e.symm (b,(e (plainDefault (hw:=hw) Ω C hno n)).2)⟩,rfl⟩
  · by_cases hf:FreeL P C (Ω.profile T.type) false
    · exact ⟨.plus ⟨(fun s => if s = [] then b else topBase Ω),fun _ => none⟩,hf⟩
    · have hm:FreeL P C (Ω.profile T.type) true:=by
        rcases T.active.classify with h | h | h
        · exact False.elim (hp h)
        · exact False.elim (hf h)
        · exact h
      exact ⟨.minus (FreeObs.embed _ _ _ _ 1
        ⟨(fun s => if s = [] then b else topBase Ω),fun _ => none⟩),hm⟩
theorem withBase_base (T:ActTy Ω C) (b:Base Ω) :
    RawValue.base (hw:=hw) Ω C hno (withBase (hw:=hw) Ω C hno T b).val = b:=by
  unfold withBase
  split
  · simp only [RawValue.base,Equiv.apply_symm_apply]
  · split
    · simp only [RawValue.base,↓reduceIte]
    · simp only [RawValue.base,FreeObs.behavior_embed,FreeObs.stageBehavior,
        FreeObs.Table.relabel,Function.comp_apply,FreeObs.mapContinue,
        List.map_nil,↓reduceIte]
noncomputable def project (T:ActTy Ω C) (v:RawValue (hw:=hw) Ω C hno):Value (hw:=hw) Ω C hno T.type :=
  if h:Fits (hw:=hw) Ω C hno T.type v then ⟨v,h⟩ else distinguished (hw:=hw) Ω C hno T
@[simp] theorem project_valid (T:ActTy Ω C) (v:Value (hw:=hw) Ω C hno T.type) :
    project (hw:=hw) Ω C hno T v.val = v:=by
  simp only [project,v.property,dite_true,Subtype.coe_eta]
end ObsVals
end S_wpc_barendregt_geuvers_klop
namespace S_wpc_barendregt_geuvers_klop.ObsVals
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
namespace RawValue
def LevelEq (n:Nat):RawValue (hw:=hw) Ω C hno → RawValue (hw:=hw) Ω C hno → Prop
  | .plain p,.plain q => p = q
  | .plus p,.plus q => FreeObs.Agree n p q
  | .minus p,.minus q => p = q
  | _,_ => False
def Bounded (n:Nat):RawValue (hw:=hw) Ω C hno → Prop
  | .minus p => FreeObs.InStage n p
  | _ => True
variable {Ω C hno}
theorem level_refl (n:Nat) (v:RawValue (hw:=hw) Ω C hno):LevelEq _ _ _ n v v:=by
  cases v <;> exact rfl
theorem level_mono {n m:Nat} (h:n ≤ m) {v w:RawValue (hw:=hw) Ω C hno}
    (he:LevelEq _ _ _ m v w):LevelEq _ _ _ n v w:=by
  cases v <;> cases w <;> try exact he
  exact FreeObs.Agree.mono h he
theorem bounded_mono {n m:Nat} (h:n ≤ m) {v:RawValue (hw:=hw) Ω C hno}
    (hv:Bounded _ _ _ n v):Bounded _ _ _ m v:=by
  cases v <;> try trivial
  exact FreeObs.InStage.mono h hv
theorem exists_bound (v:RawValue (hw:=hw) Ω C hno):∃ n,Bounded _ _ _ n v:=by
  cases v with
  | plain p => exact ⟨0,trivial⟩
  | plus p => exact ⟨0,trivial⟩
  | minus p => exact FreeObs.InStage.exists_stage p
theorem level_base {n:Nat} {v w:RawValue (hw:=hw) Ω C hno}
    (he:LevelEq _ _ _ n v w):base _ _ _ v = base _ _ _ w:=by
  cases v <;> cases w <;> try exact False.elim he
  · exact congrArg (fun p => (ActPlain.prefixEquiv hno (Base Ω) p.1 p.2).1) he
  · exact congrFun (congrArg FreeObs.Table.continuing he) []
  · exact congrArg (fun p => (FreeObs.behavior _ _ _ _ p).continuing []) he
end RawValue
end S_wpc_barendregt_geuvers_klop.ObsVals
namespace S_wpc_barendregt_geuvers_klop
universe u
namespace FreeL
variable {S:Type u} {P:Specification S} {C:Set (Set S)} {I J:Set S}
theorem path_sign {s t b:Bool} (h:FreeL P C I s) (k:FreeL P C J t)
    (e:SignedPath (SecEdge P C) I J b):s = Bool.xor b t:=by
  obtain ⟨D,hd,hp⟩:=k.2
  exact h.sign_unique ⟨h.1,D,hd,e.append hp⟩
end FreeL
namespace ObsVals
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P)
variable (C:Set (Set S)) (hw:SystemWeaklyNormalizing P)
structure FrameKey (T:ActTy Ω C) where
  domain:Expr S
  body:Expr S
  product:T.type = .pi domain body
  argument:Expr S
  normal:Normal argument
  typed:Ω.HasType argument domain
  active:ActL P C (Ω.profile (body.instantiate argument))
namespace FrameKey
variable {Ω C} {T:ActTy Ω C} (a:FrameKey Ω C T)
theorem sorted:∃ s,Ω.HasType (.pi a.domain a.body) (.sort s) :=
  a.product ▸ T.sorted
theorem domain_normal:Normal a.domain:=(a.product ▸ T.normal).pi_domain
theorem body_normal:Normal a.body:=(a.product ▸ T.normal).pi_body
theorem domain_sorted:∃ s,Ω.HasType a.domain (.sort s):=by
  obtain ⟨s,hs⟩:=a.sorted
  exact Ω.domain_sorted hs
theorem target_sorted:∃ s,Ω.HasType (a.body.instantiate a.argument) (.sort s):=by
  obtain ⟨s,hs⟩:=a.sorted
  exact Ω.frame_target_sorted hs a.typed
include hw
theorem profile_data:∃ J,
    ProfileTriple P (Ω.profile a.domain) J (Ω.profile T.type) ∧
    PositivePath (PriEdge P) (Ω.profile (a.body.instantiate a.argument)) J ∧
    ActL P C J:=by
  obtain ⟨s,hs⟩:=a.sorted
  obtain ⟨J,hf,hp⟩:=Ω.frame_profiles hw hs a.typed
  rw [← a.product] at hf
  have hj:=ObsLayers.positive a.active.layer hp
  exact ⟨J,hf,hp,T.active.predecessor (.single (.positive hj T.active.layer (.codomain hf)))⟩
theorem target_path:PositivePath (SecEdge P C)
    (Ω.profile (a.body.instantiate a.argument)) (Ω.profile T.type):=by
  obtain ⟨J,hf,hp,hj⟩:=a.profile_data hw
  exact .tail (ObsLayers.secondary a.active.layer hp)
    (.positive hj.layer T.active.layer (.codomain hf))
theorem domain_active (hd:Ω.profile a.domain ∈ ObsLayers P C) :
    ActL P C (Ω.profile a.domain):=by
  obtain ⟨J,hf,_,hj⟩:=a.profile_data hw
  exact T.active.predecessor (.single (.negative hd hj.layer T.active.layer hf))
theorem domain_edge (hd:ActL P C (Ω.profile a.domain)) :
    SecEdge P C (Ω.profile a.domain) (Ω.profile T.type) true:=by
  obtain ⟨J,hf,_,hj⟩:=a.profile_data hw
  exact .negative hd.layer hj.layer T.active.layer hf
noncomputable def target:ActTy Ω C where
  type:=(a.body.instantiate a.argument).nfTerm
  normal:=by
    obtain ⟨s,hs⟩:=a.target_sorted
    exact (Expr.nfTerm_spec (hs.weakNorm hw)).2
  sorted:=by
    obtain ⟨s,hs⟩:=a.target_sorted
    exact ⟨s,hs.nfTerm hw⟩
  active:=by simpa only [CTower.profile_nfTerm] using a.active
def domainType (hd:ActL P C (Ω.profile a.domain)):ActTy Ω C :=
  ⟨a.domain,a.domain_normal,a.domain_sorted,hd⟩
theorem plain_domain (hp:PlainL P C (Ω.profile T.type))
    (hd:ActL P C (Ω.profile a.domain)):PlainL P C (Ω.profile a.domain) :=
  hp.predecessor (a.domain_edge hw hd)
theorem free_target_sign {s t:Bool}
    (hT:FreeL P C (Ω.profile T.type) s)
    (hL:FreeL P C (Ω.profile (a.target hw).type) t):t = s:=by
  have hl:FreeL P C (Ω.profile (a.body.instantiate a.argument)) t:=by
    simpa only [target,CTower.profile_nfTerm] using hL
  simpa using hl.path_sign hT (a.target_path hw).parity
theorem free_domain_sign {s t:Bool}
    (hT:FreeL P C (Ω.profile T.type) s)
    (hI:FreeL P C (Ω.profile a.domain) t):t = !s:=by
  have h:=hI.edge_sign hT (a.domain_edge hw hI.active)
  simpa using h
theorem domain_direct (hC:IsComp (PriEdge P) C)
    (hK:Ω.profile T.type ∈ C) (hL:Ω.profile (a.target hw).type ∈ C)
    (hd:ActL P C (Ω.profile a.domain)):DirectLayer P C (Ω.profile a.domain):=by
  obtain ⟨J,hf,hp,_⟩:=a.profile_data hw
  have hl:Ω.profile (a.body.instantiate a.argument) ∈ C:=by
    simpa only [target,CTower.profile_nfTerm] using hL
  have hj:J ∈ C:=hC.between hl hK hp.reach (.single (.codomain hf))
  exact ⟨hd.layer,J,hj,Ω.profile T.type,hK,hf⟩
theorem domain_not_minus (hC:IsComp (PriEdge P) C)
    (hK:Ω.profile T.type ∈ C) (hL:Ω.profile (a.target hw).type ∈ C) :
    ¬ FreeL P C (Ω.profile a.domain) true:=by
  intro hm
  exact Bool.noConfusion (hm.direct_sign (a.domain_direct hw hC hK hL hm.active))
end FrameKey
variable [Fintype S] {hw} (hno:¬ ForbiddenConfiguration P C)
def PayFits (D:Expr S) (p:Option (RawValue (hw:=hw) Ω C hno)):Prop :=
  match p with
  | none => ¬ ActL P C (Ω.profile D)
  | some v => Fits Ω C hno D v
namespace Fits
variable {Ω C hno} {T:Expr S} {v:RawValue (hw:=hw) Ω C hno}
theorem active (h:Fits Ω C hno T v):ActL P C (Ω.profile T):=by
  cases v with
  | plain p => exact h ▸ p.1.plain.active
  | plus p => exact h.active
  | minus p => exact h.active
end Fits
abbrev PlusFrame:=FreeObs.Frame (Expr S) (PlainValue (hw:=hw) Ω C hno)
  (Minus (hw:=hw) Ω C hno)
abbrev MinusFrame:=FreeObs.Frame (Expr S) (PlainValue (hw:=hw) Ω C hno)
  (Plus (hw:=hw) Ω C hno)
def plusPayload:FreeObs.Payload (PlainValue (hw:=hw) Ω C hno)
    (Minus (hw:=hw) Ω C hno) → Option (RawValue (hw:=hw) Ω C hno)
  | .none => none
  | .opposite m => some (.minus m)
  | .plain p => some (.plain p)
def minusPayload:FreeObs.Payload (PlainValue (hw:=hw) Ω C hno)
    (Plus (hw:=hw) Ω C hno) → Option (RawValue (hw:=hw) Ω C hno)
  | .none => none
  | .opposite p => some (.plus p)
  | .plain p => some (.plain p)
def Gate (T:ActTy Ω C) (q:Expr S)
    (p:Option (RawValue (hw:=hw) Ω C hno)) (exit:Bool):Prop :=
  ∃ a:FrameKey Ω C T,a.argument = q ∧ PayFits Ω C hno a.domain p ∧
    (PlainL P C (Ω.profile (a.target hw).type) ↔ exit = true)
end ObsVals
namespace Converts
variable {S:Type u}
theorem app {f f' a a':Expr S} (hf:Converts f f') (ha:Converts a a') :
    Converts (.app f a) (.app f' a'):=by
  obtain ⟨g,hg,hg'⟩:=hf.join
  obtain ⟨b,hb,hb'⟩:=ha.join
  exact .trans _ _ _ (hg.app hb).converts (.symm _ _ (hg'.app hb').converts)
theorem lam {A A' b b':Expr S} (hA:Converts A A') (hb:Converts b b') :
    Converts (.lam A b) (.lam A' b'):=by
  obtain ⟨D,hD,hD'⟩:=hA.join
  obtain ⟨c,hc,hc'⟩:=hb.join
  exact .trans _ _ _ (hD.lam hc).converts (.symm _ _ (hD'.lam hc').converts)
end Converts
namespace Expr.Scoped
variable {S:Type u} {n:Nat} {M:Expr S}
theorem subst_converts (hM:Scoped n M) {σ τ:Nat → Expr S}
    (hc:∀ i,i < n → Converts (σ i) (τ i)):Converts (M.subst σ) (M.subst τ):=by
  induction M generalizing n σ τ with
  | var i => exact hc i hM
  | sort s => exact .refl _
  | app f a ihf iha => exact .app (ihf hM.1 hc) (iha hM.2 hc)
  | lam A b ihA ihb | pi A b ihA ihb =>
    have he:∀ i,i < n+1 → Converts (Expr.liftSub σ i) (Expr.liftSub τ i):=by
      intro i hi
      cases i with
      | zero => exact .refl _
      | succ i => exact (hc i (Nat.lt_of_succ_lt_succ hi)).rename Nat.succ
    first
    | exact .lam (ihA hM.1 hc) (ihb hM.2 he)
    | exact .pi (ihA hM.1 hc) (ihb hM.2 he)
end Expr.Scoped
namespace Lookup
variable {S:Type u} {Γ:List (Expr S)} {n:Nat}
theorem unique {A B:Expr S} (hA:Lookup Γ n A) (hB:Lookup Γ n B):A = B:=by
  induction hA generalizing B with
  | zero => cases hB; rfl
  | succ A h ih => cases hB with
    | succ _ hB => exact congrArg (Expr.rename Nat.succ) (ih hB)
end Lookup
namespace CTower.HasType
variable {S:Type u} {P:Specification S} {Ω:CTower P} {M A:Expr S}
theorem actual_type (h:Ω.HasType M A) (hw:SystemWeaklyNormalizing P) :
    Cands.ActualType Ω A.nfTerm:=by
  rcases h.regularity with ⟨s,rfl⟩ | ⟨s,hs⟩
  · exact .inr ⟨s,Expr.nfTerm_of_normal (Normal.sort s)⟩
  · exact .inl ⟨(Expr.nfTerm_spec (hs.weakNorm hw)).2,s,hs.nfTerm hw⟩
theorem actual_expression {s:S} (h:Ω.HasType M (.sort s)) (hw:SystemWeaklyNormalizing P) :
    Cands.ActualType Ω M.nfTerm :=
  .inl ⟨(Expr.nfTerm_spec (h.weakNorm hw)).2,s,h.nfTerm hw⟩
end CTower.HasType
namespace ObsVals
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
namespace Param
def Bounded (n:Nat) (p:Option (RawValue (hw:=hw) Ω C hno)):Prop :=
  ∀ v,p = some v → RawValue.Bounded Ω C hno n v
def LevelEq (n:Nat):Option (RawValue (hw:=hw) Ω C hno) → Option (RawValue (hw:=hw) Ω C hno) → Prop
  | none,none => True
  | some v,some w => RawValue.LevelEq Ω C hno n v w
  | _,_ => False
variable {Ω C hno}
theorem level_refl (n:Nat) (p:Option (RawValue (hw:=hw) Ω C hno)):LevelEq _ _ _ n p p:=by
  cases p with
  | none => trivial
  | some p => exact p.level_refl n
theorem level_mono {n m:Nat} (h:n ≤ m) {p q:Option (RawValue (hw:=hw) Ω C hno)}
    (he:LevelEq _ _ _ m p q):LevelEq _ _ _ n p q:=by
  cases p <;> cases q <;> try exact he
  exact RawValue.level_mono h he
theorem bounded_mono {n m:Nat} (h:n ≤ m) {p:Option (RawValue (hw:=hw) Ω C hno)}
    (he:Bounded _ _ _ n p):Bounded _ _ _ m p:=fun v hv => RawValue.bounded_mono h (he v hv)
theorem exists_bound (p:Option (RawValue (hw:=hw) Ω C hno)):∃ n,Bounded _ _ _ n p:=by
  cases p with
  | none => exact ⟨0,fun _ h => by cases h⟩
  | some p =>
    obtain ⟨n,hn⟩:=p.exists_bound
    exact ⟨n,fun _ h => Option.some.inj h ▸ hn⟩
end Param
structure ValEnv (Γ:List (Expr S)) where
  images:Nat → Expr S
  typed:Ω.TySub Γ images
  parameters:Nat → Option (RawValue (hw:=hw) Ω C hno)
  lawful:∀ n A,Lookup Γ n A → PayFits Ω C hno (A.subst images).nfTerm (parameters n)
namespace ValEnv
variable {Ω C hno} {Γ:List (Expr S)} (e:ValEnv (hw:=hw) Ω C hno Γ)
def Bounded (k:Nat):Prop:=∀ n,n < Γ.length → Param.Bounded Ω C hno k (e.parameters n)
def ImageCompatible (f:ValEnv (hw:=hw) Ω C hno Γ):Prop :=
  ∀ n,n < Γ.length → Converts (e.images n) (f.images n)
def LevelEq (k:Nat) (f:ValEnv (hw:=hw) Ω C hno Γ):Prop :=
  ImageCompatible e f ∧ ∀ n,n < Γ.length → Param.LevelEq Ω C hno k (e.parameters n) (f.parameters n)
theorem bounded_mono {k l:Nat} (hkl:k ≤ l) (he:e.Bounded k):e.Bounded l :=
  fun n hn => Param.bounded_mono hkl (he n hn)
theorem exists_bound:∃ k,e.Bounded k:=by
  have hh:∀ n,∃ k,∀ i,i < n → Param.Bounded Ω C hno k (e.parameters i):=by
    intro n
    induction n with
    | zero => exact ⟨0,fun _ h => by omega⟩
    | succ n ih =>
      obtain ⟨k,hk⟩:=ih
      obtain ⟨l,hl⟩:=Param.exists_bound (e.parameters n)
      refine ⟨max k l,fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Param.bounded_mono (le_max_left k l) (hk i hi)
      · exact Param.bounded_mono (le_max_right k l) hl
  exact hh Γ.length
theorem level_refl (k:Nat):e.LevelEq k e :=
  ⟨fun _ _ => .refl _,fun _ _ => Param.level_refl _ _⟩
theorem level_mono {k l:Nat} {f:ValEnv (hw:=hw) Ω C hno Γ}
    (hkl:k ≤ l) (he:e.LevelEq l f):e.LevelEq k f :=
  ⟨he.1,fun n hn => Param.level_mono hkl (he.2 n hn)⟩
def cons {A a:Expr S} (ha:Ω.HasType a (A.subst e.images))
    (p:Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno (A.subst e.images).nfTerm p) :
    ValEnv (hw:=hw) Ω C hno (A :: Γ) where
  images:=fun n => match n with | 0 => a | n+1 => e.images n
  typed:=e.typed.cons ha
  parameters:=fun n => match n with | 0 => p | n+1 => e.parameters n
  lawful:=by
    intro n B hn
    cases hn with
    | zero => simpa only [Expr.subst_rename,Function.comp_def] using hp
    | succ A hn => simpa only [Expr.subst_rename,Function.comp_def] using e.lawful _ _ hn
theorem bounded_cons {A a:Expr S} (ha:Ω.HasType a (A.subst e.images))
    (p:Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno (A.subst e.images).nfTerm p)
    {k:Nat} (he:e.Bounded k) (hb:Param.Bounded Ω C hno k p) :
    (e.cons ha p hp).Bounded k:=by
  intro n hn
  cases n with
  | zero => exact hb
  | succ n => exact he n (Nat.lt_of_succ_lt_succ hn)
theorem actual_expr_eq {f:ValEnv (hw:=hw) Ω C hno Γ} (he:e.ImageCompatible f)
    {M A:Expr S} (ht:HasType P Γ M A) :
    (M.subst e.images).nfTerm = (M.subst f.images).nfTerm :=
  Expr.nfTerm_converts ((CTower.HasType.subst ht e.typed).weakNorm hw)
    ((CTower.HasType.subst ht f.typed).weakNorm hw)
    (ht.scope.1.subst_converts he)
theorem actual_type_eq {f:ValEnv (hw:=hw) Ω C hno Γ} (he:e.ImageCompatible f)
    {M A:Expr S} (ht:HasType P Γ M A) :
    (A.subst e.images).nfTerm = (A.subst f.images).nfTerm :=
  Expr.nfTerm_converts ((CTower.HasType.subst ht e.typed).type_weakNorm hw)
    ((CTower.HasType.subst ht f.typed).type_weakNorm hw)
    (ht.scope.2.subst_converts he)
end ValEnv
end ObsVals
namespace WeaklyNormalizing
variable {S:Type u} {A B:Expr S}
theorem pi_domain (h:WeaklyNormalizing (.pi A B)):WeaklyNormalizing A:=by
  obtain ⟨N,hr,hn⟩:=h
  obtain ⟨D,E,rfl,hD,_⟩:=Reduces.pi_inv hr
  exact ⟨D,hD,hn.pi_domain⟩
theorem pi_body (h:WeaklyNormalizing (.pi A B)):WeaklyNormalizing B:=by
  obtain ⟨N,hr,hn⟩:=h
  obtain ⟨D,E,rfl,_,hE⟩:=Reduces.pi_inv hr
  exact ⟨E,hE,hn.pi_body⟩
end WeaklyNormalizing
namespace Expr
variable {S:Type u}
theorem instantiate_liftSub (E:Expr S) (σ:Nat → Expr S) (n:Expr S) :
    (E.subst (liftSub σ)).instantiate n =
      E.subst (fun i => match i with | 0 => n | i+1 => σ i):=by
  rw [instantiate,subst_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => simpa only [liftSub_succ,subst_rename,Function.comp_def,single] using subst_var (σ i)
end Expr
namespace CTower.HasType
variable {S:Type u} {P:Specification S} {Ω:CTower P} {M A:Expr S} {s:S}
theorem denormalize_type (h:Ω.HasType M A.nfTerm) (hA:Ω.HasType A (.sort s))
    (hw:SystemWeaklyNormalizing P):Ω.HasType M A :=
  h.conversion hA (.symm _ _ (Expr.nfTerm_spec (hA.weakNorm hw)).1.converts)
end CTower.HasType
namespace ObsVals
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
namespace PayFits
variable {Ω C hno}
theorem exists_of_actual (T:ActualType Ω):∃ p,PayFits (hw:=hw) Ω C hno T.val p:=by
  by_cases ha:ActL P C (Ω.profile T.val)
  · exact ⟨some (distinguished (hw:=hw) Ω C hno (.ofActual T ha)).val,
      (distinguished (hw:=hw) Ω C hno (.ofActual T ha)).property⟩
  · exact ⟨none,ha⟩
end PayFits
structure ProdInst where
  context:List (Expr S)
  domain:Expr S
  body:Expr S
  domainSort:S
  bodySort:S
  resultSort:S
  domainTyping:HasType P context domain (.sort domainSort)
  bodyTyping:HasType P (domain :: context) body (.sort bodySort)
  rule:P.rule domainSort bodySort resultSort
  environment:ValEnv (hw:=hw) Ω C hno context
namespace ProdInst
variable {Ω C hno} (t:ProdInst (hw:=hw) Ω C hno)
def rawDomain:Expr S:=t.domain.subst t.environment.images
def rawBody:Expr S:=t.body.subst (Expr.liftSub t.environment.images)
noncomputable def domainNF:Expr S:=t.rawDomain.nfTerm
noncomputable def bodyNF:Expr S:=t.rawBody.nfTerm
def rawTarget (n:Expr S):Expr S :=
  t.body.subst (fun i => match i with | 0 => n | i+1 => t.environment.images i)
noncomputable def targetNF (n:Expr S):Expr S:=(t.rawTarget n).nfTerm
theorem rawDomain_typed:Ω.HasType t.rawDomain (.sort t.domainSort) :=
  CTower.HasType.subst t.domainTyping t.environment.typed
theorem rawProduct_typed:Ω.HasType (.pi t.rawDomain t.rawBody) (.sort t.resultSort) :=
  CTower.HasType.subst (HasType.product t.domainTyping t.bodyTyping t.rule) t.environment.typed
theorem domain_normal:Normal t.domainNF:=(Expr.nfTerm_spec (t.rawDomain_typed.weakNorm hw)).2
theorem body_normal:Normal t.bodyNF :=
  (Expr.nfTerm_spec (t.rawProduct_typed.weakNorm hw).pi_body).2
theorem product_nf:(Expr.pi t.rawDomain t.rawBody).nfTerm = .pi t.domainNF t.bodyNF :=
  Expr.nfTerm_pi (t.rawProduct_typed.weakNorm hw).pi_domain
    (t.rawProduct_typed.weakNorm hw).pi_body
theorem product_typed:Ω.HasType (.pi t.domainNF t.bodyNF) (.sort t.resultSort):=by
  rw [← t.product_nf]
  exact t.rawProduct_typed.nfTerm hw
theorem rawArgument {n:Expr S} (hn:Ω.HasType n t.domainNF):Ω.HasType n t.rawDomain :=
  hn.denormalize_type t.rawDomain_typed hw
noncomputable def extend {n:Expr S} (hn:Ω.HasType n t.domainNF)
    (p:Option (RawValue (hw:=hw) Ω C hno)) (hp:PayFits Ω C hno t.domainNF p) :
    ValEnv (hw:=hw) Ω C hno (t.domain :: t.context) :=
  t.environment.cons (t.rawArgument hn) p hp
theorem rawTarget_typed {n:Expr S} (hn:Ω.HasType n t.domainNF) :
    Ω.HasType (t.rawTarget n) (.sort t.bodySort) :=
  CTower.HasType.subst t.bodyTyping (t.environment.typed.cons (t.rawArgument hn))
theorem target_typed {n:Expr S} (hn:Ω.HasType n t.domainNF) :
    Ω.HasType (t.targetNF n) (.sort t.bodySort):=(t.rawTarget_typed hn).nfTerm hw
theorem target_eq {n:Expr S} (hn:Ω.HasType n t.domainNF) :
    t.targetNF n = (t.bodyNF.instantiate n).nfTerm:=by
  have hr:Reduces (t.rawTarget n) (t.bodyNF.instantiate n):=by
    rw [rawTarget,← Expr.instantiate_liftSub]
    exact (Expr.nfTerm_spec (t.rawProduct_typed.weakNorm hw).pi_body).1.subst (Expr.single n)
  obtain ⟨s,hs⟩:=Ω.frame_target_sorted t.product_typed hn
  exact Expr.nfTerm_converts ((t.rawTarget_typed hn).weakNorm hw)
    (hs.weakNorm hw) hr.converts
noncomputable def testers (d:Candidate Ω t.domainNF):Set (Expr S) :=
  if Ω.profile t.domainNF ∈ C then d.val else Cands.Top Ω t.domainNF
theorem testers_top (d:Candidate Ω t.domainNF):t.testers d ⊆ Cands.Top Ω t.domainNF:=by
  unfold testers
  split
  · exact d.property.upper
  · exact Set.Subset.rfl
abbrev BodyReads:=∀ (n:Expr S),Ω.HasType n t.domainNF →
  (p:Option (RawValue (hw:=hw) Ω C hno)) → PayFits Ω C hno t.domainNF p → Candidate Ω (t.targetNF n)
noncomputable def fibers (b:t.BodyReads) (n:Expr S):Set (Set (Expr S)) :=
  if hn:Ω.HasType n t.domainNF then
    if Ω.profile (t.targetNF n) ∈ C then
      {U | ∃ p hp,U = (b n hn p hp).val}
    else {Cands.Top Ω (t.targetNF n)}
  else ∅
theorem fibers_candidate (d:Candidate Ω t.domainNF) (b:t.BodyReads)
    {n:Expr S} (hn:n ∈ t.testers d) {U:Set (Expr S)} (hU:U ∈ t.fibers b n) :
    Cands.IsCandidate Ω (t.bodyNF.instantiate n).nfTerm U:=by
  have ht:=(t.testers_top d hn).1
  rw [← t.target_eq ht]
  simp only [fibers,ht,dite_true] at hU
  split_ifs at hU with hc
  · obtain ⟨p,hp,rfl⟩:=hU
    exact (b n ht p hp).property
  · have he:U = Cands.Top Ω (t.targetNF n):=hU
    rw [he]
    exact Cands.top_candidate
noncomputable def candidate (d:Candidate Ω t.domainNF) (b:t.BodyReads) :
    Candidate Ω (.pi t.domainNF t.bodyNF) :=
  ⟨Cands.ProductTest Ω t.domainNF t.bodyNF (t.testers d) (t.fibers b),
    Cands.productTest_candidate hw (t.testers_top d) (fun _ hn _ hU => t.fibers_candidate d b hn hU)⟩
theorem candidate_body (d:Candidate Ω t.domainNF) (b:t.BodyReads) {M n:Expr S}
    (hM:M ∈ (t.candidate d b).val) (hn:n ∈ t.testers d)
    (hc:Ω.profile (t.targetNF n) ∈ C)
    (p:Option (RawValue (hw:=hw) Ω C hno)) (hp:PayFits Ω C hno t.domainNF p) :
    Expr.app M n ∈ (b n (t.testers_top d hn).1 p hp).val:=by
  apply hM.2 n hn
  simp only [fibers,(t.testers_top d hn).1,dite_true,hc,ite_true,Set.mem_ofPred_eq]
  exact ⟨p,hp,rfl⟩
theorem candidate_outside (d:Candidate Ω t.domainNF) (b:t.BodyReads) {M n:Expr S}
    (hM:M ∈ (t.candidate d b).val) (hn:n ∈ t.testers d)
    (hc:Ω.profile (t.targetNF n) ∉ C) :
    Expr.app M n ∈ Cands.Top Ω (t.targetNF n):=by
  apply hM.2 n hn
  simp only [fibers,(t.testers_top d hn).1,dite_true,hc,ite_false,Set.mem_singleton_iff]
end ProdInst
end ObsVals
end S_wpc_barendregt_geuvers_klop
end OMA
namespace OMA
namespace S_wpc_barendregt_geuvers_klop
universe u
namespace ActPlain.Node
variable {S:Type u} {P:Specification S} {Ω:CTower P} {C:Set (Set S)}
theorem ext {n m:ActPlain.Node Ω C} (h:n.type = m.type):n = m:=by
  cases n; cases m; cases h; rfl
end ActPlain.Node
namespace ObsVals
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
namespace ActTy
variable {Ω C}
abbrev plainNode (T:ActTy Ω C) (hp:PlainL P C (Ω.profile T.type)):ActPlain.Node Ω C :=
  ⟨T.type,T.normal,T.sorted,hp⟩
omit [Fintype S] in
theorem ext {T U:ActTy Ω C} (h:T.type = U.type):T = U:=by
  cases T; cases U; cases h; rfl
end ActTy
namespace Value
variable {Ω C hno}
def plain (n:ActPlain.Node Ω C) (p:ActPlain.Space (hw:=hw) hno (Base Ω) n) :
    Value (hw:=hw) Ω C hno n.type:=⟨.plain ⟨n,p⟩,rfl⟩
theorem plain_exists (n:ActPlain.Node Ω C) (v:Value (hw:=hw) Ω C hno n.type) :
    ∃ p,plain n p = v:=by
  rcases v with ⟨v,hv⟩
  cases v with
  | plain p =>
    have he:p.1 = n:=ActPlain.Node.ext hv
    rcases p with ⟨m,p⟩
    dsimp at he
    subst m
    exact ⟨p,rfl⟩
  | plus p => exact False.elim (hv.1 n.plain)
  | minus p => exact False.elim (hv.1 n.plain)
noncomputable def asPlain (n:ActPlain.Node Ω C) (v:Value (hw:=hw) Ω C hno n.type) :
    ActPlain.Space (hw:=hw) hno (Base Ω) n:=(plain_exists n v).choose
@[simp] theorem plain_asPlain (n:ActPlain.Node Ω C) (v:Value (hw:=hw) Ω C hno n.type) :
    plain n (asPlain n v) = v:=(plain_exists n v).choose_spec
@[simp] theorem asPlain_plain (n:ActPlain.Node Ω C) (p:ActPlain.Space (hw:=hw) hno (Base Ω) n) :
    asPlain n (plain n p) = p:=by
  have he:=congrArg Subtype.val (plain_asPlain n (plain n p))
  exact eq_of_heq (Sigma.mk.inj (RawValue.plain.inj he)).2
theorem plus_exists {T:Expr S} (hT:FreeL P C (Ω.profile T) false)
    (v:Value (hw:=hw) Ω C hno T):∃ p,v.val = .plus p:=by
  rcases v with ⟨v,hv⟩
  cases v with
  | plain p => exact False.elim (hT.1 (hv ▸ p.1.plain))
  | plus p => exact ⟨p,rfl⟩
  | minus p => exact False.elim (Bool.noConfusion (hT.sign_unique hv))
theorem minus_exists {T:Expr S} (hT:FreeL P C (Ω.profile T) true)
    (v:Value (hw:=hw) Ω C hno T):∃ p,v.val = .minus p:=by
  rcases v with ⟨v,hv⟩
  cases v with
  | plain p => exact False.elim (hT.1 (hv ▸ p.1.plain))
  | plus p => exact False.elim (Bool.noConfusion (hT.sign_unique hv))
  | minus p => exact ⟨p,rfl⟩
noncomputable def asPlus {T:Expr S} (hT:FreeL P C (Ω.profile T) false)
    (v:Value (hw:=hw) Ω C hno T):Plus (hw:=hw) Ω C hno:=(plus_exists hT v).choose
noncomputable def asMinus {T:Expr S} (hT:FreeL P C (Ω.profile T) true)
    (v:Value (hw:=hw) Ω C hno T):Minus (hw:=hw) Ω C hno:=(minus_exists hT v).choose
@[simp] theorem asPlus_spec {T:Expr S} (hT:FreeL P C (Ω.profile T) false)
    (v:Value (hw:=hw) Ω C hno T):v.val = .plus (asPlus hT v):=(plus_exists hT v).choose_spec
@[simp] theorem asMinus_spec {T:Expr S} (hT:FreeL P C (Ω.profile T) true)
    (v:Value (hw:=hw) Ω C hno T):v.val = .minus (asMinus hT v):=(minus_exists hT v).choose_spec
end Value
namespace ActualPlainKey
variable {Ω C hno}
def frame {n:ActPlain.Node Ω C} (a:ActPlain.Key Ω C n) :
    FrameKey Ω C (⟨n.type,n.normal,n.sorted,n.plain.active⟩:ActTy Ω C) :=
  ⟨a.domain,a.body,a.product,a.argument,a.normal,a.typed,a.active⟩
noncomputable def payload {n:ActPlain.Node Ω C} (a:ActPlain.Key Ω C n)
    (p:(ActPlain.schema hw).FrameParams (ActPlain.Space (hw:=hw) hno (Base Ω)) a) :
    Option (RawValue (hw:=hw) Ω C hno) :=
  if h:ActL P C (Ω.profile a.domain) then
    some (.plain ⟨a.domainNode hw h,p _ (by simp only [ActPlain.schema,h,dite_true])⟩)
  else none
theorem payload_fits {n:ActPlain.Node Ω C} (a:ActPlain.Key Ω C n)
    (p:(ActPlain.schema hw).FrameParams (ActPlain.Space (hw:=hw) hno (Base Ω)) a) :
    PayFits Ω C hno a.domain (payload a p):=by
  unfold payload
  split
  · rfl
  · assumption
noncomputable def parameters {n:ActPlain.Node Ω C} (a:ActPlain.Key Ω C n)
    (p:Option (RawValue (hw:=hw) Ω C hno)) (hp:PayFits Ω C hno a.domain p) :
    (ActPlain.schema hw).FrameParams (ActPlain.Space (hw:=hw) hno (Base Ω)) a:=by
  cases p with
  | none =>
    intro d hd
    exact False.elim (hp (ActPlain.Schema.domain_eq hd).choose)
  | some v =>
    intro d hd
    apply Value.asPlain d
    refine ⟨v,?_⟩
    obtain ⟨ha,rfl⟩:=ActPlain.Schema.domain_eq hd
    exact hp
@[simp] theorem payload_parameters {n:ActPlain.Node Ω C} (a:ActPlain.Key Ω C n)
    (p:Option (RawValue (hw:=hw) Ω C hno)) (hp:PayFits Ω C hno a.domain p) :
    payload a (parameters a p hp) = p:=by
  unfold payload
  split
  · rename_i ha
    cases p with
    | none => exact False.elim (hp ha)
    | some v =>
      simpa only [parameters,Value.plain] using
        congrArg (fun w:Value (hw:=hw) Ω C hno a.domain => some w.val)
          (Value.plain_asPlain (a.domainNode hw ha) ⟨v,hp⟩)
  · rename_i ha
    cases p with
    | none => rfl
    | some v => exact False.elim (ha hp.active)
theorem payload_injective {n:ActPlain.Node Ω C} (a:ActPlain.Key Ω C n) :
    Function.Injective (payload (hw:=hw) (hno:=hno) a):=by
  intro p q he
  funext d hd
  obtain ⟨ha,rfl⟩:=ActPlain.Schema.domain_eq hd
  simp only [payload,ha,dite_true,Option.some.injEq,RawValue.plain.injEq] at he
  exact eq_of_heq (Sigma.mk.inj he).2
@[simp] theorem parameters_payload {n:ActPlain.Node Ω C} (a:ActPlain.Key Ω C n)
    (p:(ActPlain.schema hw).FrameParams (ActPlain.Space (hw:=hw) hno (Base Ω)) a) :
    parameters a (payload a p) (payload_fits a p) = p :=
  payload_injective a (payload_parameters a (payload a p) (payload_fits a p))
end ActualPlainKey
namespace FrameKey
variable {Ω C hno}
omit [Fintype S] in
theorem ext {T:ActTy Ω C} {a b:FrameKey Ω C T}
    (h:a.argument = b.argument):a = b:=by
  cases a with
  | mk D E ht q hn hh hact =>
    cases b with
    | mk D' E' ht' q' hn' hh' hact' =>
      obtain ⟨rfl,rfl⟩:=Expr.pi.inj (ht.symm.trans ht')
      cases h
      rfl
abbrev plainKey {T:ActTy Ω C} (a:FrameKey Ω C T)
    (hT:PlainL P C (Ω.profile T.type)):ActPlain.Key Ω C (T.plainNode hT) :=
  ⟨a.domain,a.body,a.product,a.argument,a.normal,a.typed,a.active⟩
omit [Fintype S] in
theorem free_target {T:ActTy Ω C} (a:FrameKey Ω C T) {sgn:Bool}
    (hT:FreeL P C (Ω.profile T.type) sgn)
    (ht:¬ PlainL P C (Ω.profile (a.target hw).type)) :
    FreeL P C (Ω.profile (a.target hw).type) sgn:=by
  rcases (a.target hw).active.classify with h | h | h
  · exact False.elim (ht h)
  · exact a.free_target_sign hw hT h ▸ h
  · exact a.free_target_sign hw hT h ▸ h
end FrameKey
noncomputable def packMinus
    (t:FreeObs.Table (Expr S) (PlainValue (hw:=hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw:=hw) Ω C hno)) (Plus (hw:=hw) Ω C hno)):Minus (hw:=hw) Ω C hno :=
  if h:∃ x,FreeObs.behavior _ _ _ _ x = t then h.choose
  else FreeObs.minusDefault _ _ (topBase Ω) none
theorem packMinus_spec
    (t:FreeObs.Table (Expr S) (PlainValue (hw:=hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw:=hw) Ω C hno)) (Plus (hw:=hw) Ω C hno))
    (h:∃ x,FreeObs.behavior _ _ _ _ x = t) :
    FreeObs.behavior _ _ _ _ (packMinus Ω C hno t) = t:=by
  simp only [packMinus,h,dite_true]
  exact h.choose_spec
theorem packMinus_stage {n:Nat}
    (t:FreeObs.Table (Expr S) (PlainValue (hw:=hw) Ω C hno) (Base Ω)
      (Option (PlainValue (hw:=hw) Ω C hno)) (Plus (hw:=hw) Ω C hno))
    (h:∃ x,FreeObs.InStage n x ∧ FreeObs.behavior _ _ _ _ x = t) :
    FreeObs.InStage n (packMinus Ω C hno t):=by
  obtain ⟨x,hx,he⟩:=h
  have hp:=packMinus_spec Ω C hno t ⟨x,he⟩
  have hh:=FreeObs.behavior_injective (topBase Ω) (none:Option (PlainValue (hw:=hw) Ω C hno))
    (hp.trans he.symm)
  exact hh ▸ hx
end ObsVals
end S_wpc_barendregt_geuvers_klop
namespace S_wpc_barendregt_geuvers_klop.ObsVals
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
namespace Gate
variable {Ω C hno} {T:ActTy Ω C} {q:Expr S}
variable {p:Option (RawValue (hw:=hw) Ω C hno)} {exit:Bool}
noncomputable def frame (h:Gate Ω C hno T q p exit):FrameKey Ω C T:=h.choose
theorem argument (h:Gate Ω C hno T q p exit):h.frame.argument = q:=h.choose_spec.1
theorem payload (h:Gate Ω C hno T q p exit):PayFits Ω C hno h.frame.domain p:=h.choose_spec.2.1
theorem plain (h:Gate Ω C hno T q p true) :
    PlainL P C (Ω.profile (h.frame.target hw).type):=h.choose_spec.2.2.mpr rfl
theorem not_plain (h:Gate Ω C hno T q p false) :
    ¬ PlainL P C (Ω.profile (h.frame.target hw).type):=fun hp => Bool.noConfusion (h.choose_spec.2.2.mp hp)
theorem unique (h:Gate Ω C hno T q p exit) (a:FrameKey Ω C T) (ha:a.argument = q) :
    h.frame = a:=FrameKey.ext (h.argument.trans ha.symm)
end Gate
abbrev LambdaAction (T:ActTy Ω C):=(a:FrameKey Ω C T) →
  (p:Option (RawValue (hw:=hw) Ω C hno)) → PayFits Ω C hno a.domain p →
  Value (hw:=hw) Ω C hno (a.target hw).type
noncomputable def tagPlain (T:ActTy Ω C) (hp:PlainL P C (Ω.profile T.type))
    (v:Value (hw:=hw) Ω C hno T.type):PlainValue (hw:=hw) Ω C hno :=
  ⟨T.plainNode hp,Value.asPlain (T.plainNode hp) v⟩
theorem tagPlain_spec (T:ActTy Ω C) (hp:PlainL P C (Ω.profile T.type))
    (v:Value (hw:=hw) Ω C hno T.type):RawValue.plain (tagPlain Ω C hno T hp v) = v.val :=
  congrArg Subtype.val (Value.plain_asPlain (T.plainNode hp) v)
noncomputable def plainLambda (T:ActTy Ω C) (hp:PlainL P C (Ω.profile T.type))
    (act:LambdaAction (hw:=hw) Ω C hno T):Value (hw:=hw) Ω C hno T.type:=by
  let n:=T.plainNode hp
  apply Value.plain n
  refine (ActPlain.prefixEquiv (hw:=hw) hno (Base Ω) n).symm ⟨topBase Ω,fun a p => ?_⟩
  let a':FrameKey Ω C T:=⟨a.domain,a.body,a.product,a.argument,a.normal,a.typed,a.active⟩
  exact Value.asPlain (a.target hw)
    (act a' (ActualPlainKey.payload a p) (ActualPlainKey.payload_fits a p))
noncomputable def lambdaExit {X:Type u}
    (decode:FreeObs.Payload (PlainValue (hw:=hw) Ω C hno) X →
      Option (RawValue (hw:=hw) Ω C hno))
    (T:ActTy Ω C) (act:LambdaAction (hw:=hw) Ω C hno T)
    (a:FreeObs.Frame (Expr S) (PlainValue (hw:=hw) Ω C hno) X) :
    Option (PlainValue (hw:=hw) Ω C hno) :=
  if h:Gate Ω C hno T a.1 (decode a.2) true then
    some (tagPlain Ω C hno (h.frame.target hw) h.plain (act h.frame (decode a.2) h.payload))
  else none
noncomputable def plusContinue (T:ActTy Ω C)
    (hT:FreeL P C (Ω.profile T.type) false) (act:LambdaAction (hw:=hw) Ω C hno T)
    (a:PlusFrame (hw:=hw) Ω C hno):Plus (hw:=hw) Ω C hno :=
  if h:Gate Ω C hno T a.1 (plusPayload Ω C hno a.2) false then
    Value.asPlus (h.frame.free_target hT h.not_plain) (act h.frame _ h.payload)
  else FreeObs.plusDefault _ _ (topBase Ω) none
noncomputable def minusContinue (T:ActTy Ω C)
    (hT:FreeL P C (Ω.profile T.type) true) (act:LambdaAction (hw:=hw) Ω C hno T)
    (a:MinusFrame (hw:=hw) Ω C hno):Minus (hw:=hw) Ω C hno :=
  if h:Gate Ω C hno T a.1 (minusPayload Ω C hno a.2) false then
    Value.asMinus (h.frame.free_target hT h.not_plain) (act h.frame _ h.payload)
  else FreeObs.minusDefault _ _ (topBase Ω) none
noncomputable def plusLambda (T:ActTy Ω C)
    (hT:FreeL P C (Ω.profile T.type) false) (act:LambdaAction (hw:=hw) Ω C hno T) :
    Plus (hw:=hw) Ω C hno where
  continuing
    | [] => topBase Ω
    | a :: as => (plusContinue Ω C hno T hT act a).continuing as
  exiting
    | ([],a) => lambdaExit Ω C hno (plusPayload Ω C hno) T act a
    | (a :: as,e) => (plusContinue Ω C hno T hT act a).exiting (as,e)
noncomputable def minusLambdaBehavior (T:ActTy Ω C)
    (hT:FreeL P C (Ω.profile T.type) true) (act:LambdaAction (hw:=hw) Ω C hno T) :=
  FreeObs.lambdaTable (topBase Ω) (minusContinue Ω C hno T hT act)
    (lambdaExit Ω C hno (minusPayload Ω C hno) T act)
noncomputable def lambdaValue (T:ActTy Ω C) (act:LambdaAction (hw:=hw) Ω C hno T) :
    Value (hw:=hw) Ω C hno T.type:=by
  by_cases hp:PlainL P C (Ω.profile T.type)
  · exact plainLambda Ω C hno T hp act
  · by_cases hf:FreeL P C (Ω.profile T.type) false
    · exact ⟨.plus (plusLambda Ω C hno T hf act),hf⟩
    · have hm:FreeL P C (Ω.profile T.type) true:=by
        rcases T.active.classify with h | h | h
        · exact False.elim (hp h)
        · exact False.elim (hf h)
        · exact h
      exact ⟨.minus (packMinus Ω C hno (minusLambdaBehavior Ω C hno T hm act)),hm⟩
namespace FrameKey
variable {Ω C hno} {T:ActTy Ω C} (a:FrameKey Ω C T)
noncomputable def plusParam (hT:FreeL P C (Ω.profile T.type) false)
    (p:Option (RawValue (hw:=hw) Ω C hno)) (hp:PayFits Ω C hno a.domain p) :
    FreeObs.Payload (PlainValue (hw:=hw) Ω C hno) (Minus (hw:=hw) Ω C hno):=by
  cases p with
  | none => exact .none
  | some v =>
    cases v with
    | plain p => exact .plain p
    | minus m => exact .opposite m
    | plus v => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))
noncomputable def minusParam (hT:FreeL P C (Ω.profile T.type) true)
    (p:Option (RawValue (hw:=hw) Ω C hno)) (hp:PayFits Ω C hno a.domain p) :
    FreeObs.Payload (PlainValue (hw:=hw) Ω C hno) (Plus (hw:=hw) Ω C hno):=by
  cases p with
  | none => exact .none
  | some v =>
    cases v with
    | plain p => exact .plain p
    | plus m => exact .opposite m
    | minus v => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))
@[simp] theorem plusPayload_parameter (hT:FreeL P C (Ω.profile T.type) false)
    (p:Option (RawValue (hw:=hw) Ω C hno)) (hp:PayFits Ω C hno a.domain p) :
    plusPayload Ω C hno (a.plusParam hT p hp) = p:=by
  cases p with
  | none => rfl
  | some v =>
    cases v with
    | plain p => rfl
    | minus m => rfl
    | plus v => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))
@[simp] theorem minusPayload_parameter (hT:FreeL P C (Ω.profile T.type) true)
    (p:Option (RawValue (hw:=hw) Ω C hno)) (hp:PayFits Ω C hno a.domain p) :
    minusPayload Ω C hno (a.minusParam hT p hp) = p:=by
  cases p with
  | none => rfl
  | some v =>
    cases v with
    | plain p => rfl
    | plus m => rfl
    | minus v => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))
end FrameKey
noncomputable def exitValue (T:ActTy Ω C) (out:Option (PlainValue (hw:=hw) Ω C hno)) :
    Value (hw:=hw) Ω C hno T.type :=
  match out with
  | none => distinguished (hw:=hw) Ω C hno T
  | some p => project (hw:=hw) Ω C hno T (.plain p)
noncomputable def plainApply (T:ActTy Ω C) (hT:PlainL P C (Ω.profile T.type))
    (v:Value (hw:=hw) Ω C hno T.type) (a:FrameKey Ω C T)
    (p:Option (RawValue (hw:=hw) Ω C hno)) (hp:PayFits Ω C hno a.domain p) :
    Value (hw:=hw) Ω C hno (a.target hw).type:=by
  let n:=T.plainNode hT
  let a':=a.plainKey hT
  let ps:=ActualPlainKey.parameters a' p hp
  exact Value.plain (a'.target hw)
    ((ActPlain.prefixEquiv (hw:=hw) hno (Base Ω) n (Value.asPlain n v)).2 a' ps)
noncomputable def applyValue (T:ActTy Ω C) (v:Value (hw:=hw) Ω C hno T.type)
    (a:FrameKey Ω C T) (p:Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno a.domain p):Value (hw:=hw) Ω C hno (a.target hw).type:=by
  by_cases hT:PlainL P C (Ω.profile T.type)
  · exact plainApply Ω C hno T hT v a p hp
  · by_cases hF:FreeL P C (Ω.profile T.type) false
    · let f:=Value.asPlus hF v
      let key:PlusFrame (hw:=hw) Ω C hno:=(a.argument,a.plusParam hF p hp)
      by_cases hA:PlainL P C (Ω.profile (a.target hw).type)
      · exact exitValue Ω C hno (a.target hw) (f.exiting ([],key))
      · exact ⟨.plus (f.slice key),a.free_target hF hA⟩
    · have hM:FreeL P C (Ω.profile T.type) true:=by
        rcases T.active.classify with h | h | h
        · exact False.elim (hT h)
        · exact False.elim (hF h)
        · exact h
      let f:=Value.asMinus hM v
      let key:MinusFrame (hw:=hw) Ω C hno:=(a.argument,a.minusParam hM p hp)
      by_cases hA:PlainL P C (Ω.profile (a.target hw).type)
      · exact exitValue Ω C hno (a.target hw) ((FreeObs.behavior _ _ _ _ f).exiting ([],key))
      · exact ⟨.minus (FreeObs.minusSlice f key),a.free_target hM hA⟩
end S_wpc_barendregt_geuvers_klop.ObsVals
namespace S_wpc_barendregt_geuvers_klop
universe u
namespace ObsVals
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
namespace ValEnv
variable {Ω C hno} {Γ:List (Expr S)} (e:ValEnv (hw:=hw) Ω C hno Γ)
noncomputable abbrev actualType {M T:Expr S} (h:HasType P Γ M T):ActualType Ω :=
  ⟨(T.subst e.images).nfTerm,(CTower.HasType.subst h e.typed).actual_type hw⟩
noncomputable abbrev activeType {M T:Expr S} (h:HasType P Γ M T)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)):ActTy Ω C :=
  .ofActual (e.actualType h) ha
noncomputable abbrev actualExpression {M:Expr S} {s:S} (h:HasType P Γ M (.sort s)):ActualType Ω :=
  ⟨(M.subst e.images).nfTerm,(CTower.HasType.subst h e.typed).actual_expression hw⟩
theorem type_convert_eq {M T N U:Expr S} (hM:HasType P Γ M T)
    (hN:HasType P Γ N U) (hc:Converts T U) :
    (T.subst e.images).nfTerm = (U.subst e.images).nfTerm :=
  Expr.nfTerm_converts ((CTower.HasType.subst hM e.typed).type_weakNorm hw)
    ((CTower.HasType.subst hN e.typed).type_weakNorm hw) (hc.subst _)
theorem expression_convert_eq {M T N U:Expr S} (hM:HasType P Γ M T)
    (hN:HasType P Γ N U) (hc:Converts M N) :
    (M.subst e.images).nfTerm = (N.subst e.images).nfTerm :=
  Expr.nfTerm_converts ((CTower.HasType.subst hM e.typed).weakNorm hw)
    ((CTower.HasType.subst hN e.typed).weakNorm hw) (hc.subst _)
end ValEnv
namespace ProdInst
variable {Ω C hno}
noncomputable def ofFormation {Γ:List (Expr S)} {D E:Expr S} {s:S}
    (hp:HasType P Γ (.pi D E) (.sort s)) (e:ValEnv (hw:=hw) Ω C hno Γ) :
    ProdInst (hw:=hw) Ω C hno :=
  let h:=hp.generation_pi
  { context:=Γ
    domain:=D
    body:=E
    domainSort:=h.choose
    bodySort:=h.choose_spec.choose
    resultSort:=h.choose_spec.choose_spec.choose
    domainTyping:=h.choose_spec.choose_spec.choose_spec.1
    bodyTyping:=h.choose_spec.choose_spec.choose_spec.2.1
    rule:=h.choose_spec.choose_spec.choose_spec.2.2.1
    environment:=e }
noncomputable def ofFunction {Γ:List (Expr S)} {f D E:Expr S}
    (hf:HasType P Γ f (.pi D E)) (e:ValEnv (hw:=hw) Ω C hno Γ) :
    ProdInst (hw:=hw) Ω C hno :=
  ofFormation hf.product_type_sorted.choose_spec e
variable (t:ProdInst (hw:=hw) Ω C hno)
theorem frame_domain {T:ActTy Ω C} (he:T.type = .pi t.domainNF t.bodyNF)
    (a:FrameKey Ω C T):a.domain = t.domainNF:=(Expr.pi.inj (a.product.symm.trans he)).1
theorem frame_body {T:ActTy Ω C} (he:T.type = .pi t.domainNF t.bodyNF)
    (a:FrameKey Ω C T):a.body = t.bodyNF:=(Expr.pi.inj (a.product.symm.trans he)).2
noncomputable def frameValEnv {T:ActTy Ω C} (he:T.type = .pi t.domainNF t.bodyNF)
    (a:FrameKey Ω C T) (p:Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno a.domain p):ValEnv (hw:=hw) Ω C hno (t.domain :: t.context) :=
  t.extend (t.frame_domain he a ▸ a.typed) p (t.frame_domain he a ▸ hp)
theorem frame_type {T:ActTy Ω C} (he:T.type = .pi t.domainNF t.bodyNF)
    (a:FrameKey Ω C T) (p:Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno a.domain p) :
    (t.body.subst (t.frameValEnv he a p hp).images).nfTerm = (a.target hw).type:=by
  change t.targetNF a.argument = (a.body.instantiate a.argument).nfTerm
  rw [t.target_eq (t.frame_domain he a ▸ a.typed),t.frame_body he a]
noncomputable def argumentFrame {T:ActTy Ω C} (he:T.type = .pi t.domainNF t.bodyNF)
    {n:Expr S} (hn:Ω.HasType n t.domainNF)
    (ha:ActL P C (Ω.profile (t.targetNF n))):FrameKey Ω C T where
  domain:=t.domainNF
  body:=t.bodyNF
  product:=he
  argument:=n.nfTerm
  normal:=(Expr.nfTerm_spec (hn.weakNorm hw)).2
  typed:=hn.nfTerm hw
  active:=by
    have h1:(t.bodyNF.instantiate n).nfTerm = (t.bodyNF.instantiate n.nfTerm).nfTerm:=by
      have hs:=t.target_typed hn
      have hn':=hn.nfTerm hw
      have hs':=t.target_typed hn'
      rw [t.target_eq hn] at hs
      rw [t.target_eq hn'] at hs'
      obtain ⟨s,hb⟩:=Ω.frame_target_sorted t.product_typed hn
      obtain ⟨s',hb'⟩:=Ω.frame_target_sorted t.product_typed hn'
      exact Expr.nfTerm_converts (hb.weakNorm hw) (hb'.weakNorm hw)
        ((Expr.nfTerm_spec (hn.weakNorm hw)).1.converts.instantiate_right t.bodyNF)
    rw [t.target_eq hn,h1] at ha
    simpa only [CTower.profile_nfTerm] using ha
theorem argumentFrame_type {T:ActTy Ω C} (he:T.type = .pi t.domainNF t.bodyNF)
    {n:Expr S} (hn:Ω.HasType n t.domainNF)
    (ha:ActL P C (Ω.profile (t.targetNF n))) :
    ((t.argumentFrame he hn ha).target hw).type = t.targetNF n:=by
  change (t.bodyNF.instantiate n.nfTerm).nfTerm = t.targetNF n
  rw [t.target_eq hn]
  obtain ⟨s,hb⟩:=Ω.frame_target_sorted t.product_typed hn
  obtain ⟨s',hb'⟩:=Ω.frame_target_sorted t.product_typed (hn.nfTerm hw)
  exact Expr.nfTerm_converts (hb'.weakNorm hw) (hb.weakNorm hw)
    (.symm _ _ ((Expr.nfTerm_spec (hn.weakNorm hw)).1.converts.instantiate_right t.bodyNF))
end ProdInst
end ObsVals
end S_wpc_barendregt_geuvers_klop
namespace S_wpc_barendregt_geuvers_klop.ObsVals
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
namespace PayFits
variable {Ω C hno} {T:Expr S} {p:Option (RawValue (hw:=hw) Ω C hno)}
noncomputable def value (hp:PayFits Ω C hno T p) (ha:ActL P C (Ω.profile T)) :
    Value (hw:=hw) Ω C hno T:=by
  cases p with
  | none => exact False.elim (hp ha)
  | some v => exact ⟨v,hp⟩
theorem value_spec (hp:PayFits Ω C hno T p) (ha:ActL P C (Ω.profile T)) :
    some (hp.value ha).val = p:=by
  cases p with
  | none => exact False.elim (hp ha)
  | some v => rfl
end PayFits
structure PreRes {Γ:List (Expr S)} (M T:Expr S) (e:ValEnv (hw:=hw) Ω C hno Γ) where
  val:ActL P C (Ω.profile (T.subst e.images).nfTerm) →
    Value (hw:=hw) Ω C hno (T.subst e.images).nfTerm
  read:Candidate Ω (M.subst e.images).nfTerm
namespace PreRes
variable {Ω C hno} {Γ:List (Expr S)} {M T:Expr S} {e:ValEnv (hw:=hw) Ω C hno Γ}
noncomputable def parameter (r:PreRes Ω C hno M T e):Option (RawValue (hw:=hw) Ω C hno) :=
  if ha:ActL P C (Ω.profile (T.subst e.images).nfTerm) then some (r.val ha).val else none
theorem parameter_fits (r:PreRes Ω C hno M T e) :
    PayFits Ω C hno (T.subst e.images).nfTerm r.parameter:=by
  unfold parameter
  split
  · exact (r.val _).property
  · assumption
noncomputable def baseRead (h:HasType P Γ M T)
    (v:ActL P C (Ω.profile (T.subst e.images).nfTerm) →
      Value (hw:=hw) Ω C hno (T.subst e.images).nfTerm) :
    Candidate Ω (M.subst e.images).nfTerm :=
  if _hm:Ω.profile (M.subst e.images).nfTerm ∈ C then
    if hs:∃ s:S,T = .sort s ∧ ({s}:Set S) ∈ C then
      if ha:ActL P C (Ω.profile (T.subst e.images).nfTerm) then
        (RawValue.base Ω C hno (v ha).val) (e.actualExpression (hs.choose_spec.1 ▸ h))
      else ⟨_,Cands.top_candidate⟩
    else ⟨_,Cands.top_candidate⟩
  else ⟨_,Cands.top_candidate⟩
noncomputable def baseResult (h:HasType P Γ M T)
    (v:ActL P C (Ω.profile (T.subst e.images).nfTerm) →
      Value (hw:=hw) Ω C hno (T.subst e.images).nfTerm):PreRes Ω C hno M T e :=
  ⟨v,baseRead h v⟩
noncomputable def lookup {n:Nat} {A:Expr S} (h:HasType P Γ (.var n) T)
    (hd:Lookup Γ n A) (hc:Converts T A) (e:ValEnv (hw:=hw) Ω C hno Γ) :
    PreRes Ω C hno (.var n) T e:=by
  apply baseResult h
  intro ha
  have he:(T.subst e.images).nfTerm = (A.subst e.images).nfTerm :=
    e.type_convert_eq h (HasType.lookup h.valid hd) hc
  have hp:=e.lawful n A hd
  rw [← he] at hp
  exact hp.value ha
noncomputable def sort {s t:S} (h:HasType P Γ (.sort s) T)
    (_ha:P.sortAxioms s t) (_hc:Converts T (.sort t))
    (e:ValEnv (hw:=hw) Ω C hno Γ):PreRes Ω C hno (.sort s) T e where
  val ha:=distinguished Ω C hno (e.activeType h ha)
  read:=⟨_,Cands.top_candidate⟩
noncomputable abbrev productData {D E:Expr S} {a b c:S}
    (hd:HasType P Γ D (.sort a)) (hb:HasType P (D :: Γ) E (.sort b))
    (hr:P.rule a b c) (e:ValEnv (hw:=hw) Ω C hno Γ) :
    ProdInst (hw:=hw) Ω C hno:=⟨Γ,D,E,a,b,c,hd,hb,hr,e⟩
noncomputable def productCandidate {D E:Expr S} {a b c:S}
    (hd:HasType P Γ D (.sort a)) (hb:HasType P (D :: Γ) E (.sort b))
    (hr:P.rule a b c)
    (ed:∀ e:ValEnv (hw:=hw) Ω C hno Γ,PreRes Ω C hno D (.sort a) e)
    (eb:∀ e:ValEnv (hw:=hw) Ω C hno (D :: Γ),PreRes Ω C hno E (.sort b) e)
    (e:ValEnv (hw:=hw) Ω C hno Γ):Candidate Ω (Expr.pi D E |>.subst e.images).nfTerm:=by
  let t:=productData hd hb hr e
  let pc:=t.candidate (ed e).read (fun n hn p hp => (eb (t.extend hn p hp)).read)
  exact ⟨pc.val,t.product_nf.symm ▸ pc.property⟩
noncomputable def product {D E:Expr S} {a b c:S} (h:HasType P Γ (.pi D E) T)
    (hd:HasType P Γ D (.sort a)) (hb:HasType P (D :: Γ) E (.sort b))
    (hr:P.rule a b c) (_hc:Converts T (.sort c))
    (ed:∀ e:ValEnv (hw:=hw) Ω C hno Γ,PreRes Ω C hno D (.sort a) e)
    (eb:∀ e:ValEnv (hw:=hw) Ω C hno (D :: Γ),PreRes Ω C hno E (.sort b) e)
    (e:ValEnv (hw:=hw) Ω C hno Γ):PreRes Ω C hno (.pi D E) T e:=by
  let pc:=productCandidate hd hb hr ed eb e
  refine ⟨?_,?_⟩
  · intro ha
    if hh:({c}:Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst e.images).nfTerm ∈ C then
      exact withBase Ω C hno (e.activeType h ha)
        (Base.update Ω (topBase Ω) (e.actualExpression (.product hd hb hr)) pc)
    else exact distinguished Ω C hno (e.activeType h ha)
  · exact if Ω.profile (Expr.pi D E |>.subst e.images).nfTerm ∈ C then pc
      else ⟨_,Cands.top_candidate⟩
noncomputable def abstractionAction {D m E:Expr S} {s:S} (h:HasType P Γ (.lam D m) T)
    (hp:HasType P Γ (.pi D E) (.sort s)) (hc:Converts T (.pi D E))
    (eb:∀ e:ValEnv (hw:=hw) Ω C hno (D :: Γ),PreRes Ω C hno m E e)
    (e:ValEnv (hw:=hw) Ω C hno Γ) (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)) :
    LambdaAction (hw:=hw) Ω C hno (e.activeType h ha):=by
  let t:=ProdInst.ofFormation hp e
  let A:=e.activeType h ha
  have he:A.type = .pi t.domainNF t.bodyNF:=by
    exact (Expr.nfTerm_converts ((CTower.HasType.subst h e.typed).type_weakNorm hw)
      ((CTower.HasType.subst hp e.typed).weakNorm hw) (hc.subst e.images)).trans t.product_nf
  intro k p hk
  let e':=t.frameValEnv he k p hk
  have he':(E.subst e'.images).nfTerm = (k.target hw).type:=t.frame_type he k p hk
  have ha':ActL P C (Ω.profile (E.subst e'.images).nfTerm):=he' ▸ (k.target hw).active
  exact ⟨((eb e').val ha').val,he' ▸ ((eb e').val ha').property⟩
noncomputable def abstraction {D m E:Expr S} {s:S} (h:HasType P Γ (.lam D m) T)
    (hp:HasType P Γ (.pi D E) (.sort s)) (hc:Converts T (.pi D E))
    (eb:∀ e:ValEnv (hw:=hw) Ω C hno (D :: Γ),PreRes Ω C hno m E e)
    (e:ValEnv (hw:=hw) Ω C hno Γ):PreRes Ω C hno (.lam D m) T e :=
  baseResult h fun ha => lambdaValue Ω C hno (e.activeType h ha) (abstractionAction h hp hc eb e ha)
noncomputable def applicationValue {f n D E:Expr S} (h:HasType P Γ (.app f n) T)
    (hf:HasType P Γ f (.pi D E)) (hn:HasType P Γ n D) (hc:Converts T (E.instantiate n))
    (ef:∀ e:ValEnv (hw:=hw) Ω C hno Γ,PreRes Ω C hno f (.pi D E) e)
    (en:∀ e:ValEnv (hw:=hw) Ω C hno Γ,PreRes Ω C hno n D e)
    (e:ValEnv (hw:=hw) Ω C hno Γ) (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)) :
    Value (hw:=hw) Ω C hno (T.subst e.images).nfTerm:=by
  let Ta:=e.activeType h ha
  by_cases hF:ActL P C (Ω.profile (Expr.pi D E |>.subst e.images).nfTerm)
  · let t:=ProdInst.ofFunction hf e
    let Fa:=e.activeType hf hF
    have he:Fa.type = .pi t.domainNF t.bodyNF:=t.product_nf
    have hn':Ω.HasType (n.subst e.images) t.domainNF :=
      (CTower.HasType.subst hn e.typed).normalize_type hw
    have ht:(T.subst e.images).nfTerm = t.targetNF (n.subst e.images):=by
      have hh:=e.type_convert_eq h (HasType.application hf hn) hc
      simpa only [ProdInst.targetNF,ProdInst.rawTarget,
        t,ProdInst.ofFunction,ProdInst.ofFormation,
        ← Expr.instantiate_subst,Expr.instantiate_liftSub] using hh
    have ha':ActL P C (Ω.profile (t.targetNF (n.subst e.images))):=ht ▸ ha
    let k:=t.argumentFrame he hn' ha'
    have hk:(k.target hw).type = (T.subst e.images).nfTerm :=
      (t.argumentFrame_type he hn' ha').trans ht.symm
    let v:=applyValue Ω C hno Fa ((ef e).val hF) k (en e).parameter (en e).parameter_fits
    exact ⟨v.val,hk ▸ v.property⟩
  · exact distinguished Ω C hno Ta
noncomputable def application {f n D E:Expr S} (h:HasType P Γ (.app f n) T)
    (hf:HasType P Γ f (.pi D E)) (hn:HasType P Γ n D) (hc:Converts T (E.instantiate n))
    (ef:∀ e:ValEnv (hw:=hw) Ω C hno Γ,PreRes Ω C hno f (.pi D E) e)
    (en:∀ e:ValEnv (hw:=hw) Ω C hno Γ,PreRes Ω C hno n D e)
    (e:ValEnv (hw:=hw) Ω C hno Γ):PreRes Ω C hno (.app f n) T e :=
  baseResult h fun ha => applicationValue h hf hn hc ef en e ha
end PreRes
noncomputable def preEval {Γ:List (Expr S)} {M T:Expr S} (t:TyTree P Γ M T) :
    ∀ e:ValEnv (hw:=hw) Ω C hno Γ,PreRes Ω C hno M T e:=by
  induction t with
  | var h hd hc => exact PreRes.lookup h hd hc
  | sort h ha hc => exact PreRes.sort h ha hc
  | product h d b hr hc ihd ihb => exact PreRes.product h d.typing b.typing hr hc ihd ihb
  | abstraction h d b hp hc ihd ihb => exact PreRes.abstraction h hp hc ihb
  | application h f a hc ihf iha => exact PreRes.application h f.typing a.typing hc ihf iha
end S_wpc_barendregt_geuvers_klop.ObsVals
end OMA
namespace OMA
namespace S_wpc_barendregt_geuvers_klop.ObsVals
section
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
namespace RawValue
variable {Ω C hno}
theorem level_symm {n:Nat} {v w:RawValue (hw:=hw) Ω C hno}
    (he:LevelEq Ω C hno n v w):LevelEq Ω C hno n w v:=by
  cases v <;> cases w <;> try exact False.elim he
  · exact Eq.symm he
  · exact FreeObs.Agree.symm he
  · exact Eq.symm he
theorem level_fits {n:Nat} {T:Expr S} {v w:RawValue (hw:=hw) Ω C hno}
    (he:LevelEq Ω C hno n v w):Fits Ω C hno T v ↔ Fits Ω C hno T w:=by
  cases v <;> cases w <;> try exact False.elim he
  · exact he ▸ Iff.rfl
  · rfl
  · rfl
theorem level_eq_of_plain {n:Nat} {T:Expr S} (hT:PlainL P C (Ω.profile T))
    {v w:RawValue (hw:=hw) Ω C hno} (hv:Fits Ω C hno T v)
    (he:LevelEq Ω C hno n v w):v = w:=by
  cases v with
  | plus p => exact False.elim (hv.1 hT)
  | minus p => exact False.elim (hv.1 hT)
  | plain p =>
    cases w with
    | plain q => exact congrArg RawValue.plain he
    | plus _ | minus _ => exact False.elim he
theorem bounded_of_not_minus {n:Nat} {T:Expr S}
    (hT:¬ FreeL P C (Ω.profile T) true)
    {v:RawValue (hw:=hw) Ω C hno} (hv:Fits Ω C hno T v):Bounded Ω C hno n v:=by
  cases v with
  | plain _ | plus _ => trivial
  | minus _ => exact False.elim (hT hv)
end RawValue
namespace Param
variable {Ω C hno}
theorem level_symm {n:Nat} {p q:Option (RawValue (hw:=hw) Ω C hno)}
    (he:LevelEq Ω C hno n p q):LevelEq Ω C hno n q p:=by
  cases p <;> cases q <;> try exact he
  exact RawValue.level_symm he
theorem level_fits {n:Nat} {T:Expr S} {p q:Option (RawValue (hw:=hw) Ω C hno)}
    (he:LevelEq Ω C hno n p q):PayFits Ω C hno T p ↔ PayFits Ω C hno T q:=by
  cases p <;> cases q <;> try exact False.elim he
  · rfl
  · exact RawValue.level_fits he
theorem bounded_of_not_minus {n:Nat} {T:Expr S}
    (hT:¬ FreeL P C (Ω.profile T) true)
    {p:Option (RawValue (hw:=hw) Ω C hno)} (hp:PayFits Ω C hno T p):Bounded Ω C hno n p:=by
  intro v hv
  subst p
  exact RawValue.bounded_of_not_minus hT hp
theorem bounded_none (n:Nat):Bounded (hw:=hw) Ω C hno n none:=fun _ h => by cases h
end Param
namespace Value
variable {Ω C hno}
theorem level_asPlus {n:Nat} {T:Expr S} (hT:FreeL P C (Ω.profile T) false)
    {v w:Value (hw:=hw) Ω C hno T}
    (he:RawValue.LevelEq Ω C hno n v.val w.val) :
    FreeObs.Agree n (asPlus hT v) (asPlus hT w):=by
  rw [asPlus_spec hT v,asPlus_spec hT w] at he
  exact he
theorem level_asMinus {n:Nat} {T:Expr S} (hT:FreeL P C (Ω.profile T) true)
    {v w:Value (hw:=hw) Ω C hno T}
    (he:RawValue.LevelEq Ω C hno n v.val w.val):asMinus hT v = asMinus hT w:=by
  rw [asMinus_spec hT v,asMinus_spec hT w] at he
  exact he
theorem bounded_asMinus {n:Nat} {T:Expr S} (hT:FreeL P C (Ω.profile T) true)
    {v:Value (hw:=hw) Ω C hno T} (hv:RawValue.Bounded Ω C hno n v.val) :
    FreeObs.InStage n (asMinus hT v):=by
  rw [asMinus_spec hT v] at hv
  exact hv
end Value
theorem distinguished_bounded (T:ActTy Ω C) :
    RawValue.Bounded Ω C hno 1 (distinguished (hw:=hw) Ω C hno T).val:=by
  unfold distinguished
  split
  · trivial
  · split
    · trivial
    · exact ⟨_,rfl⟩
theorem withBase_bounded (T:ActTy Ω C) (b:Base Ω) :
    RawValue.Bounded Ω C hno 1 (withBase (hw:=hw) Ω C hno T b).val:=by
  unfold withBase
  split
  · trivial
  · split
    · trivial
    · exact ⟨_,rfl⟩
namespace Gate
variable {Ω C hno}
theorem level_iff {n:Nat} {T:ActTy Ω C} {q:Expr S} {e:Bool}
    {p p':Option (RawValue (hw:=hw) Ω C hno)} (he:Param.LevelEq Ω C hno n p p') :
    Gate Ω C hno T q p e ↔ Gate Ω C hno T q p' e:=by
  constructor
  · rintro ⟨a,ha,hp,hf⟩
    exact ⟨a,ha,(Param.level_fits he).mp hp,hf⟩
  · rintro ⟨a,ha,hp,hf⟩
    exact ⟨a,ha,(Param.level_fits he).mpr hp,hf⟩
end Gate
theorem plusPayload_bounded {n:Nat} (a:PlusFrame (hw:=hw) Ω C hno)
    (ha:FreeObs.FrameBound n a):Param.Bounded Ω C hno n (plusPayload Ω C hno a.2):=by
  rcases a with ⟨q,p⟩
  cases p with
  | none => exact Param.bounded_none n
  | plain p => intro v hv; cases hv; trivial
  | opposite p => intro v hv; cases hv; exact ha p rfl
theorem minusPayload_bounded (n:Nat) (a:MinusFrame (hw:=hw) Ω C hno) :
    Param.Bounded Ω C hno n (minusPayload Ω C hno a.2):=by
  rcases a with ⟨q,p⟩
  cases p with
  | none => exact Param.bounded_none n
  | plain p | opposite p => intro v hv; cases hv; trivial
theorem minusFrame_restrict {n:Nat} {a a':MinusFrame (hw:=hw) Ω C hno}
    (ha:FreeObs.mapFrame (FreeObs.restrict _ _ _ _ n) a =
      FreeObs.mapFrame (FreeObs.restrict _ _ _ _ n) a') :
    a.1 = a'.1 ∧ Param.LevelEq Ω C hno n (minusPayload Ω C hno a.2) (minusPayload Ω C hno a'.2):=by
  rcases a with ⟨q,p⟩
  rcases a' with ⟨q',p'⟩
  have hh:=Prod.mk.inj ha
  refine ⟨hh.1,?_⟩
  cases p <;> cases p' <;> dsimp only [FreeObs.Payload.map,minusPayload,
    Param.LevelEq,RawValue.LevelEq] at hh ⊢
  all_goals first | exact True.intro | exact FreeObs.Payload.plain.inj hh.2 |
    exact FreeObs.Payload.opposite.inj hh.2 | cases hh.2
def ActionBound (T:ActTy Ω C) (k l:Nat) (act:LambdaAction (hw:=hw) Ω C hno T):Prop :=
  ∀ a p hp,Param.Bounded Ω C hno k p → RawValue.Bounded Ω C hno l (act a p hp).val
def ActionRelated (T:ActTy Ω C) (k l:Nat)
    (act act':LambdaAction (hw:=hw) Ω C hno T):Prop :=
  ∀ a p p' hp hp',Param.Bounded Ω C hno k p → Param.Bounded Ω C hno k p' →
    Param.LevelEq Ω C hno l p p' → RawValue.LevelEq Ω C hno k (act a p hp).val (act' a p' hp').val
namespace LambdaAction
variable {Ω C hno}
theorem frame_congr {T:ActTy Ω C} (act:LambdaAction (hw:=hw) Ω C hno T)
    {a b:FrameKey Ω C T} (he:a = b) (p:Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno a.domain p) (hq:PayFits Ω C hno b.domain p) :
    (act a p hp).val = (act b p hq).val:=by
  cases he
  rfl
end LambdaAction
namespace ActionRelated
variable {Ω C hno}
theorem gates {T:ActTy Ω C} {k l:Nat} {act act':LambdaAction (hw:=hw) Ω C hno T}
    (hr:ActionRelated Ω C hno T k l act act')
    {q q':Expr S} (hq:q = q') {ex:Bool}
    {p p':Option (RawValue (hw:=hw) Ω C hno)}
    (h:Gate Ω C hno T q p ex) (h':Gate Ω C hno T q' p' ex)
    (hb:Param.Bounded Ω C hno k p) (hb':Param.Bounded Ω C hno k p')
    (he:Param.LevelEq Ω C hno l p p') :
    RawValue.LevelEq Ω C hno k (act h.frame p h.payload).val (act' h'.frame p' h'.payload).val:=by
  have hf:h.frame = h'.frame:=FrameKey.ext (h.argument.trans (hq.trans h'.argument.symm))
  have hp':PayFits Ω C hno h.frame.domain p':=hf.symm ▸ h'.payload
  have hh:=hr h.frame p p' h.payload hp' hb hb' he
  rw [LambdaAction.frame_congr act' hf p' hp' h'.payload] at hh
  exact hh
end ActionRelated
theorem minusContinue_bounded {T:ActTy Ω C}
    (hT:FreeL P C (Ω.profile T.type) true) {k l:Nat} (hl:1 ≤ l)
    {act:LambdaAction (hw:=hw) Ω C hno T} (hb:ActionBound Ω C hno T k l act)
    (a:MinusFrame (hw:=hw) Ω C hno) :
    FreeObs.InStage l (minusContinue Ω C hno T hT act a):=by
  unfold minusContinue
  split
  · exact Value.bounded_asMinus _ (hb _ _ _ (minusPayload_bounded Ω C hno k a))
  · exact FreeObs.InStage.mono hl ⟨_,rfl⟩
theorem minusContinue_level {T:ActTy Ω C}
    (hT:FreeL P C (Ω.profile T.type) true) {k l:Nat}
    {act act':LambdaAction (hw:=hw) Ω C hno T} (hr:ActionRelated Ω C hno T k l act act')
    {a a':MinusFrame (hw:=hw) Ω C hno}
    (ha:FreeObs.mapFrame (FreeObs.restrict _ _ _ _ l) a =
      FreeObs.mapFrame (FreeObs.restrict _ _ _ _ l) a') :
    minusContinue Ω C hno T hT act a = minusContinue Ω C hno T hT act' a':=by
  have hh:=minusFrame_restrict Ω C hno ha
  have hg:Gate Ω C hno T a.1 (minusPayload Ω C hno a.2) false ↔
      Gate Ω C hno T a'.1 (minusPayload Ω C hno a'.2) false:=by
    rw [hh.1]
    exact Gate.level_iff hh.2
  unfold minusContinue
  by_cases h:Gate Ω C hno T a.1 (minusPayload Ω C hno a.2) false
  · have h':=hg.mp h
    rw [dif_pos h,dif_pos h']
    have he:=hr.gates hh.1 h h' (minusPayload_bounded Ω C hno k a)
      (minusPayload_bounded Ω C hno k a') hh.2
    rw [Value.asMinus_spec (h.frame.free_target hT h.not_plain) (act _ _ _),
      Value.asMinus_spec (h'.frame.free_target hT h'.not_plain) (act' _ _ _)] at he
    exact he
  · rw [dif_neg h,dif_neg (mt hg.mpr h)]
theorem lambdaExit_level {X:Type u}
    (decode:FreeObs.Payload (PlainValue (hw:=hw) Ω C hno) X →
      Option (RawValue (hw:=hw) Ω C hno))
    {T:ActTy Ω C} {k l:Nat} {act act':LambdaAction (hw:=hw) Ω C hno T}
    (hr:ActionRelated Ω C hno T k l act act')
    {a a':FreeObs.Frame (Expr S) (PlainValue (hw:=hw) Ω C hno) X}
    (hq:a.1 = a'.1) (hb:Param.Bounded Ω C hno k (decode a.2))
    (hb':Param.Bounded Ω C hno k (decode a'.2))
    (he:Param.LevelEq Ω C hno l (decode a.2) (decode a'.2)) :
    lambdaExit Ω C hno decode T act a = lambdaExit Ω C hno decode T act' a':=by
  have hg:Gate Ω C hno T a.1 (decode a.2) true ↔ Gate Ω C hno T a'.1 (decode a'.2) true:=by
    rw [hq]
    exact Gate.level_iff he
  unfold lambdaExit
  by_cases h:Gate Ω C hno T a.1 (decode a.2) true
  · have h':=hg.mp h
    rw [dif_pos h,dif_pos h']
    have hh:=hr.gates hq h h' hb hb' he
    rw [← tagPlain_spec Ω C hno (h.frame.target hw) h.plain (act _ _ _),
      ← tagPlain_spec Ω C hno (h'.frame.target hw) h'.plain (act' _ _ _)] at hh
    exact congrArg some hh
  · rw [dif_neg h,dif_neg (mt hg.mpr h)]
theorem minusLambda_representable {T:ActTy Ω C}
    (hT:FreeL P C (Ω.profile T.type) true) {k l:Nat} (hl:1 ≤ l)
    {act:LambdaAction (hw:=hw) Ω C hno T} (hb:ActionBound Ω C hno T k l act)
    (hr:ActionRelated Ω C hno T k l act act) :
    ∃ x,FreeObs.InStage (l+1) x ∧
      FreeObs.behavior _ _ _ _ x = minusLambdaBehavior Ω C hno T hT act:=by
  apply FreeObs.lambdaTable_representable (topBase Ω) none l
  · intro a
    exact (minusContinue_bounded Ω C hno hT hl hb a).mono (Nat.le_succ l)
  · intro a a' ha
    exact minusContinue_level Ω C hno hT hr ha
  · intro a a' ha
    have hh:=minusFrame_restrict Ω C hno ha
    exact lambdaExit_level Ω C hno (minusPayload Ω C hno) hr hh.1
      (minusPayload_bounded Ω C hno k a) (minusPayload_bounded Ω C hno k a') hh.2
namespace Value
variable {Ω C hno}
theorem level_asPlain {n:Nat} (T:ActPlain.Node Ω C)
    {v w:Value (hw:=hw) Ω C hno T.type}
    (he:RawValue.LevelEq Ω C hno n v.val w.val):asPlain T v = asPlain T w:=by
  have hh:v = w:=Subtype.ext (RawValue.level_eq_of_plain T.plain v.property he)
  exact congrArg (asPlain T) hh
end Value
namespace ActualPlainKey
variable {Ω C hno}
theorem payload_bounded {T:ActPlain.Node Ω C} (a:ActPlain.Key Ω C T)
    (p:(ActPlain.schema hw).FrameParams (ActPlain.Space (hw:=hw) hno (Base Ω)) a)
    (k:Nat):Param.Bounded Ω C hno k (payload a p):=by
  unfold payload
  split
  · intro v hv
    cases hv
    trivial
  · exact Param.bounded_none k
end ActualPlainKey
theorem plainLambda_level {T:ActTy Ω C} (hT:PlainL P C (Ω.profile T.type))
    {k l:Nat} {act act':LambdaAction (hw:=hw) Ω C hno T}
    (hr:ActionRelated Ω C hno T k l act act') :
    RawValue.LevelEq Ω C hno k (plainLambda Ω C hno T hT act).val
      (plainLambda Ω C hno T hT act').val:=by
  unfold plainLambda
  change Sigma.mk _ _ = Sigma.mk _ _
  congr 1
  apply congrArg (ActPlain.prefixEquiv (hw:=hw) hno (Base Ω) (T.plainNode hT)).symm
  apply Prod.ext
  · rfl
  funext a p
  apply Value.level_asPlain
  exact hr _ _ _ _ _ (ActualPlainKey.payload_bounded a p k)
    (ActualPlainKey.payload_bounded a p k) (Param.level_refl l _)
theorem plusContinue_level {T:ActTy Ω C}
    (hT:FreeL P C (Ω.profile T.type) false) {k l:Nat}
    {act act':LambdaAction (hw:=hw) Ω C hno T} (hr:ActionRelated Ω C hno T k l act act')
    (a:PlusFrame (hw:=hw) Ω C hno) (ha:FreeObs.FrameBound k a) :
    FreeObs.Agree k (plusContinue Ω C hno T hT act a) (plusContinue Ω C hno T hT act' a):=by
  unfold plusContinue
  split
  · exact Value.level_asPlus _ (hr _ _ _ _ _ (plusPayload_bounded Ω C hno a ha)
      (plusPayload_bounded Ω C hno a ha) (Param.level_refl l _))
  · exact .refl _ _
theorem plusLambda_level {T:ActTy Ω C}
    (hT:FreeL P C (Ω.profile T.type) false) {k l:Nat}
    {act act':LambdaAction (hw:=hw) Ω C hno T} (hr:ActionRelated Ω C hno T k l act act') :
    FreeObs.Agree k (plusLambda Ω C hno T hT act) (plusLambda Ω C hno T hT act'):=by
  apply FreeObs.Agree.of_observations
  · intro as has
    cases as with
    | nil => rfl
    | cons a as =>
      exact (plusContinue_level Ω C hno hT hr a (has a List.mem_cons_self)).continuing
        (fun x hx => has x (List.mem_cons_of_mem _ hx))
  · rintro ⟨as,e⟩ ⟨has,hes⟩
    cases as with
    | nil =>
      exact lambdaExit_level Ω C hno (plusPayload Ω C hno) hr rfl
        (plusPayload_bounded Ω C hno e hes) (plusPayload_bounded Ω C hno e hes) (Param.level_refl l _)
    | cons a as =>
      exact (plusContinue_level Ω C hno hT hr a (has a List.mem_cons_self)).exiting
        ⟨fun x hx => has x (List.mem_cons_of_mem _ hx),hes⟩
theorem minusLambdaBehavior_level {T:ActTy Ω C}
    (hT:FreeL P C (Ω.profile T.type) true) {k l:Nat}
    {act act':LambdaAction (hw:=hw) Ω C hno T} (hr:ActionRelated Ω C hno T k l act act') :
    minusLambdaBehavior Ω C hno T hT act = minusLambdaBehavior Ω C hno T hT act':=by
  unfold minusLambdaBehavior
  congr 1
  · funext a
    exact minusContinue_level Ω C hno hT hr rfl
  · funext a
    exact lambdaExit_level Ω C hno (minusPayload Ω C hno) hr rfl
      (minusPayload_bounded Ω C hno k a) (minusPayload_bounded Ω C hno k a) (Param.level_refl l _)
theorem lambdaValue_bounded {T:ActTy Ω C} {k l:Nat} (hl:1 ≤ l)
    {act:LambdaAction (hw:=hw) Ω C hno T} (hb:ActionBound Ω C hno T k l act)
    (hr:ActionRelated Ω C hno T k l act act) :
    RawValue.Bounded Ω C hno (l+1) (lambdaValue Ω C hno T act).val:=by
  unfold lambdaValue
  split
  · trivial
  · split
    · trivial
    · exact packMinus_stage Ω C hno _ (minusLambda_representable Ω C hno _ hl hb hr)
theorem lambdaValue_level {T:ActTy Ω C} {k l:Nat}
    {act act':LambdaAction (hw:=hw) Ω C hno T} (hr:ActionRelated Ω C hno T k l act act') :
    RawValue.LevelEq Ω C hno k (lambdaValue Ω C hno T act).val (lambdaValue Ω C hno T act').val:=by
  unfold lambdaValue
  split
  · exact plainLambda_level Ω C hno _ hr
  · split
    · exact plusLambda_level Ω C hno _ hr
    · exact congrArg (packMinus Ω C hno) (minusLambdaBehavior_level Ω C hno _ hr)
namespace RawValue
variable {Ω C hno}
theorem level_eq_of_not_plus {n:Nat} {T:Expr S} (hT:¬ FreeL P C (Ω.profile T) false)
    {v w:RawValue (hw:=hw) Ω C hno} (hv:Fits Ω C hno T v)
    (he:LevelEq Ω C hno n v w):v = w:=by
  cases v <;> cases w <;> dsimp only [LevelEq] at he
  all_goals first | exact False.elim he | exact False.elim (hT hv) |
    exact congrArg RawValue.plain he | exact congrArg RawValue.minus he
end RawValue
namespace Param
variable {Ω C hno}
theorem level_eq_of_not_plus {n:Nat} {T:Expr S} (hT:¬ FreeL P C (Ω.profile T) false)
    {p q:Option (RawValue (hw:=hw) Ω C hno)} (hp:PayFits Ω C hno T p)
    (he:LevelEq Ω C hno n p q):p = q:=by
  cases p <;> cases q
  · rfl
  · exact False.elim he
  · exact False.elim he
  · exact congrArg some (RawValue.level_eq_of_not_plus hT hp he)
end Param
theorem minusFrame_restrict_of_level {n:Nat} {a a':MinusFrame (hw:=hw) Ω C hno}
    (hq:a.1 = a'.1)
    (he:Param.LevelEq Ω C hno n (minusPayload Ω C hno a.2) (minusPayload Ω C hno a'.2)) :
    FreeObs.mapFrame (FreeObs.restrict _ _ _ _ n) a =
      FreeObs.mapFrame (FreeObs.restrict _ _ _ _ n) a':=by
  rcases a with ⟨q,p⟩
  rcases a' with ⟨q',p'⟩
  cases p <;> cases p' <;> dsimp only [minusPayload,Param.LevelEq,RawValue.LevelEq] at he
  all_goals first | exact False.elim he |
    exact Prod.ext hq rfl |
    exact Prod.ext hq (congrArg FreeObs.Payload.plain he) |
    exact Prod.ext hq (congrArg FreeObs.Payload.opposite he)
namespace FrameKey
variable {Ω C hno} {T:ActTy Ω C} (a:FrameKey Ω C T)
theorem plusParam_bound (hT:FreeL P C (Ω.profile T.type) false)
    {n:Nat} (p:Option (RawValue (hw:=hw) Ω C hno)) (hp:PayFits Ω C hno a.domain p)
    (hb:Param.Bounded Ω C hno n p) :
    FreeObs.FrameBound n (a.argument,a.plusParam hT p hp):=by
  cases p with
  | none => intro x hx; cases hx
  | some v =>
    cases v with
    | plain p => intro x hx; cases hx
    | plus p => exact False.elim (Bool.noConfusion (a.free_domain_sign hw hT hp))
    | minus p =>
      intro x hx
      have hh:p = x:=FreeObs.Payload.opposite.inj hx
      exact hh ▸ hb _ rfl
theorem minusParam_level (hT:FreeL P C (Ω.profile T.type) true)
    {n:Nat} (p p':Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno a.domain p) (hp':PayFits Ω C hno a.domain p')
    (he:Param.LevelEq Ω C hno n p p') :
    FreeObs.mapFrame (FreeObs.restrict _ _ _ _ n) (a.argument,a.minusParam hT p hp) =
      FreeObs.mapFrame (FreeObs.restrict _ _ _ _ n) (a.argument,a.minusParam hT p' hp'):=by
  apply minusFrame_restrict_of_level Ω C hno
  · rfl
  · simpa only [minusPayload_parameter] using he
end FrameKey
theorem applyValue_bounded {T:ActTy Ω C} {n:Nat} (v:Value (hw:=hw) Ω C hno T.type)
    (hv:RawValue.Bounded Ω C hno n v.val) (a:FrameKey Ω C T)
    (p:Option (RawValue (hw:=hw) Ω C hno)) (hp:PayFits Ω C hno a.domain p) :
    RawValue.Bounded Ω C hno n (applyValue Ω C hno T v a p hp).val:=by
  unfold applyValue
  split
  · trivial
  · split
    · split
      · rename_i ht
        exact RawValue.bounded_of_not_minus (fun h => h.1 ht) (exitValue Ω C hno _ _).property
      · trivial
    · split
      · rename_i ht
        exact RawValue.bounded_of_not_minus (fun h => h.1 ht) (exitValue Ω C hno _ _).property
      · exact FreeObs.inStage_minusSlice (topBase Ω) none (Value.bounded_asMinus _ hv) _
theorem applyValue_level {T:ActTy Ω C} {k j r:Nat}
    (v v':Value (hw:=hw) Ω C hno T.type) (hv:RawValue.Bounded Ω C hno j v.val)
    (hvv:RawValue.LevelEq Ω C hno (max k r) v.val v'.val) (a:FrameKey Ω C T)
    (p p':Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno a.domain p) (hp':PayFits Ω C hno a.domain p')
    (hb:Param.Bounded Ω C hno r p) (hpp:Param.LevelEq Ω C hno j p p') :
    RawValue.LevelEq Ω C hno k (applyValue Ω C hno T v a p hp).val
      (applyValue Ω C hno T v' a p' hp').val:=by
  unfold applyValue
  by_cases hT:PlainL P C (Ω.profile T.type)
  · rw [dif_pos hT,dif_pos hT]
    have hvv':v = v':=Subtype.ext (RawValue.level_eq_of_plain hT v.property hvv)
    have hpp':p = p':=Param.level_eq_of_not_plus
      (fun hf => hf.1 (a.plain_domain hw hT hf.active)) hp hpp
    subst v'
    subst p'
    exact RawValue.level_refl k _
  · rw [dif_neg hT,dif_neg hT]
    by_cases hF:FreeL P C (Ω.profile T.type) false
    · rw [dif_pos hF,dif_pos hF]
      have hpp':p = p':=Param.level_eq_of_not_plus
        (fun hf => Bool.noConfusion (a.free_domain_sign hw hF hf)) hp hpp
      subst p'
      have hh:=Value.level_asPlus hF hvv
      have ha:=(a.plusParam_bound hF p hp hb).mono (le_max_right k r)
      split
      · have he:=hh.exiting (as:=([],(a.argument,a.plusParam hF p hp)))
          ⟨fun x hx => False.elim (List.not_mem_nil hx),ha⟩
        dsimp only
        rw [he]
        exact RawValue.level_refl k _
      · exact hh.slice (le_max_left k r) _ ha
    · rw [dif_neg hF,dif_neg hF]
      have hM:FreeL P C (Ω.profile T.type) true:=by
        rcases T.active.classify with hh | hh | hh
        · exact False.elim (hT hh)
        · exact False.elim (hF hh)
        · exact hh
      have hh:=Value.level_asMinus hM hvv
      have hs:=(Value.bounded_asMinus hM hv).mono (Nat.le_succ j)
      have ha:=a.minusParam_level hM p p' hp hp' hpp
      split
      · dsimp only
        rw [← hh]
        have he:=FreeObs.minusExit_eq_of_restrict (topBase Ω) none hs ha
        rw [he]
        exact RawValue.level_refl k _
      · change FreeObs.minusSlice _ _ = FreeObs.minusSlice _ _
        rw [← hh]
        exact FreeObs.minusSlice_eq_of_restrict (topBase Ω) none hs ha
namespace ValEnv
variable {Ω C hno} {Γ:List (Expr S)}
theorem imageCompatible_symm {e f:ValEnv (hw:=hw) Ω C hno Γ} (he:e.ImageCompatible f) :
    f.ImageCompatible e:=fun n hn => (he n hn).symm
theorem level_symm {e f:ValEnv (hw:=hw) Ω C hno Γ} {k:Nat} (he:e.LevelEq k f) :
    f.LevelEq k e:=⟨imageCompatible_symm he.1,fun n hn => Param.level_symm (he.2 n hn)⟩
theorem level_cons {e f:ValEnv (hw:=hw) Ω C hno Γ} {k:Nat}
    (he:e.LevelEq k f) {A a b:Expr S} (ha:Ω.HasType a (A.subst e.images))
    (hb:Ω.HasType b (A.subst f.images)) (hab:Converts a b)
    (p q:Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno (A.subst e.images).nfTerm p)
    (hq:PayFits Ω C hno (A.subst f.images).nfTerm q)
    (hpq:Param.LevelEq Ω C hno k p q) :
    (e.cons ha p hp).LevelEq k (f.cons hb q hq):=by
  constructor
  · intro n hn
    cases n with
    | zero => exact hab
    | succ n => exact he.1 n (Nat.lt_of_succ_lt_succ hn)
  · intro n hn
    cases n with
    | zero => exact hpq
    | succ n => exact he.2 n (Nat.lt_of_succ_lt_succ hn)
end ValEnv
namespace Value
variable {Ω C hno}
@[simp] theorem cast_val {T U:Expr S} (h:T = U) (v:Value (hw:=hw) Ω C hno T) :
    (h ▸ v).val = v.val:=by subst U; rfl
end Value
theorem lambdaValue_level_of_type_eq {T U:ActTy Ω C} (hTU:T.type = U.type)
    {k l:Nat} (act:LambdaAction (hw:=hw) Ω C hno T)
    (act':LambdaAction (hw:=hw) Ω C hno U)
    (hr:∀ (a:FrameKey Ω C T) (a':FrameKey Ω C U),a.argument = a'.argument →
      ∀ p p' hp hp',Param.Bounded Ω C hno k p → Param.Bounded Ω C hno k p' →
      Param.LevelEq Ω C hno l p p' →
      RawValue.LevelEq Ω C hno k (act a p hp).val (act' a' p' hp').val) :
    RawValue.LevelEq Ω C hno k (lambdaValue Ω C hno T act).val (lambdaValue Ω C hno U act').val:=by
  have hu:=ActTy.ext hTU
  subst U
  exact lambdaValue_level Ω C hno (fun a p p' hp hp' hb hb' he => hr a a rfl p p' hp hp' hb hb' he)
theorem applyValue_level_of_type_eq {T U:ActTy Ω C} (hTU:T.type = U.type)
    {k j r:Nat} (v:Value (hw:=hw) Ω C hno T.type) (v':Value (hw:=hw) Ω C hno U.type)
    (hv:RawValue.Bounded Ω C hno j v.val)
    (hvv:RawValue.LevelEq Ω C hno (max k r) v.val v'.val)
    (a:FrameKey Ω C T) (a':FrameKey Ω C U) (hq:a.argument = a'.argument)
    (p p':Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno a.domain p) (hp':PayFits Ω C hno a'.domain p')
    (hb:Param.Bounded Ω C hno r p) (hpp:Param.LevelEq Ω C hno j p p') :
    RawValue.LevelEq Ω C hno k (applyValue Ω C hno T v a p hp).val
      (applyValue Ω C hno U v' a' p' hp').val:=by
  have hu:=ActTy.ext hTU
  subst U
  have ha:=FrameKey.ext hq
  subst a'
  exact applyValue_level Ω C hno v v' hv hvv a p p' hp hp' hb hpp
namespace PreRes
variable {Ω C hno} {Γ:List (Expr S)} {M T:Expr S}
variable {e f:ValEnv (hw:=hw) Ω C hno Γ}
theorem parameter_eq (r:PreRes Ω C hno M T e)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)) :
    r.parameter = some (r.val ha).val:=dif_pos ha
theorem parameter_bounded {k:Nat} (r:PreRes Ω C hno M T e)
    (hb:∀ ha,RawValue.Bounded Ω C hno k (r.val ha).val) :
    Param.Bounded Ω C hno k r.parameter:=by
  unfold parameter
  split
  · intro v hv
    exact Option.some.inj hv ▸ hb _
  · exact Param.bounded_none k
theorem val_bounded {k:Nat} (r:PreRes Ω C hno M T e)
    (hb:Param.Bounded Ω C hno k r.parameter)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)) :
    RawValue.Bounded Ω C hno k (r.val ha).val:=hb _ (r.parameter_eq ha)
theorem parameter_level {k:Nat} (r:PreRes Ω C hno M T e) (q:PreRes Ω C hno M T f)
    (ht:(T.subst e.images).nfTerm = (T.subst f.images).nfTerm)
    (hv:∀ ha hb,RawValue.LevelEq Ω C hno k (r.val ha).val (q.val hb).val) :
    Param.LevelEq Ω C hno k r.parameter q.parameter:=by
  unfold parameter
  by_cases ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)
  · have hb:=ht ▸ ha
    rw [dif_pos ha,dif_pos hb]
    exact hv ha hb
  · have hb:¬ ActL P C (Ω.profile (T.subst f.images).nfTerm):=ht ▸ ha
    rw [dif_neg ha,dif_neg hb]
    trivial
theorem val_level {k:Nat} (r:PreRes Ω C hno M T e) (q:PreRes Ω C hno M T f)
    (hr:Param.LevelEq Ω C hno k r.parameter q.parameter)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (hb:ActL P C (Ω.profile (T.subst f.images).nfTerm)) :
    RawValue.LevelEq Ω C hno k (r.val ha).val (q.val hb).val:=by
  rw [r.parameter_eq ha,q.parameter_eq hb] at hr
  exact hr
 theorem baseRead_level {k:Nat} (h:HasType P Γ M T) (he:e.ImageCompatible f)
    (v:ActL P C (Ω.profile (T.subst e.images).nfTerm) →
      Value (hw:=hw) Ω C hno (T.subst e.images).nfTerm)
    (w:ActL P C (Ω.profile (T.subst f.images).nfTerm) →
      Value (hw:=hw) Ω C hno (T.subst f.images).nfTerm)
    (hv:∀ ha hb,RawValue.LevelEq Ω C hno k (v ha).val (w hb).val) :
    (baseRead h v).val = (baseRead h w).val:=by
  have hM:=e.actual_expr_eq he h
  have hT:=e.actual_type_eq he h
  by_cases hm:Ω.profile (M.subst e.images).nfTerm ∈ C
  · have hm':Ω.profile (M.subst f.images).nfTerm ∈ C:=hM ▸ hm
    by_cases hs:∃ s:S,T = .sort s ∧ ({s}:Set S) ∈ C
    · by_cases ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)
      · have hb:ActL P C (Ω.profile (T.subst f.images).nfTerm):=hT ▸ ha
        simp only [baseRead,ValEnv.actualExpression,hm,hm',hs,ha,hb,dite_true]
        have hbase:=RawValue.level_base (hv ha hb)
        have hX:e.actualExpression (hs.choose_spec.1 ▸ h) =
            f.actualExpression (hs.choose_spec.1 ▸ h):=Subtype.ext hM
        dsimp only [ValEnv.actualExpression] at hX
        rw [hbase]
        exact congrArg (fun X:ActualType Ω => ((RawValue.base Ω C hno (w hb).val) X).val) hX
      · have hb:¬ ActL P C (Ω.profile (T.subst f.images).nfTerm):=hT ▸ ha
        simp only [baseRead,ValEnv.actualExpression,hm,hm',hs,ha,hb,dite_true,dite_false]
        exact congrArg (Cands.Top Ω) hM
    · simp only [baseRead,ValEnv.actualExpression,hm,hm',hs,dite_true,dite_false]
      exact congrArg (Cands.Top Ω) hM
  · have hm':Ω.profile (M.subst f.images).nfTerm ∉ C:=hM ▸ hm
    simp only [baseRead,ValEnv.actualExpression,hm,hm',dite_false]
    exact congrArg (Cands.Top Ω) hM
end PreRes
namespace ProdInst
variable {Ω C hno}
theorem domain_not_minus (t:ProdInst (hw:=hw) Ω C hno)
    (hC:IsComp (PriEdge P) C) {n:Expr S} (hn:Ω.HasType n t.domainNF)
    (hK:Ω.profile (.pi t.domainNF t.bodyNF) ∈ C) (hL:Ω.profile (t.targetNF n) ∈ C) :
    ¬ FreeL P C (Ω.profile t.domainNF) true:=by
  intro hm
  obtain ⟨J,hf,hp⟩:=Ω.frame_profiles hw t.product_typed hn
  have hL':Ω.profile (t.bodyNF.instantiate n) ∈ C:=by
    rw [t.target_eq hn,CTower.profile_nfTerm] at hL
    exact hL
  have hJ:=hC.between hL' hK hp.reach (.single (.codomain hf))
  exact Bool.noConfusion (hm.direct_sign ⟨hm.active.layer,J,hJ,_,hK,hf⟩)
theorem targetNF_eq {t t':ProdInst (hw:=hw) Ω C hno}
    (hD:t.domainNF = t'.domainNF) (hE:t.bodyNF = t'.bodyNF)
    {n:Expr S} (hn:Ω.HasType n t.domainNF):t.targetNF n = t'.targetNF n:=by
  rw [t.target_eq hn,t'.target_eq (hD ▸ hn),hE]
theorem testers_eq {t t':ProdInst (hw:=hw) Ω C hno}
    (hD:t.domainNF = t'.domainNF) (d:Candidate Ω t.domainNF) (d':Candidate Ω t'.domainNF)
    (hd:Ω.profile t.domainNF ∈ C → d.val = d'.val):t.testers d = t'.testers d':=by
  unfold testers
  by_cases hh:Ω.profile t.domainNF ∈ C
  · have hh':Ω.profile t'.domainNF ∈ C:=hD ▸ hh
    rw [if_pos hh,if_pos hh']
    exact hd hh
  · have hh':Ω.profile t'.domainNF ∉ C:=hD ▸ hh
    rw [if_neg hh,if_neg hh',hD]
theorem fibers_eq {t t':ProdInst (hw:=hw) Ω C hno}
    (hD:t.domainNF = t'.domainNF) (hE:t.bodyNF = t'.bodyNF)
    (b:t.BodyReads) (b':t'.BodyReads)
    (hb:∀ n hn p hp,Ω.profile (t.targetNF n) ∈ C →
        (b n hn p hp).val = (b' n (hD ▸ hn) p (hD ▸ hp)).val) :
    t.fibers b = t'.fibers b':=by
  funext n
  unfold fibers
  by_cases hn:Ω.HasType n t.domainNF
  · have hn':Ω.HasType n t'.domainNF:=hD ▸ hn
    rw [dif_pos hn,dif_pos hn']
    have ht:=targetNF_eq hD hE hn
    by_cases hc:Ω.profile (t.targetNF n) ∈ C
    · have hc':Ω.profile (t'.targetNF n) ∈ C:=ht ▸ hc
      rw [if_pos hc,if_pos hc']
      ext U
      constructor
      · rintro ⟨p,hp,rfl⟩
        exact ⟨p,hD ▸ hp,hb n hn p hp hc⟩
      · rintro ⟨p,hp,rfl⟩
        exact ⟨p,hD.symm ▸ hp,(hb n hn p (hD.symm ▸ hp) hc).symm⟩
    · have hc':Ω.profile (t'.targetNF n) ∉ C:=ht ▸ hc
      rw [if_neg hc,if_neg hc',ht]
  · have hn':¬ Ω.HasType n t'.domainNF:=hD ▸ hn
    rw [dif_neg hn,dif_neg hn']
theorem candidate_eq {t t':ProdInst (hw:=hw) Ω C hno}
    (hD:t.domainNF = t'.domainNF) (hE:t.bodyNF = t'.bodyNF)
    (d:Candidate Ω t.domainNF) (d':Candidate Ω t'.domainNF)
    (b:t.BodyReads) (b':t'.BodyReads)
    (hd:Ω.profile t.domainNF ∈ C → d.val = d'.val)
    (hb:∀ n hn p hp,Ω.profile (t.targetNF n) ∈ C →
        (b n hn p hp).val = (b' n (hD ▸ hn) p (hD ▸ hp)).val) :
    (t.candidate d b).val = (t'.candidate d' b').val:=by
  change Cands.ProductTest Ω t.domainNF t.bodyNF (t.testers d) (t.fibers b) =
    Cands.ProductTest Ω t'.domainNF t'.bodyNF (t'.testers d') (t'.fibers b')
  rw [testers_eq hD d d' hd,fibers_eq hD hE b b' hb,hD,hE]
end ProdInst
abbrev Evaluator (Γ:List (Expr S)) (M T:Expr S) :=
  ∀ e:ValEnv (hw:=hw) Ω C hno Γ,PreRes Ω C hno M T e
structure Uniform {Γ:List (Expr S)} {M T:Expr S}
    (ev:Evaluator (hw:=hw) Ω C hno Γ M T) (F:Nat → Nat):Prop where
  growth:∀ k,k+1 ≤ F k
  bounded:∀ k e,e.Bounded k → Param.Bounded Ω C hno (F k) (ev e).parameter
  compare:∀ k e f,e.Bounded k → f.Bounded k → e.LevelEq (F k) f →
    Param.LevelEq Ω C hno k (ev e).parameter (ev f).parameter ∧ (ev e).read.val = (ev f).read.val
namespace Uniform
variable {Ω C hno} {Γ:List (Expr S)} {M T:Expr S}
variable {ev:Evaluator (hw:=hw) Ω C hno Γ M T} {F:Nat → Nat}
theorem val_bounded (h:Uniform Ω C hno ev F) (k:Nat) (e:ValEnv (hw:=hw) Ω C hno Γ)
    (he:e.Bounded k) (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)) :
    RawValue.Bounded Ω C hno (F k) ((ev e).val ha).val :=
  (ev e).val_bounded (h.bounded k e he) ha
theorem val_level (h:Uniform Ω C hno ev F) (k:Nat) (e f:ValEnv (hw:=hw) Ω C hno Γ)
    (he:e.Bounded k) (hf:f.Bounded k) (hef:e.LevelEq (F k) f)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (hb:ActL P C (Ω.profile (T.subst f.images).nfTerm)) :
    RawValue.LevelEq Ω C hno k ((ev e).val ha).val ((ev f).val hb).val :=
  (ev e).val_level (ev f) (h.compare k e f he hf hef).1 ha hb
end Uniform
namespace PreRes
variable {Ω C hno} {Γ:List (Expr S)} {M T:Expr S}
theorem lookup_parameter {n:Nat} {A:Expr S} (h:HasType P Γ (.var n) T)
    (hd:Lookup Γ n A) (hc:Converts T A) (e:ValEnv (hw:=hw) Ω C hno Γ) :
    (lookup h hd hc e).parameter = e.parameters n:=by
  have ht:=e.type_convert_eq h (HasType.lookup h.valid hd) hc
  have hp:=e.lawful n A hd
  rw [← ht] at hp
  by_cases ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)
  · rw [parameter_eq _ ha]
    exact hp.value_spec ha
  · rw [show (lookup h hd hc e).parameter = none from dif_neg ha]
    cases hh:e.parameters n with
    | none => rfl
    | some v =>
      rw [hh] at hp
      exact False.elim (ha hp.active)
theorem lookup_uniform {n:Nat} {A:Expr S} (h:HasType P Γ (.var n) T)
    (hd:Lookup Γ n A) (hc:Converts T A) :
    Uniform (hw:=hw) Ω C hno (lookup h hd hc) (fun k => k+1):=by
  constructor
  · intro k; exact le_refl _
  · intro k e he
    rw [lookup_parameter]
    exact Param.bounded_mono (Nat.le_succ k) (he n h.scope.1)
  · intro k e f he hf hef
    have hparam:Param.LevelEq Ω C hno k (lookup h hd hc e).parameter (lookup h hd hc f).parameter:=by
      rw [lookup_parameter,lookup_parameter]
      exact Param.level_mono (Nat.le_succ k) (hef.2 n h.scope.1)
    refine ⟨hparam,?_⟩
    apply baseRead_level h hef.1
    intro ha hb
    exact val_level _ _ hparam ha hb
theorem sort_uniform {s t:S} (h:HasType P Γ (.sort s) T)
    (ha:P.sortAxioms s t) (hc:Converts T (.sort t)) :
    Uniform (hw:=hw) Ω C hno (sort h ha hc) (fun k => k+1):=by
  constructor
  · intro k; exact le_refl _
  · intro k e _
    apply parameter_bounded
    intro ht
    exact RawValue.bounded_mono (Nat.succ_le_succ (Nat.zero_le k)) (distinguished_bounded Ω C hno _)
  · intro k e f _ _ hef
    constructor
    · apply parameter_level _ _ (e.actual_type_eq hef.1 h)
      intro ht ht'
      have hh:e.activeType h ht = f.activeType h ht':=ActTy.ext (e.actual_type_eq hef.1 h)
      change RawValue.LevelEq Ω C hno k (distinguished Ω C hno (e.activeType h ht)).val
        (distinguished Ω C hno (f.activeType h ht')).val
      rw [hh]
      exact RawValue.level_refl k _
    · exact congrArg (Cands.Top Ω) (e.actual_expr_eq hef.1 h)
theorem abstractionAction_bounded {D m E:Expr S} {s:S} (h:HasType P Γ (.lam D m) T)
    (hp:HasType P Γ (.pi D E) (.sort s)) (hc:Converts T (.pi D E))
    (eb:Evaluator (hw:=hw) Ω C hno (D :: Γ) m E) {B:Nat → Nat}
    (hb:Uniform Ω C hno eb B) (k:Nat) (e:ValEnv (hw:=hw) Ω C hno Γ)
    (he:e.Bounded k) (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)) :
    ActionBound Ω C hno (e.activeType h ha) k (B k) (abstractionAction h hp hc eb e ha):=by
  intro a p hp' hbp
  dsimp only [abstractionAction]
  apply hb.val_bounded
  dsimp only [ProdInst.frameValEnv,ProdInst.extend]
  exact ValEnv.bounded_cons _ _ _ _ he hbp
theorem abstractionAction_level {D m E:Expr S} {s:S} (h:HasType P Γ (.lam D m) T)
    (hp:HasType P Γ (.pi D E) (.sort s)) (hc:Converts T (.pi D E))
    (eb:Evaluator (hw:=hw) Ω C hno (D :: Γ) m E) {B:Nat → Nat}
    (hb:Uniform Ω C hno eb B) (k:Nat) (e f:ValEnv (hw:=hw) Ω C hno Γ)
    (he:e.Bounded k) (hf:f.Bounded k) (hef:e.LevelEq (B k) f)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (ha':ActL P C (Ω.profile (T.subst f.images).nfTerm))
    (a:FrameKey Ω C (e.activeType h ha)) (a':FrameKey Ω C (f.activeType h ha'))
    (hq:a.argument = a'.argument)
    (p p':Option (RawValue (hw:=hw) Ω C hno))
    (hp':PayFits Ω C hno a.domain p) (hp'':PayFits Ω C hno a'.domain p')
    (hbp:Param.Bounded Ω C hno k p) (hbp':Param.Bounded Ω C hno k p')
    (hpp:Param.LevelEq Ω C hno (B k) p p') :
    RawValue.LevelEq Ω C hno k (abstractionAction h hp hc eb e ha a p hp').val
      (abstractionAction h hp hc eb f ha' a' p' hp'').val:=by
  dsimp only [abstractionAction]
  apply hb.val_level
  · dsimp only [ProdInst.frameValEnv,ProdInst.extend]
    exact ValEnv.bounded_cons _ _ _ _ he hbp
  · dsimp only [ProdInst.frameValEnv,ProdInst.extend]
    exact ValEnv.bounded_cons _ _ _ _ hf hbp'
  · dsimp only [ProdInst.frameValEnv,ProdInst.extend]
    apply ValEnv.level_cons hef
    · exact hq ▸ .refl _
    · exact hpp
theorem abstraction_val_level {D m E:Expr S} {s:S} (h:HasType P Γ (.lam D m) T)
    (hp:HasType P Γ (.pi D E) (.sort s)) (hc:Converts T (.pi D E))
    (eb:Evaluator (hw:=hw) Ω C hno (D :: Γ) m E) {B:Nat → Nat}
    (hb:Uniform Ω C hno eb B) (k:Nat) (e f:ValEnv (hw:=hw) Ω C hno Γ)
    (he:e.Bounded k) (hf:f.Bounded k) (hef:e.LevelEq (B k) f)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (ha':ActL P C (Ω.profile (T.subst f.images).nfTerm)) :
    RawValue.LevelEq Ω C hno k ((abstraction h hp hc eb e).val ha).val
      ((abstraction h hp hc eb f).val ha').val:=by
  apply lambdaValue_level_of_type_eq Ω C hno (e.actual_type_eq hef.1 h)
  exact abstractionAction_level h hp hc eb hb k e f he hf hef ha ha'
theorem abstraction_uniform {D m E:Expr S} {s:S} (h:HasType P Γ (.lam D m) T)
    (hp:HasType P Γ (.pi D E) (.sort s)) (hc:Converts T (.pi D E))
    (eb:Evaluator (hw:=hw) Ω C hno (D :: Γ) m E) {B:Nat → Nat}
    (hb:Uniform Ω C hno eb B) :
    Uniform Ω C hno (abstraction h hp hc eb) (fun k => B k + 1):=by
  constructor
  · intro k
    exact le_trans (hb.growth k) (Nat.le_succ _)
  · intro k e he
    apply parameter_bounded
    intro ha
    apply lambdaValue_bounded Ω C hno (by have:=hb.growth k; omega)
    · exact abstractionAction_bounded h hp hc eb hb k e he ha
    · intro a p p' hp' hp'' hbp hbp' hpp
      exact abstractionAction_level h hp hc eb hb k e e he he (e.level_refl _) ha ha
        a a rfl p p' hp' hp'' hbp hbp' hpp
  · intro k e f he hf hef
    have hf':=e.level_mono (Nat.le_succ (B k)) hef
    constructor
    · apply parameter_level _ _ (e.actual_type_eq hef.1 h)
      exact abstraction_val_level h hp hc eb hb k e f he hf hf'
    · apply baseRead_level h hef.1
      exact abstraction_val_level h hp hc eb hb k e f he hf hf'
def appBound (F N:Nat → Nat) (k:Nat):Nat :=
  1 + max (max (max k (F k)) (N k)) (max (F (max k (N k))) (N (max k (F k))))
 theorem applicationValue_bounded {f n D E:Expr S} (h:HasType P Γ (.app f n) T)
    (hf:HasType P Γ f (.pi D E)) (hn:HasType P Γ n D) (hc:Converts T (E.instantiate n))
    (ef:Evaluator (hw:=hw) Ω C hno Γ f (.pi D E)) (en:Evaluator (hw:=hw) Ω C hno Γ n D)
    {F N:Nat → Nat} (huf:Uniform Ω C hno ef F) (_hun:Uniform Ω C hno en N)
    (k:Nat) (e:ValEnv (hw:=hw) Ω C hno Γ) (he:e.Bounded k)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)) :
    RawValue.Bounded Ω C hno (appBound F N k) (applicationValue h hf hn hc ef en e ha).val:=by
  dsimp only [applicationValue]
  split
  ·
    apply RawValue.bounded_mono (m:=appBound F N k) (n:=F k) (by unfold appBound; omega)
    apply applyValue_bounded
    exact huf.val_bounded k e he _
  · exact RawValue.bounded_mono (by unfold appBound; omega) (distinguished_bounded Ω C hno _)
 theorem applicationValue_level {f n D E:Expr S} (h:HasType P Γ (.app f n) T)
    (hf:HasType P Γ f (.pi D E)) (hn:HasType P Γ n D) (hc:Converts T (E.instantiate n))
    (ef:Evaluator (hw:=hw) Ω C hno Γ f (.pi D E)) (en:Evaluator (hw:=hw) Ω C hno Γ n D)
    {F N:Nat → Nat} (huf:Uniform Ω C hno ef F) (hun:Uniform Ω C hno en N)
    (k:Nat) (e e':ValEnv (hw:=hw) Ω C hno Γ) (he:e.Bounded k) (he':e'.Bounded k)
    (hee:e.LevelEq (appBound F N k) e')
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (ha':ActL P C (Ω.profile (T.subst e'.images).nfTerm)) :
    RawValue.LevelEq Ω C hno k (applicationValue h hf hn hc ef en e ha).val
      (applicationValue h hf hn hc ef en e' ha').val:=by
  have ht:=e.actual_type_eq hee.1 hf
  by_cases hF:ActL P C (Ω.profile (Expr.pi D E |>.subst e.images).nfTerm)
  · have hF':ActL P C (Ω.profile (Expr.pi D E |>.subst e'.images).nfTerm):=ht ▸ hF
    simp only [applicationValue,hF,hF',dite_true]
    apply applyValue_level_of_type_eq Ω C hno (j:=F k) (r:=N k) ht
    · exact huf.val_bounded k e he _
    · exact huf.val_level (max k (N k)) e e'
        (e.bounded_mono (le_max_left _ _) he) (e'.bounded_mono (le_max_left _ _) he')
        (e.level_mono (by unfold appBound; omega) hee) _ _
    · exact e.actual_expr_eq hee.1 hn
    · exact hun.bounded k e he
    · apply Param.level_mono (le_max_right k (F k))
      exact (hun.compare (max k (F k)) e e'
        (e.bounded_mono (le_max_left _ _) he) (e'.bounded_mono (le_max_left _ _) he')
        (e.level_mono (by unfold appBound; omega) hee)).1
  · have hF':¬ ActL P C (Ω.profile (Expr.pi D E |>.subst e'.images).nfTerm):=ht ▸ hF
    simp only [applicationValue,hF,hF',dite_false]
    have hA:e.activeType h ha = e'.activeType h ha':=ActTy.ext (e.actual_type_eq hee.1 h)
    have hv:=congrArg (fun A:ActTy Ω C => (distinguished (hw:=hw) Ω C hno A).val) hA
    rw [hv]
    exact RawValue.level_refl k _
 theorem application_uniform {f n D E:Expr S} (h:HasType P Γ (.app f n) T)
    (hf:HasType P Γ f (.pi D E)) (hn:HasType P Γ n D) (hc:Converts T (E.instantiate n))
    (ef:Evaluator (hw:=hw) Ω C hno Γ f (.pi D E)) (en:Evaluator (hw:=hw) Ω C hno Γ n D)
    {F N:Nat → Nat} (huf:Uniform Ω C hno ef F) (hun:Uniform Ω C hno en N) :
    Uniform Ω C hno (application h hf hn hc ef en) (appBound F N):=by
  constructor
  · intro k; unfold appBound; omega
  · intro k e he
    apply parameter_bounded
    exact applicationValue_bounded h hf hn hc ef en huf hun k e he
  · intro k e e' he he' hee
    constructor
    · apply parameter_level _ _ (e.actual_type_eq hee.1 h)
      exact applicationValue_level h hf hn hc ef en huf hun k e e' he he' hee
    · apply baseRead_level h hee.1
      exact applicationValue_level h hf hn hc ef en huf hun k e e' he he' hee
end PreRes
omit [Fintype S] in
theorem Base.update_congr {T U:ActualType Ω} (b:Base Ω) (hTU:T = U)
    (d:Candidate Ω T.val) (e:Candidate Ω U.val) (hde:d.val = e.val) :
    Base.update Ω b T d = Base.update Ω b U e:=by
  subst U
  have hd:d = e:=Subtype.ext hde
  subst e
  rfl
theorem withBase_level_of_type_eq {T U:ActTy Ω C} (hTU:T.type = U.type)
    {b b':Base Ω} (hbb:b = b') (k:Nat) :
    RawValue.LevelEq (hw:=hw) Ω C hno k (withBase Ω C hno T b).val (withBase Ω C hno U b').val:=by
  have ht:=ActTy.ext hTU
  subst U
  subst b'
  exact RawValue.level_refl k _
theorem distinguished_level_of_type_eq {T U:ActTy Ω C} (hTU:T.type = U.type) (k:Nat) :
    RawValue.LevelEq (hw:=hw) Ω C hno k (distinguished Ω C hno T).val (distinguished Ω C hno U).val:=by
  have ht:=ActTy.ext hTU
  subst U
  exact RawValue.level_refl k _
namespace PreRes
variable {Ω C hno} {Γ:List (Expr S)} {T:Expr S}
def productBound (D B:Nat → Nat) (k:Nat):Nat:=1 + max k (max (D k) (B k))
theorem productCandidate_level {D E:Expr S} {a b c:S}
    (hd:HasType P Γ D (.sort a)) (hb:HasType P (D :: Γ) E (.sort b)) (hr:P.rule a b c)
    (ed:Evaluator (hw:=hw) Ω C hno Γ D (.sort a))
    (eb:Evaluator (hw:=hw) Ω C hno (D :: Γ) E (.sort b))
    (hC:IsComp (PriEdge P) C)
    {F B:Nat → Nat} (hud:Uniform Ω C hno ed F) (hub:Uniform Ω C hno eb B)
    (k:Nat) (e f:ValEnv (hw:=hw) Ω C hno Γ)
    (he:e.Bounded k) (hf:f.Bounded k) (hef:e.LevelEq (productBound F B k) f)
    (hK:Ω.profile (Expr.pi D E |>.subst e.images).nfTerm ∈ C) :
    (productCandidate hd hb hr ed eb e).val = (productCandidate hd hb hr ed eb f).val:=by
  let t:=productData hd hb hr e
  let u:=productData hd hb hr f
  have hp:=e.actual_expr_eq hef.1 (HasType.product hd hb hr)
  have hdu:=Expr.pi.inj ((t.product_nf.symm.trans hp).trans u.product_nf)
  have hk:Ω.profile (.pi t.domainNF t.bodyNF) ∈ C:=t.product_nf ▸ hK
  apply ProdInst.candidate_eq hdu.1 hdu.2
  · intro _
    exact (hud.compare k e f he hf (e.level_mono (by unfold productBound; omega) hef)).2
  · intro n hn p hpn hc
    have hnb:=t.domain_not_minus hC hn hk hc
    have hbp:Param.Bounded Ω C hno k p:=Param.bounded_of_not_minus hnb hpn
    apply (hub.compare k (t.extend hn p hpn) (u.extend (hdu.1 ▸ hn) p (hdu.1 ▸ hpn)) ?_ ?_ ?_).2
    · dsimp only [ProdInst.extend]
      exact ValEnv.bounded_cons _ _ _ _ he hbp
    · dsimp only [ProdInst.extend]
      exact ValEnv.bounded_cons _ _ _ _ hf hbp
    · dsimp only [ProdInst.extend]
      apply ValEnv.level_cons (e.level_mono (by unfold productBound; omega) hef)
      · exact .refl _
      · exact Param.level_refl _ _
theorem product_val_level {D E:Expr S} {a b c:S} (h:HasType P Γ (.pi D E) T)
    (hd:HasType P Γ D (.sort a)) (hb:HasType P (D :: Γ) E (.sort b)) (hr:P.rule a b c)
    (hc:Converts T (.sort c))
    (ed:Evaluator (hw:=hw) Ω C hno Γ D (.sort a))
    (eb:Evaluator (hw:=hw) Ω C hno (D :: Γ) E (.sort b))
    (hC:IsComp (PriEdge P) C)
    {F B:Nat → Nat} (hud:Uniform Ω C hno ed F) (hub:Uniform Ω C hno eb B)
    (k:Nat) (e f:ValEnv (hw:=hw) Ω C hno Γ)
    (he:e.Bounded k) (hf:f.Bounded k) (hef:e.LevelEq (productBound F B k) f)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (ha':ActL P C (Ω.profile (T.subst f.images).nfTerm)) :
    RawValue.LevelEq Ω C hno k ((product h hd hb hr hc ed eb e).val ha).val
      ((product h hd hb hr hc ed eb f).val ha').val:=by
  have hp:=e.actual_expr_eq hef.1 h
  have ht:=e.actual_type_eq hef.1 h
  by_cases hh:({c}:Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst e.images).nfTerm ∈ C
  · have hh':({c}:Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst f.images).nfTerm ∈ C:=hp ▸ hh
    simp only [product,hh,hh']
    apply withBase_level_of_type_eq Ω C hno ht
    apply Base.update_congr Ω _ (Subtype.ext hp)
    exact productCandidate_level hd hb hr ed eb hC hud hub k e f he hf hef hh.2
  · have hh':¬ (({c}:Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst f.images).nfTerm ∈ C):=hp ▸ hh
    simp only [product,hh,hh',dite_false]
    exact distinguished_level_of_type_eq Ω C hno ht k
theorem product_uniform {D E:Expr S} {a b c:S} (h:HasType P Γ (.pi D E) T)
    (hd:HasType P Γ D (.sort a)) (hb:HasType P (D :: Γ) E (.sort b)) (hr:P.rule a b c)
    (hc:Converts T (.sort c))
    (ed:Evaluator (hw:=hw) Ω C hno Γ D (.sort a))
    (eb:Evaluator (hw:=hw) Ω C hno (D :: Γ) E (.sort b))
    (hC:IsComp (PriEdge P) C)
    {F B:Nat → Nat} (hud:Uniform Ω C hno ed F) (hub:Uniform Ω C hno eb B) :
    Uniform Ω C hno (product h hd hb hr hc ed eb) (productBound F B):=by
  constructor
  · intro k; unfold productBound; omega
  · intro k e _
    apply parameter_bounded
    intro ha
    dsimp only [product]
    split
    · exact RawValue.bounded_mono (by unfold productBound; omega) (withBase_bounded Ω C hno _ _)
    · exact RawValue.bounded_mono (by unfold productBound; omega) (distinguished_bounded Ω C hno _)
  · intro k e f he hf hef
    constructor
    · apply parameter_level _ _ (e.actual_type_eq hef.1 h)
      exact product_val_level h hd hb hr hc ed eb hC hud hub k e f he hf hef
    · have hp:=e.actual_expr_eq hef.1 h
      by_cases hh:Ω.profile (Expr.pi D E |>.subst e.images).nfTerm ∈ C
      · have hh':Ω.profile (Expr.pi D E |>.subst f.images).nfTerm ∈ C:=hp ▸ hh
        simp only [product,hh,hh',ite_true]
        exact productCandidate_level hd hb hr ed eb hC hud hub k e f he hf hef hh
      · have hh':Ω.profile (Expr.pi D E |>.subst f.images).nfTerm ∉ C:=hp ▸ hh
        simp only [product,hh,hh',ite_false]
        exact congrArg (Cands.Top Ω) hp
end PreRes
end
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
theorem preEval_uniform {Γ:List (Expr S)} {M T:Expr S}
    (hC:IsComp (PriEdge P) C) (t:TyTree P Γ M T) :
    ∃ F,Uniform (hw:=hw) Ω C hno (preEval Ω C hno t) F:=by
  induction t with
  | var h hd hc => exact ⟨_,PreRes.lookup_uniform h hd hc⟩
  | sort h ha hc => exact ⟨_,PreRes.sort_uniform h ha hc⟩
  | product h d b hr hc ihd ihb =>
    obtain ⟨F,hF⟩:=ihd
    obtain ⟨B,hB⟩:=ihb
    exact ⟨_,PreRes.product_uniform h d.typing b.typing hr hc _ _ hC hF hB⟩
  | abstraction h d b hp hc _ ihb =>
    obtain ⟨B,hB⟩:=ihb
    exact ⟨_,PreRes.abstraction_uniform h hp hc _ hB⟩
  | application h f a hc ihf iha =>
    obtain ⟨F,hF⟩:=ihf
    obtain ⟨N,hN⟩:=iha
    exact ⟨_,PreRes.application_uniform h f.typing a.typing hc _ _ hF hN⟩
namespace RawValue
variable {Ω C hno}
theorem all_levels_eq {v w:RawValue (hw:=hw) Ω C hno}
    (h:∀ n,LevelEq Ω C hno n v w):v = w:=by
  cases v <;> cases w <;> try exact False.elim (h 0)
  · exact congrArg _ (h 0)
  · exact congrArg _ (FreeObs.Agree.all_levels_eq h)
  · exact congrArg _ (h 0)
end RawValue
namespace Param
variable {Ω C hno}
theorem all_levels_eq {v w:Option (RawValue (hw:=hw) Ω C hno)}
    (h:∀ n,LevelEq Ω C hno n v w):v = w:=by
  cases v <;> cases w <;> try exact False.elim (h 0)
  · rfl
  · exact congrArg some (RawValue.all_levels_eq h)
end Param
namespace ValEnv
variable {Ω C hno} {Γ:List (Expr S)}
def Compatible (e f:ValEnv (hw:=hw) Ω C hno Γ):Prop :=
  e.ImageCompatible f ∧ ∀ n,n < Γ.length → e.parameters n = f.parameters n
theorem Compatible.level {e f:ValEnv (hw:=hw) Ω C hno Γ}
    (h:e.Compatible f) (k:Nat):e.LevelEq k f:=by
  refine ⟨h.1,fun n hn => ?_⟩
  rw [h.2 n hn]
  exact Param.level_refl _ _
end ValEnv
namespace Uniform
variable {Ω C hno} {Γ:List (Expr S)} {M T:Expr S}
variable {ev:Evaluator (hw:=hw) Ω C hno Γ M T} {F:Nat → Nat}
theorem compatible (h:Uniform Ω C hno ev F)
    (e f:ValEnv (hw:=hw) Ω C hno Γ) (hef:e.Compatible f) :
    (ev e).parameter = (ev f).parameter ∧ (ev e).read.val = (ev f).read.val:=by
  obtain ⟨i,hi⟩:=e.exists_bound
  obtain ⟨j,hj⟩:=f.exists_bound
  have hc (k:Nat):=h.compare (max k (max i j)) e f
    (e.bounded_mono (by omega) hi) (f.bounded_mono (by omega) hj)
    (hef.level _)
  constructor
  · apply Param.all_levels_eq
    intro k
    exact Param.level_mono (le_max_left _ _) (hc k).1
  · exact (hc 0).2
end Uniform
theorem preEval_compatible {Γ:List (Expr S)} {M T:Expr S}
    (hC:IsComp (PriEdge P) C) (t:TyTree P Γ M T)
    (e f:ValEnv (hw:=hw) Ω C hno Γ) (hef:e.Compatible f) :
    (preEval Ω C hno t e).parameter = (preEval Ω C hno t f).parameter ∧
    (preEval Ω C hno t e).read.val = (preEval Ω C hno t f).read.val:=by
  obtain ⟨F,hF⟩:=preEval_uniform Ω C hno hC t
  exact hF.compatible e f hef
end S_wpc_barendregt_geuvers_klop.ObsVals
end OMA
namespace OMA
namespace S_wpc_barendregt_geuvers_klop.ObsVals
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
theorem lambdaValue_congr {T U:ActTy Ω C} (hTU:T.type = U.type)
    (act:LambdaAction (hw:=hw) Ω C hno T) (act':LambdaAction (hw:=hw) Ω C hno U)
    (hr:∀ (a:FrameKey Ω C T) (a':FrameKey Ω C U),a.argument = a'.argument →
      ∀ p hp hp',(act a p hp).val = (act' a' p hp').val) :
    (lambdaValue Ω C hno T act).val = (lambdaValue Ω C hno U act').val:=by
  have hu:=ActTy.ext hTU
  subst U
  have he:act = act':=by
    funext a p hp
    exact Subtype.ext (hr a a rfl p hp hp)
  rw [he]
theorem applyValue_congr {T U:ActTy Ω C} (hTU:T.type = U.type)
    (v:Value (hw:=hw) Ω C hno T.type) (v':Value (hw:=hw) Ω C hno U.type)
    (hvv:v.val = v'.val) (a:FrameKey Ω C T) (a':FrameKey Ω C U)
    (hq:a.argument = a'.argument) (p p':Option (RawValue (hw:=hw) Ω C hno)) (hpp:p = p')
    (hp:PayFits Ω C hno a.domain p) (hp':PayFits Ω C hno a'.domain p') :
    (applyValue Ω C hno T v a p hp).val = (applyValue Ω C hno U v' a' p' hp').val:=by
  have hu:=ActTy.ext hTU
  subst U
  have hv:v = v':=Subtype.ext hvv
  have ha:a = a':=FrameKey.ext hq
  subst v'
  subst a'
  subst p'
  rfl
theorem withBase_congr {T U:ActTy Ω C} (hTU:T.type = U.type)
    (b b':Base Ω) (hbb:b = b') :
    (withBase (hw:=hw) Ω C hno T b).val = (withBase Ω C hno U b').val:=by
  have hu:=ActTy.ext hTU
  subst U
  subst b'
  rfl
theorem distinguished_congr {T U:ActTy Ω C} (hTU:T.type = U.type) :
    (distinguished (hw:=hw) Ω C hno T).val = (distinguished Ω C hno U).val:=by
  have hu:=ActTy.ext hTU
  subst U
  rfl
namespace PreRes
section
variable {Ω C hno} {Γ Δ:List (Expr S)} {M M' T T':Expr S}
variable {e:ValEnv (hw:=hw) Ω C hno Γ} {f:ValEnv (hw:=hw) Ω C hno Δ}
theorem parameter_congr (r:PreRes Ω C hno M T e) (q:PreRes Ω C hno M' T' f)
    (hT:(T.subst e.images).nfTerm = (T'.subst f.images).nfTerm)
    (hv:∀ ha hb,(r.val ha).val = (q.val hb).val):r.parameter = q.parameter:=by
  by_cases ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)
  · have hb:ActL P C (Ω.profile (T'.subst f.images).nfTerm):=hT ▸ ha
    rw [r.parameter_eq ha,q.parameter_eq hb,hv ha hb]
  · have hb:¬ ActL P C (Ω.profile (T'.subst f.images).nfTerm):=hT ▸ ha
    simp only [parameter,ha,hb,dite_false]
theorem val_congr (r:PreRes Ω C hno M T e) (q:PreRes Ω C hno M' T' f)
    (hr:r.parameter = q.parameter)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (hb:ActL P C (Ω.profile (T'.subst f.images).nfTerm)) :
    (r.val ha).val = (q.val hb).val:=by
  rw [r.parameter_eq ha,q.parameter_eq hb] at hr
  exact Option.some.inj hr
theorem baseRead_congr (h:HasType P Γ M T) (h':HasType P Δ M' T')
    (hM:(M.subst e.images).nfTerm = (M'.subst f.images).nfTerm)
    (hT:(T.subst e.images).nfTerm = (T'.subst f.images).nfTerm)
    (hS:(∃ s:S,T = .sort s ∧ ({s}:Set S) ∈ C) ↔
      (∃ s:S,T' = .sort s ∧ ({s}:Set S) ∈ C))
    (v:ActL P C (Ω.profile (T.subst e.images).nfTerm) →
      Value (hw:=hw) Ω C hno (T.subst e.images).nfTerm)
    (w:ActL P C (Ω.profile (T'.subst f.images).nfTerm) →
      Value (hw:=hw) Ω C hno (T'.subst f.images).nfTerm)
    (hv:∀ ha hb,(v ha).val = (w hb).val) :
    (baseRead h v).val = (baseRead h' w).val:=by
  by_cases hm:Ω.profile (M.subst e.images).nfTerm ∈ C
  · have hm':Ω.profile (M'.subst f.images).nfTerm ∈ C:=hM ▸ hm
    by_cases hs:∃ s:S,T = .sort s ∧ ({s}:Set S) ∈ C
    · have hs':=hS.mp hs
      by_cases ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)
      · have hb:ActL P C (Ω.profile (T'.subst f.images).nfTerm):=hT ▸ ha
        simp only [baseRead,hm,hm',hs,hs',ha,hb,dite_true]
        have hX:e.actualExpression (hs.choose_spec.1 ▸ h) =
            f.actualExpression (hs'.choose_spec.1 ▸ h'):=Subtype.ext hM
        rw [hv ha hb]
        exact congrArg (fun X:ActualType Ω => ((RawValue.base Ω C hno (w hb).val) X).val) hX
      · have hb:¬ ActL P C (Ω.profile (T'.subst f.images).nfTerm):=hT ▸ ha
        simp only [baseRead,hm,hm',hs,hs',ha,hb,dite_true,dite_false]
        exact congrArg (Cands.Top Ω) hM
    · have hs':=mt hS.mpr hs
      simp only [baseRead,hm,hm',hs,hs',dite_true,dite_false]
      exact congrArg (Cands.Top Ω) hM
  · have hm':Ω.profile (M'.subst f.images).nfTerm ∉ C:=hM ▸ hm
    simp only [baseRead,hm,hm',dite_false]
    exact congrArg (Cands.Top Ω) hM
end
variable {Ω C hno} {Γ Δ:List (Expr S)} {T T':Expr S}
 theorem abstractionAction_congr {D m E D' m' E':Expr S} {s s':S}
    (h:HasType P Γ (.lam D m) T) (h':HasType P Δ (.lam D' m') T')
    (hp:HasType P Γ (.pi D E) (.sort s)) (hp':HasType P Δ (.pi D' E') (.sort s'))
    (hc:Converts T (.pi D E)) (hc':Converts T' (.pi D' E'))
    (eb:Evaluator (hw:=hw) Ω C hno (D :: Γ) m E)
    (eb':Evaluator (hw:=hw) Ω C hno (D' :: Δ) m' E')
    (e:ValEnv (hw:=hw) Ω C hno Γ) (e':ValEnv (hw:=hw) Ω C hno Δ)
    (hb:∀ n n' (hn:Ω.HasType n (D.subst e.images)) (hn':Ω.HasType n' (D'.subst e'.images)),
      n = n' → ∀ p hp hp' ha ha',
        ((eb (e.cons hn p hp)).val ha).val = ((eb' (e'.cons hn' p hp')).val ha').val)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (ha':ActL P C (Ω.profile (T'.subst e'.images).nfTerm))
    (a:FrameKey Ω C (e.activeType h ha)) (a':FrameKey Ω C (e'.activeType h' ha'))
    (haa:a.argument = a'.argument) (p:Option (RawValue (hw:=hw) Ω C hno))
    (hpa:PayFits Ω C hno a.domain p) (hpa':PayFits Ω C hno a'.domain p) :
    (abstractionAction h hp hc eb e ha a p hpa).val =
      (abstractionAction h' hp' hc' eb' e' ha' a' p hpa').val:=by
  dsimp only [abstractionAction,ProdInst.frameValEnv,ProdInst.extend]
  exact hb a.argument a'.argument _ _ haa p _ _ _ _
 theorem abstraction_val_congr {D m E D' m' E':Expr S} {s s':S}
    (h:HasType P Γ (.lam D m) T) (h':HasType P Δ (.lam D' m') T')
    (hp:HasType P Γ (.pi D E) (.sort s)) (hp':HasType P Δ (.pi D' E') (.sort s'))
    (hc:Converts T (.pi D E)) (hc':Converts T' (.pi D' E'))
    (eb:Evaluator (hw:=hw) Ω C hno (D :: Γ) m E)
    (eb':Evaluator (hw:=hw) Ω C hno (D' :: Δ) m' E')
    (e:ValEnv (hw:=hw) Ω C hno Γ) (e':ValEnv (hw:=hw) Ω C hno Δ)
    (hT:(T.subst e.images).nfTerm = (T'.subst e'.images).nfTerm)
    (hb:∀ n n' (hn:Ω.HasType n (D.subst e.images)) (hn':Ω.HasType n' (D'.subst e'.images)),
      n = n' → ∀ p hp hp' ha ha',
        ((eb (e.cons hn p hp)).val ha).val = ((eb' (e'.cons hn' p hp')).val ha').val)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (ha':ActL P C (Ω.profile (T'.subst e'.images).nfTerm)) :
    ((abstraction h hp hc eb e).val ha).val =
      ((abstraction h' hp' hc' eb' e').val ha').val:=by
  apply lambdaValue_congr Ω C hno hT
  exact abstractionAction_congr h h' hp hp' hc hc' eb eb' e e' hb ha ha'
 theorem application_val_congr {f n D E f' n' D' E':Expr S}
    (h:HasType P Γ (.app f n) T) (h':HasType P Δ (.app f' n') T')
    (hf:HasType P Γ f (.pi D E)) (hf':HasType P Δ f' (.pi D' E'))
    (hn:HasType P Γ n D) (hn':HasType P Δ n' D')
    (hc:Converts T (E.instantiate n)) (hc':Converts T' (E'.instantiate n'))
    (ef:Evaluator (hw:=hw) Ω C hno Γ f (.pi D E))
    (ef':Evaluator (hw:=hw) Ω C hno Δ f' (.pi D' E'))
    (en:Evaluator (hw:=hw) Ω C hno Γ n D)
    (en':Evaluator (hw:=hw) Ω C hno Δ n' D')
    (e:ValEnv (hw:=hw) Ω C hno Γ) (e':ValEnv (hw:=hw) Ω C hno Δ)
    (hT:(T.subst e.images).nfTerm = (T'.subst e'.images).nfTerm)
    (hF:(Expr.pi D E |>.subst e.images).nfTerm = (Expr.pi D' E' |>.subst e'.images).nfTerm)
    (hN:(n.subst e.images).nfTerm = (n'.subst e'.images).nfTerm)
    (hvf:∀ ha ha',((ef e).val ha).val = ((ef' e').val ha').val)
    (hvn:(en e).parameter = (en' e').parameter)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (ha':ActL P C (Ω.profile (T'.subst e'.images).nfTerm)) :
    ((application h hf hn hc ef en e).val ha).val =
      ((application h' hf' hn' hc' ef' en' e').val ha').val:=by
  by_cases hA:ActL P C (Ω.profile (Expr.pi D E |>.subst e.images).nfTerm)
  · have hA':ActL P C (Ω.profile (Expr.pi D' E' |>.subst e'.images).nfTerm):=hF ▸ hA
    dsimp only [application,baseResult,applicationValue]
    simp only [dif_pos hA,dif_pos hA']
    apply applyValue_congr Ω C hno hF _ _ (hvf _ _) _ _ hN _ _ hvn
  · have hA':¬ ActL P C (Ω.profile (Expr.pi D' E' |>.subst e'.images).nfTerm):=hF ▸ hA
    dsimp only [application,baseResult,applicationValue]
    simp only [dif_neg hA,dif_neg hA']
    exact distinguished_congr Ω C hno hT
 theorem productCandidate_congr {D E D' E':Expr S} {a b c a' b' c':S}
    (hd:HasType P Γ D (.sort a)) (hb:HasType P (D :: Γ) E (.sort b)) (hr:P.rule a b c)
    (hd':HasType P Δ D' (.sort a')) (hb':HasType P (D' :: Δ) E' (.sort b')) (hr':P.rule a' b' c')
    (ed:Evaluator (hw:=hw) Ω C hno Γ D (.sort a))
    (ed':Evaluator (hw:=hw) Ω C hno Δ D' (.sort a'))
    (eb:Evaluator (hw:=hw) Ω C hno (D :: Γ) E (.sort b))
    (eb':Evaluator (hw:=hw) Ω C hno (D' :: Δ) E' (.sort b'))
    (e:ValEnv (hw:=hw) Ω C hno Γ) (e':ValEnv (hw:=hw) Ω C hno Δ)
    (hD:(D.subst e.images).nfTerm = (D'.subst e'.images).nfTerm)
    (hE:(E.subst (Expr.liftSub e.images)).nfTerm = (E'.subst (Expr.liftSub e'.images)).nfTerm)
    (hvd:Ω.profile (D.subst e.images).nfTerm ∈ C → (ed e).read.val = (ed' e').read.val)
    (hvb:∀ n (hn:Ω.HasType n (D.subst e.images)) (hn':Ω.HasType n (D'.subst e'.images))
        p hp hp',Ω.profile (E.subst (e.cons hn p hp).images).nfTerm ∈ C →
        (eb (e.cons hn p hp)).read.val = (eb' (e'.cons hn' p hp')).read.val) :
    (productCandidate hd hb hr ed eb e).val = (productCandidate hd' hb' hr' ed' eb' e').val:=by
  dsimp only [productCandidate]
  apply ProdInst.candidate_eq (t:=productData hd hb hr e) (t':=productData hd' hb' hr' e') hD hE
  · exact hvd
  · intro n hn p hp hh
    exact hvb n _ _ p _ _ hh
 theorem product_val_congr {D E D' E':Expr S} {a b c a' b' c':S}
    (h:HasType P Γ (.pi D E) T) (h':HasType P Δ (.pi D' E') T')
    (hd:HasType P Γ D (.sort a)) (hb:HasType P (D :: Γ) E (.sort b)) (hr:P.rule a b c)
    (hd':HasType P Δ D' (.sort a')) (hb':HasType P (D' :: Δ) E' (.sort b')) (hr':P.rule a' b' c')
    (hc:Converts T (.sort c)) (hc':Converts T' (.sort c'))
    (ed:Evaluator (hw:=hw) Ω C hno Γ D (.sort a))
    (ed':Evaluator (hw:=hw) Ω C hno Δ D' (.sort a'))
    (eb:Evaluator (hw:=hw) Ω C hno (D :: Γ) E (.sort b))
    (eb':Evaluator (hw:=hw) Ω C hno (D' :: Δ) E' (.sort b'))
    (e:ValEnv (hw:=hw) Ω C hno Γ) (e':ValEnv (hw:=hw) Ω C hno Δ)
    (hT:(T.subst e.images).nfTerm = (T'.subst e'.images).nfTerm)
    (hM:(Expr.pi D E |>.subst e.images).nfTerm = (Expr.pi D' E' |>.subst e'.images).nfTerm)
    (hcc:({c}:Set S) ∈ C ↔ ({c'}:Set S) ∈ C)
    (hpc:Ω.profile (Expr.pi D E |>.subst e.images).nfTerm ∈ C →
      (productCandidate hd hb hr ed eb e).val = (productCandidate hd' hb' hr' ed' eb' e').val)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (ha':ActL P C (Ω.profile (T'.subst e'.images).nfTerm)) :
    ((product h hd hb hr hc ed eb e).val ha).val =
      ((product h' hd' hb' hr' hc' ed' eb' e').val ha').val:=by
  by_cases hh:({c}:Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst e.images).nfTerm ∈ C
  · have hh':({c'}:Set S) ∈ C ∧ Ω.profile (Expr.pi D' E' |>.subst e'.images).nfTerm ∈ C :=
      ⟨hcc.mp hh.1,hM ▸ hh.2⟩
    simp only [product,dif_pos hh,dif_pos hh']
    apply withBase_congr Ω C hno hT
    apply Base.update_congr Ω _ (Subtype.ext hM)
    exact hpc hh.2
  · have hh':¬ (({c'}:Set S) ∈ C ∧ Ω.profile (Expr.pi D' E' |>.subst e'.images).nfTerm ∈ C) :=
      fun hcc' => hh ⟨hcc.mpr hcc'.1,hM.symm ▸ hcc'.2⟩
    simp only [product,dif_neg hh,dif_neg hh']
    exact distinguished_congr Ω C hno hT
 theorem product_read_congr {D E D' E':Expr S} {a b c a' b' c':S}
    (h:HasType P Γ (.pi D E) T) (h':HasType P Δ (.pi D' E') T')
    (hd:HasType P Γ D (.sort a)) (hb:HasType P (D :: Γ) E (.sort b)) (hr:P.rule a b c)
    (hd':HasType P Δ D' (.sort a')) (hb':HasType P (D' :: Δ) E' (.sort b')) (hr':P.rule a' b' c')
    (hc:Converts T (.sort c)) (hc':Converts T' (.sort c'))
    (ed:Evaluator (hw:=hw) Ω C hno Γ D (.sort a))
    (ed':Evaluator (hw:=hw) Ω C hno Δ D' (.sort a'))
    (eb:Evaluator (hw:=hw) Ω C hno (D :: Γ) E (.sort b))
    (eb':Evaluator (hw:=hw) Ω C hno (D' :: Δ) E' (.sort b'))
    (e:ValEnv (hw:=hw) Ω C hno Γ) (e':ValEnv (hw:=hw) Ω C hno Δ)
    (hM:(Expr.pi D E |>.subst e.images).nfTerm = (Expr.pi D' E' |>.subst e'.images).nfTerm)
    (hpc:Ω.profile (Expr.pi D E |>.subst e.images).nfTerm ∈ C →
      (productCandidate hd hb hr ed eb e).val = (productCandidate hd' hb' hr' ed' eb' e').val) :
    (product h hd hb hr hc ed eb e).read.val = (product h' hd' hb' hr' hc' ed' eb' e').read.val:=by
  by_cases hh:Ω.profile (Expr.pi D E |>.subst e.images).nfTerm ∈ C
  · have hh':Ω.profile (Expr.pi D' E' |>.subst e'.images).nfTerm ∈ C:=hM ▸ hh
    simp only [product,if_pos hh,if_pos hh']
    exact hpc hh
  · have hh':Ω.profile (Expr.pi D' E' |>.subst e'.images).nfTerm ∉ C:=hM ▸ hh
    simp only [product,if_neg hh,if_neg hh']
    exact congrArg (Cands.Top Ω) hM
end PreRes
end S_wpc_barendregt_geuvers_klop.ObsVals
namespace S_wpc_barendregt_geuvers_klop
universe u
namespace Expr
variable {S:Type u} {M:Expr S} {n:Nat}
theorem Scoped.subst_congr (h:Scoped n M) {σ τ:Nat → Expr S}
    (he:∀ i,i < n → σ i = τ i):M.subst σ = M.subst τ:=by
  induction M generalizing n σ τ with
  | var i => exact he i h
  | sort s => rfl
  | app f a ihf iha => exact congrArg₂ Expr.app (ihf h.1 he) (iha h.2 he)
  | lam D m ihD ihm =>
    apply congrArg₂ Expr.lam (ihD h.1 he)
    apply ihm h.2
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact congrArg (Expr.rename Nat.succ) (he i (by omega))
  | pi D E ihD ihE =>
    apply congrArg₂ Expr.pi (ihD h.1 he)
    apply ihE h.2
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact congrArg (Expr.rename Nat.succ) (he i (by omega))
@[simp] theorem rename_eq_sort (M:Expr S) (ρ:Nat → Nat) (s:S) :
    M.rename ρ = .sort s ↔ M = .sort s:=by
  cases M <;> simp [rename]
end Expr
namespace ObsVals
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
namespace ValEnv
variable {Ω C hno} {Γ Δ:List (Expr S)}
def Reindexed (e:ValEnv (hw:=hw) Ω C hno Γ)
    (f:ValEnv (hw:=hw) Ω C hno Δ) (ρ:Nat → Nat):Prop :=
  ∀ i,i < Γ.length → e.images i = f.images (ρ i) ∧ e.parameters i = f.parameters (ρ i)
namespace Reindexed
variable {e:ValEnv (hw:=hw) Ω C hno Γ} {f:ValEnv (hw:=hw) Ω C hno Δ}
variable {ρ:Nat → Nat} (he:e.Reindexed f ρ)
include he
 theorem raw_eq {M:Expr S} (hm:M.Scoped Γ.length) :
    M.subst e.images = (M.rename ρ).subst f.images:=by
  rw [Expr.subst_rename]
  apply hm.subst_congr
  exact fun n hn => (he n hn).1
 theorem expr_eq {M T:Expr S} (h:HasType P Γ M T) :
    (M.subst e.images).nfTerm = (M.rename ρ |>.subst f.images).nfTerm :=
  congrArg Expr.nfTerm (he.raw_eq h.scope.1)
 theorem type_eq {M T:Expr S} (h:HasType P Γ M T) :
    (T.subst e.images).nfTerm = (T.rename ρ |>.subst f.images).nfTerm :=
  congrArg Expr.nfTerm (he.raw_eq h.scope.2)
 theorem cons {A:Expr S} {n m:Expr S}
    (hn:Ω.HasType n (A.subst e.images)) (hm:Ω.HasType m (A.rename ρ |>.subst f.images))
    (hnm:n = m) (p:Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno (A.subst e.images).nfTerm p)
    (hp':PayFits Ω C hno (A.rename ρ |>.subst f.images).nfTerm p) :
    (e.cons hn p hp).Reindexed (f.cons hm p hp') (Expr.liftRen ρ):=by
  intro i hi
  cases i with
  | zero => exact ⟨hnm,rfl⟩
  | succ i => exact he i (Nat.lt_of_succ_lt_succ hi)
end Reindexed
end ValEnv
 theorem preEvaluate_rename {Γ:List (Expr S)} {M T:Expr S} (t:TyTree P Γ M T)
    {Δ:List (Expr S)} (hΔ:ValidContext P Δ) (ρ:Nat → Nat) (hρ:TyTree.DeclRenaming Γ Δ ρ)
    (e:ValEnv (hw:=hw) Ω C hno Γ) (f:ValEnv (hw:=hw) Ω C hno Δ)
    (hef:e.Reindexed f ρ) :
    (preEval Ω C hno t e).parameter = (preEval Ω C hno (t.rename hΔ ρ hρ) f).parameter ∧
    (preEval Ω C hno t e).read.val = (preEval Ω C hno (t.rename hΔ ρ hρ) f).read.val:=by
  induction t generalizing Δ ρ with
  | var ht hd hc =>
      have hparam:(PreRes.lookup ht hd hc e).parameter =
          (PreRes.lookup (ht.rename hΔ ρ (hρ.typed hΔ)) (hρ _ _ hd) (hc.rename ρ) f).parameter:=by
        exact (PreRes.lookup_parameter ht hd hc e).trans
          ((hef _ ht.scope.1).2.trans (PreRes.lookup_parameter
            (ht.rename hΔ ρ (hρ.typed hΔ)) (hρ _ _ hd) (hc.rename ρ) f).symm)
      refine ⟨hparam,?_⟩
      apply PreRes.baseRead_congr ht (ht.rename hΔ ρ (hρ.typed hΔ))
        (hef.expr_eq ht) (hef.type_eq ht)
      · simp only [Expr.rename_eq_sort]
      · exact fun ha hb => PreRes.val_congr _ _ hparam ha hb
  | sort ht ha hc =>
      constructor
      · apply PreRes.parameter_congr _ _ (hef.type_eq ht)
        intro hs hs'
        exact distinguished_congr Ω C hno (hef.type_eq ht)
      · exact congrArg (Cands.Top Ω) (hef.expr_eq ht)
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hh:HasType P Δ (D.rename ρ) (.sort a):=d.typing.rename hΔ ρ (hρ.typed hΔ)
      have he:=hef.type_eq ht
      have hv:∀ ha ha',((preEval Ω C hno (.abstraction ht d b hp hc) e).val ha).val =
          ((preEval Ω C hno ((TyTree.abstraction ht d b hp hc).rename hΔ ρ hρ) f).val ha').val:=by
        apply PreRes.abstraction_val_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) hp
          (hp.rename hΔ ρ (hρ.typed hΔ)) hc (hc.rename ρ) _ _ e f he
        intro n m hn hm hnm p hpp hpp' ha ha'
        apply PreRes.val_congr
        exact (ihb (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D)
          (e.cons hn p hpp) (f.cons hm p hpp') (hef.cons hn hm hnm p hpp hpp')).1
      constructor
      · exact PreRes.parameter_congr _ _ he hv
      · apply PreRes.baseRead_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) (hef.expr_eq ht) he
        · simp only [Expr.rename_eq_sort]
        · exact hv
  | @application Γ g n D E T ht gtr ntr hc ihg ihn =>
      have hg:=ihg hΔ ρ hρ e f hef
      have hn:=ihn hΔ ρ hρ e f hef
      have he:=hef.type_eq ht
      have hv:∀ ha ha',((preEval Ω C hno (.application ht gtr ntr hc) e).val ha).val =
          ((preEval Ω C hno ((TyTree.application ht gtr ntr hc).rename hΔ ρ hρ) f).val ha').val:=by
        apply PreRes.application_val_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) gtr.typing
          (gtr.typing.rename hΔ ρ (hρ.typed hΔ)) ntr.typing (ntr.typing.rename hΔ ρ (hρ.typed hΔ))
          hc _ _ _ _ _ e f he (hef.type_eq gtr.typing) (hef.expr_eq ntr.typing)
        · exact fun ha ha' => PreRes.val_congr _ _ hg.1 ha ha'
        · exact hn.1
      constructor
      · exact PreRes.parameter_congr _ _ he hv
      · apply PreRes.baseRead_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) (hef.expr_eq ht) he
        · simp only [Expr.rename_eq_sort]
        · exact hv
  | @product Γ D E a b c T ht d btr hr hc ihd ihb =>
      have hh:HasType P Δ (D.rename ρ) (.sort a):=d.typing.rename hΔ ρ (hρ.typed hΔ)
      have hb:=btr.typing.rename (.cons hΔ hh) (Expr.liftRen ρ) ((hρ.lift D).typed (.cons hΔ hh))
      have hm:=hef.expr_eq ht
      have he:=hef.type_eq ht
      have hDE:=Expr.pi.inj (hef.raw_eq ht.scope.1)
      have hpc:∀ (_:Ω.profile (Expr.pi D E |>.subst e.images).nfTerm ∈ C),
          (PreRes.productCandidate d.typing btr.typing hr (preEval Ω C hno d)
            (preEval Ω C hno btr) e).val =
          (PreRes.productCandidate hh hb hr (preEval Ω C hno (d.rename hΔ ρ hρ))
            (preEval Ω C hno (btr.rename (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D))) f).val:=by
        intro _
        apply PreRes.productCandidate_congr d.typing btr.typing hr hh hb hr _ _ _ _ e f
          (congrArg Expr.nfTerm hDE.1) (congrArg Expr.nfTerm hDE.2)
        · intro _
          exact (ihd hΔ ρ hρ e f hef).2
        · intro n hn hn' p hp hp' _
          exact (ihb (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D)
            (e.cons hn p hp) (f.cons hn' p hp') (hef.cons hn hn' rfl p hp hp')).2
      constructor
      · apply PreRes.parameter_congr _ _ he
        apply PreRes.product_val_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) d.typing btr.typing hr hh hb hr
          hc (hc.rename ρ) _ _ _ _ e f he hm Iff.rfl hpc
      · exact PreRes.product_read_congr ht (ht.rename hΔ ρ (hρ.typed hΔ)) d.typing btr.typing hr hh hb hr
          hc (hc.rename ρ) _ _ _ _ e f hm hpc
end ObsVals
namespace TyTree
variable {S:Type u} {P:Specification S} {Γ Δ:List (Expr S)} {M T:Expr S}
noncomputable def recontext (t:TyTree P Γ M T) (h:ContextEquivalent P Γ Δ) :
    TyTree P Δ M T:=by
  induction t generalizing Δ with
  | var ht hd hc =>
      have ht':=(h.typing _ _).mp ht
      let g:=ht'.generation
      exact .var ht' g.choose_spec.1 g.choose_spec.2
  | sort ht ha hc => exact .sort ((h.typing _ _).mp ht) ha hc
  | product ht d b hr hc ihd ihb =>
      exact .product ((h.typing _ _).mp ht) (ihd h) (ihb (h.cons d.typing)) hr hc
  | abstraction ht d b hp hc ihd ihb =>
      exact .abstraction ((h.typing _ _).mp ht) (ihd h) (ihb (h.cons d.typing)) ((h.typing _ _).mp hp) hc
  | application ht g n hc ihg ihn => exact .application ((h.typing _ _).mp ht) (ihg h) (ihn h) hc
end TyTree
namespace ObsVals
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
namespace ValEnv
variable {Ω C hno} {Γ Δ:List (Expr S)}
def SameData (e:ValEnv (hw:=hw) Ω C hno Γ)
    (f:ValEnv (hw:=hw) Ω C hno Δ):Prop:=e.images = f.images ∧ e.parameters = f.parameters
namespace SameData
variable {e:ValEnv (hw:=hw) Ω C hno Γ} {f:ValEnv (hw:=hw) Ω C hno Δ}
variable (he:e.SameData f)
include he
theorem raw_eq (M:Expr S):M.subst e.images = M.subst f.images:=congrArg (M.subst) he.1
theorem expr_eq (M:Expr S):(M.subst e.images).nfTerm = (M.subst f.images).nfTerm :=
  congrArg Expr.nfTerm (he.raw_eq M)
theorem cons {A:Expr S} {n m:Expr S}
    (hn:Ω.HasType n (A.subst e.images)) (hm:Ω.HasType m (A.subst f.images))
    (hnm:n = m) (p:Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno (A.subst e.images).nfTerm p)
    (hp':PayFits Ω C hno (A.subst f.images).nfTerm p) :
    (e.cons hn p hp).SameData (f.cons hm p hp'):=by
  constructor
  · funext i; cases i with
    | zero => exact hnm
    | succ i => exact congrFun he.1 i
  · funext i; cases i with
    | zero => rfl
    | succ i => exact congrFun he.2 i
end SameData
end ValEnv
theorem preEval_recontext {Γ:List (Expr S)} {M T:Expr S} (t:TyTree P Γ M T)
    {Δ:List (Expr S)} (h:ContextEquivalent P Γ Δ)
    (e:ValEnv (hw:=hw) Ω C hno Γ) (f:ValEnv (hw:=hw) Ω C hno Δ)
    (hef:e.SameData f) :
    (preEval Ω C hno t e).parameter = (preEval Ω C hno (t.recontext h) f).parameter ∧
    (preEval Ω C hno t e).read.val = (preEval Ω C hno (t.recontext h) f).read.val:=by
  induction t generalizing Δ with
  | var ht hd hc =>
      have ht':=(h.typing _ _).mp ht
      let g:=ht'.generation
      have hparam:(PreRes.lookup ht hd hc e).parameter =
          (PreRes.lookup ht' g.choose_spec.1 g.choose_spec.2 f).parameter:=by
        rw [PreRes.lookup_parameter,PreRes.lookup_parameter]
        exact congrFun hef.2 _
      refine ⟨hparam,?_⟩
      apply PreRes.baseRead_congr ht ht' (hef.expr_eq _) (hef.expr_eq _)
      · exact Iff.rfl
      · exact fun ha hb => PreRes.val_congr _ _ hparam ha hb
  | sort ht ha hc =>
      constructor
      · apply PreRes.parameter_congr _ _ (hef.expr_eq _)
        intro hs hs'
        exact distinguished_congr Ω C hno (hef.expr_eq _)
      · exact congrArg (Cands.Top Ω) (hef.expr_eq _)
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have he:=hef.expr_eq T
      have hv:∀ ha ha',((preEval Ω C hno (.abstraction ht d b hp hc) e).val ha).val =
          ((preEval Ω C hno ((TyTree.abstraction ht d b hp hc).recontext h) f).val ha').val:=by
        apply PreRes.abstraction_val_congr ht ((h.typing _ _).mp ht) hp ((h.typing _ _).mp hp)
          hc hc _ _ e f he
        intro n m hn hm hnm p hpp hpp' ha ha'
        apply PreRes.val_congr
        exact (ihb (h.cons d.typing) (e.cons hn p hpp) (f.cons hm p hpp') (hef.cons hn hm hnm p hpp hpp')).1
      constructor
      · exact PreRes.parameter_congr _ _ he hv
      · apply PreRes.baseRead_congr ht ((h.typing _ _).mp ht) (hef.expr_eq _) he
        · exact Iff.rfl
        · exact hv
  | @application Γ g n D E T ht gtr ntr hc ihg ihn =>
      have hg:=ihg h e f hef
      have hn:=ihn h e f hef
      have he:=hef.expr_eq T
      have hv:∀ ha ha',((preEval Ω C hno (.application ht gtr ntr hc) e).val ha).val =
          ((preEval Ω C hno ((TyTree.application ht gtr ntr hc).recontext h) f).val ha').val:=by
        apply PreRes.application_val_congr ht ((h.typing _ _).mp ht) gtr.typing
          ((h.typing _ _).mp gtr.typing) ntr.typing ((h.typing _ _).mp ntr.typing)
          hc hc _ _ _ _ e f he (hef.expr_eq _) (hef.expr_eq _)
        · exact fun ha ha' => PreRes.val_congr _ _ hg.1 ha ha'
        · exact hn.1
      constructor
      · exact PreRes.parameter_congr _ _ he hv
      · apply PreRes.baseRead_congr ht ((h.typing _ _).mp ht) (hef.expr_eq _) he
        · exact Iff.rfl
        · exact hv
  | @product Γ D E a b c T ht d btr hr hc ihd ihb =>
      have hh:=(h.typing _ _).mp d.typing
      have hb:=((h.cons d.typing).typing _ _).mp btr.typing
      have hm:=hef.expr_eq (.pi D E)
      have he:=hef.expr_eq T
      have hDE:=Expr.pi.inj (hef.raw_eq (.pi D E))
      have hpc:∀ (_:Ω.profile (Expr.pi D E |>.subst e.images).nfTerm ∈ C),
          (PreRes.productCandidate d.typing btr.typing hr (preEval Ω C hno d)
            (preEval Ω C hno btr) e).val =
          (PreRes.productCandidate hh hb hr (preEval Ω C hno (d.recontext h))
            (preEval Ω C hno (btr.recontext (h.cons d.typing))) f).val:=by
        intro _
        apply PreRes.productCandidate_congr d.typing btr.typing hr hh hb hr _ _ _ _ e f
          (congrArg Expr.nfTerm hDE.1) (congrArg Expr.nfTerm hDE.2)
        · intro _
          exact (ihd h e f hef).2
        · intro n hn hn' p hp hp' _
          exact (ihb (h.cons d.typing) (e.cons hn p hp) (f.cons hn' p hp') (hef.cons hn hn' rfl p hp hp')).2
      constructor
      · apply PreRes.parameter_congr _ _ he
        apply PreRes.product_val_congr ht ((h.typing _ _).mp ht) d.typing btr.typing hr hh hb hr
          hc hc _ _ _ _ e f he hm Iff.rfl hpc
      · exact PreRes.product_read_congr ht ((h.typing _ _).mp ht) d.typing btr.typing hr hh hb hr
          hc hc _ _ _ _ e f hm hpc
end ObsVals
namespace Expr
variable {S:Type u}
def consSub (n:Expr S) (σ:Nat → Expr S):Nat → Expr S
  | 0 => n
  | i+1 => σ i
end Expr
namespace CTower
variable {S:Type u} {P:Specification S} (Ω:CTower P)
theorem profile_sort (s:S):Ω.profile (.sort s) = AxProfile P s:=by
  ext t
  change (∃ n,S_wpc_barendregt_geuvers_klop.HasType P (Ω.context n) ((Expr.sort s).nfTerm.rename (Expr.revIx n))
    ((Expr.sort t).rename (Expr.revIx n))) ↔ P.sortAxioms s t
  simp only [Expr.nfTerm_of_normal (Normal.sort s),Expr.rename]
  constructor
  · rintro ⟨n,hn⟩
    obtain ⟨u,ha,hc⟩:=hn.generation
    exact hc.sort_inj ▸ ha
  · intro h; exact ⟨0,S_wpc_barendregt_geuvers_klop.HasType.sort_of_valid (Ω.valid 0) h⟩
end CTower
namespace FeasibleProfile
variable {S:Type u} {P:Specification S}
theorem singleton {s:S} (h:(AxProfile P s).Nonempty):FeasibleProfile P {s}:=by
  obtain ⟨t,ht⟩:=h
  have hs:HasType P [] (.sort s) (.sort t):=.ax ht
  have hv:HasType P [.sort s] (.var 0) (.sort s):=.var hs
  exact ⟨Set.singleton_nonempty s,[.sort s],.var 0,hv.valid,Normal.var 0,
    Profile.neutral (Normal.var 0) (.var 0) hv⟩
end FeasibleProfile
namespace ObsVals
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) (C:Set (Set S))
def baseGood (M T:Expr S) (σ:Nat → Expr S) (v:Prop):Prop :=
  Ω.profile (M.subst σ) ∈ C →
    ∃ s,T = .sort s ∧ ({s}:Set S) ∈ C ∧
      (ActL P C (Ω.profile (T.subst σ)) → v) ∧
      (¬ ActL P C (Ω.profile (T.subst σ)) → Neutral M)
noncomputable def goodness {Γ:List (Expr S)} {M T:Expr S}
    (t:TyTree P Γ M T) (σ:Nat → Expr S):Prop × Prop :=
  match t with
  | .var _ _ _ => (True,baseGood Ω C M T σ True)
  | .sort _ _ _ => (True,True)
  | @TyTree.product _ _ _ D E _ _ c _ _ d e _ _ =>
    let g:=(Ω.profile (D.subst σ) ∈ C → (goodness d σ).2) ∧
      ∀ n,Ω.HasType n (D.subst σ) → Ω.profile (E.subst (Expr.consSub n σ)) ∈ C →
        (goodness e (Expr.consSub n σ)).2
    ((({c}:Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst σ) ∈ C) → g,
      Ω.profile (Expr.pi D E |>.subst σ) ∈ C → g)
  | @TyTree.abstraction _ _ _ D m E _ _ _ _ _ b _ _ =>
    let g:=∀ n,Ω.HasType n (D.subst σ) → ActL P C (Ω.profile (E.subst (Expr.consSub n σ))) →
      (goodness b (Expr.consSub n σ)).1
    (g,baseGood Ω C M T σ g)
  | @TyTree.application _ _ _ g n D E _ _ f a _ =>
    let v:=if ActL P C (Ω.profile (Expr.pi D E |>.subst σ)) then
      (goodness f σ).1 ∧ (ActL P C (Ω.profile (D.subst σ)) → (goodness a σ).1)
      else Neutral (.app g n)
    (v,baseGood Ω C M T σ v)
abbrev ValGood {Γ:List (Expr S)} {M T:Expr S} (t:TyTree P Γ M T) (σ:Nat → Expr S):Prop :=
  (goodness Ω C t σ).1
abbrev ReadGood {Γ:List (Expr S)} {M T:Expr S} (t:TyTree P Γ M T) (σ:Nat → Expr S):Prop :=
  (goodness Ω C t σ).2
def Relevant (Γ:List (Expr S)) (M:Expr S):Prop :=
  ∃ K ∈ C,Reach (PriEdge P) (Profile P Γ M) K
namespace Relevant
variable {Ω C}
theorem pred {Γ Δ:List (Expr S)} {M N:Expr S} (h:Relevant (P:=P) C Γ M)
    (hp:Reach (PriEdge P) (Profile P Δ N) (Profile P Γ M)):Relevant (P:=P) C Δ N:=by
  obtain ⟨K,hK,hp'⟩:=h
  exact ⟨K,hK,hp.trans hp'⟩
end Relevant
variable (hw:SystemWeaklyNormalizing P) (hC:IsComp (PriEdge P) C)
include hw hC
theorem relevant_actual_mem {Γ:List (Expr S)} {M:Expr S} {s:S} {σ:Nat → Expr S}
    (ht:HasType P Γ M (.sort s)) (hσ:Ω.TySub Γ σ)
    (hr:Relevant (P:=P) C Γ M) (hm:Ω.profile (M.subst σ) ∈ C):Profile P Γ M ∈ C:=by
  obtain ⟨K,hK,hp⟩:=hr
  have hg:=Ω.profile_subst_growth hw ht hσ
  have hga:=CTower.HasType.subst ht hσ
  have hpath:=Profile.inclusion_path (Ω.profile_feasible hw hga)
    (Profile.feasible (ht.weakNorm hw) (Profile.nonempty_of_sorted hw ht)) hg
  exact hC.between hm hK hpath.reach hp
theorem normal_baseGood {Γ:List (Expr S)} {M:Expr S} {s:S} {σ:Nat → Expr S}
    (h:HasType P Γ M (.sort s)) (hn:Normal M) (hne:Neutral M)
    (hσ:Ω.TySub Γ σ) (hr:Relevant (P:=P) C Γ M) {v:Prop}
    (hv:ActL P C (Ω.profile (Expr.sort s |>.subst σ)) → v) :
    baseGood Ω C M (.sort s) σ v:=by
  intro hm
  have hp:=relevant_actual_mem Ω C hw hC h hσ hr hm
  rw [Profile.neutral hn hne h] at hp
  exact ⟨s,rfl,hp,hv,fun _ => hne⟩
theorem normal_good {Γ:List (Expr S)} {M T:Expr S} (t:TyTree P Γ M T)
    (hn:Normal M) (σ:Nat → Expr S) (hσ:Ω.TySub Γ σ) :
    (ActL P C (Ω.profile (T.subst σ)) → ValGood Ω C t σ) ∧
    (∀ s,T = .sort s → Relevant (P:=P) C Γ M → ReadGood Ω C t σ):=by
  induction t generalizing σ with
  | var ht hd hc =>
      refine ⟨fun _ => trivial,?_⟩
      intro s hs hr
      subst hs
      exact normal_baseGood Ω C hw hC ht hn (.var _) hσ hr (fun _ => trivial)
  | sort ht ha hc => exact ⟨fun _ => trivial,fun _ _ _ => trivial⟩
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hv:ValGood Ω C (.abstraction ht d b hp hc) σ:=by
        intro n hn' ha
        exact (ihb hn.lam_body (Expr.consSub n σ) (hσ.cons hn')).1 ha
      refine ⟨fun _ => hv,?_⟩
      intro s hs _
      exact False.elim ((hs ▸ ht).lambda_cannot_have_sort_type)
  | @application Γ g n D E T ht f a hc ihf iha =>
      have hne:Neutral (.app g n):=by
        obtain ⟨s,he⟩ | hne | ⟨D,E,he⟩ | ⟨D,m,he⟩:=ht.normal_shape hn
        · cases he
        · exact hne
        · cases he
        · cases he
      have hv:ValGood Ω C (.application ht f a hc) σ:=by
        dsimp only [ValGood,goodness]
        split
        · rename_i hf
          exact ⟨(ihf hn.app_left σ hσ).1 hf,fun ha => (iha hn.app_right σ hσ).1 ha⟩
        · exact hne
      refine ⟨fun _ => hv,?_⟩
      intro s hs hr
      subst hs
      exact normal_baseGood Ω C hw hC ht hn hne hσ hr (fun _ => hv)
  | @product Γ D E a b c T ht d e hr hc ihd ihe =>
      have hpi:HasType P Γ (.pi D E) (.sort c):=.product d.typing e.typing hr
      have hp:=Profile.triple hw hpi
      have hg:Relevant (P:=P) C Γ (.pi D E) →
          (Ω.profile (D.subst σ) ∈ C → ReadGood Ω C d σ) ∧
          (∀ n,Ω.HasType n (D.subst σ) → Ω.profile (E.subst (Expr.consSub n σ)) ∈ C →
            ReadGood Ω C e (Expr.consSub n σ)):=by
        intro hrel
        constructor
        · intro _
          exact (ihd hn.pi_domain σ hσ).2 a rfl (hrel.pred (.single (.domain hp)))
        · intro n hn' _
          exact (ihe hn.pi_body (Expr.consSub n σ) (hσ.cons hn')).2 b rfl
            (hrel.pred (.single (.codomain hp)))
      constructor
      · intro hat hcc
        have hconv:(T.subst σ).nfTerm = .sort c :=
          (Expr.nfTerm_converts ((CTower.HasType.subst ht hσ).type_weakNorm hw)
            ((CTower.HasType.subst hpi hσ).type_weakNorm hw) (hc.subst σ)).trans
              (Expr.nfTerm_of_normal (Normal.sort c))
        have hax:(AxProfile P c).Nonempty:=by
          have hh:=hat.nonempty
          rwa [← Ω.profile_nfTerm (T.subst σ),hconv,Ω.profile_sort] at hh
        have hs:({c}:Set S) ⊆ Profile P Γ (.pi D E):=by
          intro r hr'
          have he:r = c:=hr'
          subst r
          exact hpi.nfTerm hw
        exact hg ⟨{c},hcc.1,(Profile.inclusion_path hp.product (FeasibleProfile.singleton hax) hs).reach⟩
      · intro _ _ hrel
        exact fun _ => hg hrel
end ObsVals
end S_wpc_barendregt_geuvers_klop
namespace S_wpc_barendregt_geuvers_klop.ObsVals
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
theorem normal_tree_independence {Γ:List (Expr S)} {M T:Expr S}
    (t:TyTree P Γ M T):Normal M →
    ∀ {U:Expr S} (t':TyTree P Γ M U) (e:ValEnv (hw:=hw) Ω C hno Γ),
    (Converts T U → (preEval Ω C hno t e).parameter = (preEval Ω C hno t' e).parameter) ∧
    (∀ s s',T = .sort s → U = .sort s' →
      (preEval Ω C hno t e).read.val = (preEval Ω C hno t' e).read.val):=by
  induction t with
  | @var Γ n A T ht hd hc =>
      intro _ U t' e
      cases t' with
      | var ht' hd' hc' =>
          have hv:(PreRes.lookup ht hd hc e).parameter = (PreRes.lookup ht' hd' hc' e).parameter:=by
            rw [PreRes.lookup_parameter,PreRes.lookup_parameter]
          refine ⟨fun _ => hv,?_⟩
          intro s s' hs hs'
          have he:s = s':=(hs ▸ hs' ▸ HasType.neutral_unique (.var n) ht ht').sort_inj
          subst s'; subst T; subst U
          apply PreRes.baseRead_congr ht ht' rfl rfl Iff.rfl
          exact fun ha hb => PreRes.val_congr _ _ hv ha hb
  | sort ht ha hc =>
      intro _ U t' e
      cases t' with
      | sort ht' ha' hc' =>
          constructor
          · intro hh
            apply PreRes.parameter_congr _ _ (e.type_convert_eq ht ht' hh)
            intro _ _
            exact distinguished_congr Ω C hno (e.type_convert_eq ht ht' hh)
          · exact fun _ _ _ _ => rfl
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      intro hn U t' e
      cases t' with
      | @abstraction _ _ _ E' a' s' _ ht' d' b' hp' hc' =>
          constructor
          · intro hh
            have hproducts:Converts (.pi D E) (.pi D E'):=.trans _ _ _ (.symm _ _ hc) (.trans _ _ _ hh hc')
            have hEE:=hproducts.product_compatibility.2
            apply PreRes.parameter_congr _ _ (e.type_convert_eq ht ht' hh)
            apply PreRes.abstraction_val_congr ht ht' hp hp' hc hc' _ _ e e (e.type_convert_eq ht ht' hh)
            intro n n' hnt hn' he p hpa hpb hact hact'
            subst n'
            exact PreRes.val_congr _ _ ((ihb hn.lam_body b' (e.cons hnt p hpa)).1 hEE) hact hact'
          · intro r r' hs _
            exact False.elim ((hs ▸ ht).lambda_cannot_have_sort_type)
  | @application Γ g n D E T ht f a hc ihf iha =>
      intro hn U t' e
      cases t' with
      | @application _ _ _ D' E' _ ht' f' a' hc' =>
          have hg:Neutral g:=by
            obtain ⟨s,he⟩ | hne | ⟨D,E,he⟩ | ⟨D,m,he⟩:=ht.normal_shape hn
            · cases he
            · cases hne with | app hne => exact hne
            · cases he
            · cases he
          have hF:=HasType.neutral_unique hg f.typing f'.typing
          have hD:=hF.product_compatibility.1
          have hv:∀ (hh:Converts T U),
              (preEval Ω C hno (.application ht f a hc) e).parameter =
              (preEval Ω C hno (.application ht' f' a' hc') e).parameter:=by
            intro hh
            apply PreRes.parameter_congr _ _ (e.type_convert_eq ht ht' hh)
            apply PreRes.application_val_congr ht ht' f.typing f'.typing a.typing a'.typing hc hc'
              _ _ _ _ e e (e.type_convert_eq ht ht' hh) (e.type_convert_eq f.typing f'.typing hF) rfl
            · exact fun ha hb => PreRes.val_congr _ _ ((ihf hn.app_left f' e).1 hF) ha hb
            · exact (iha hn.app_right a' e).1 hD
          refine ⟨hv,?_⟩
          intro s s' hs hs'
          have hh:=HasType.neutral_unique (.app hg) ht ht'
          have he:s = s':=(hs ▸ hs' ▸ hh).sort_inj
          subst s'; subst T; subst U
          apply PreRes.baseRead_congr ht ht' rfl rfl Iff.rfl
          exact fun ha hb => PreRes.val_congr _ _ (hv hh) ha hb
  | @product Γ D E a b c T ht d bt hr hc ihd ihb =>
      intro hn U t' e
      cases t' with
      | @product _ _ _ a' b' c' _ ht' d' bt' hr' hc' =>
          have hpc:(PreRes.productCandidate d.typing bt.typing hr (preEval Ω C hno d)
              (preEval Ω C hno bt) e).val =
              (PreRes.productCandidate d'.typing bt'.typing hr' (preEval Ω C hno d')
                (preEval Ω C hno bt') e).val:=by
            apply PreRes.productCandidate_congr d.typing bt.typing hr d'.typing bt'.typing hr' _ _ _ _ e e rfl rfl
            · exact fun _ => (ihd hn.pi_domain d' e).2 a a' rfl rfl
            · intro n hn' hn'' p hp hp' _
              exact (ihb hn.pi_body bt' (e.cons hn' p hp)).2 b b' rfl rfl
          constructor
          · intro hh
            have hsorts:Converts (.sort c) (.sort c'):=.trans _ _ _ (.symm _ _ hc) (.trans _ _ _ hh hc')
            have he:c = c':=hsorts.sort_inj
            apply PreRes.parameter_congr _ _ (e.type_convert_eq ht ht' hh)
            apply PreRes.product_val_congr ht ht' d.typing bt.typing hr d'.typing bt'.typing hr'
              hc hc' _ _ _ _ e e (e.type_convert_eq ht ht' hh) rfl
            · exact he ▸ Iff.rfl
            · exact fun _ => hpc
          · intro _ _ _ _
            exact PreRes.product_read_congr ht ht' d.typing bt.typing hr d'.typing bt'.typing hr'
              hc hc' _ _ _ _ e e rfl (fun _ => hpc)
end S_wpc_barendregt_geuvers_klop.ObsVals
namespace S_wpc_barendregt_geuvers_klop
universe u
namespace CTower.TySub
variable {S:Type u} {P:Specification S} {Ω:CTower P} {Γ:List (Expr S)}
    {σ τ:Nat → Expr S}
def Compatible (Γ:List (Expr S)) (σ τ:Nat → Expr S):Prop :=
  ∀ n,n < Γ.length → Converts (σ n) (τ n)
namespace Compatible
variable (hw:SystemWeaklyNormalizing P)
include hw
theorem expr_eq (he:Compatible Γ σ τ) (hσ:Ω.TySub Γ σ)
    (hτ:Ω.TySub Γ τ) {M A:Expr S} (h:S_wpc_barendregt_geuvers_klop.HasType P Γ M A) :
    (M.subst σ).nfTerm = (M.subst τ).nfTerm :=
  Expr.nfTerm_converts ((CTower.HasType.subst h hσ).weakNorm hw)
    ((CTower.HasType.subst h hτ).weakNorm hw) (h.scope.1.subst_converts he)
theorem type_eq (he:Compatible Γ σ τ) (hσ:Ω.TySub Γ σ)
    (hτ:Ω.TySub Γ τ) {M A:Expr S} (h:S_wpc_barendregt_geuvers_klop.HasType P Γ M A) :
    (A.subst σ).nfTerm = (A.subst τ).nfTerm :=
  Expr.nfTerm_converts ((CTower.HasType.subst h hσ).type_weakNorm hw)
    ((CTower.HasType.subst h hτ).type_weakNorm hw) (h.scope.2.subst_converts he)
omit hw in
theorem cons (he:Compatible Γ σ τ) {D n m:Expr S} (hh:Converts n m) :
    Compatible (D :: Γ) (Expr.consSub n σ) (Expr.consSub m τ):=by
  intro i hi
  cases i with
  | zero => exact hh
  | succ i => exact he i (Nat.lt_of_succ_lt_succ hi)
end Compatible
end CTower.TySub
namespace ObsVals
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) (C:Set (Set S))
variable (hw:SystemWeaklyNormalizing P)
include hw
end ObsVals
namespace Neutral
variable {S:Type u} {M:Expr S} {ρ:Nat → Nat}
theorem of_rename (h:Neutral (M.rename ρ)):Neutral M:=by
  induction M with
  | var n => exact .var n
  | sort s => cases h
  | lam D m ihD ihm => cases h
  | pi D E ihD ihE => cases h
  | app f n ihf ihn => cases h with | app h => exact .app (ihf h)
theorem rename_iff:Neutral (M.rename ρ) ↔ Neutral M:=⟨of_rename,fun h => h.rename ρ⟩
end Neutral
namespace Expr
variable {S:Type u}
theorem consSub_liftRen (n:Expr S) (σ:Nat → Expr S) (ρ:Nat → Nat) :
    (consSub n σ) ∘ liftRen ρ = consSub n (σ ∘ ρ):=by
  funext i; cases i <;> rfl
end Expr
namespace ObsVals
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) (C:Set (Set S))
theorem baseGood_rename {M T:Expr S} (ρ:Nat → Nat) (σ:Nat → Expr S) (v:Prop) :
    baseGood Ω C (M.rename ρ) (T.rename ρ) σ v ↔ baseGood Ω C M T (σ ∘ ρ) v:=by
  simp only [baseGood,Expr.subst_rename,Expr.rename_eq_sort,Neutral.rename_iff]
theorem goodness_rename {Γ:List (Expr S)} {M T:Expr S} (t:TyTree P Γ M T)
    {Δ:List (Expr S)} (hΔ:ValidContext P Δ) (ρ:Nat → Nat) (hρ:TyTree.DeclRenaming Γ Δ ρ)
    (σ:Nat → Expr S) :
    goodness Ω C (t.rename hΔ ρ hρ) σ = goodness Ω C t (σ ∘ ρ):=by
  induction t generalizing Δ ρ σ with
  | var ht hd hc =>
      apply Prod.ext
      · rfl
      · exact propext (baseGood_rename Ω C ρ σ True)
  | sort ht ha hc => rfl
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hh:HasType P Δ (D.rename ρ) (.sort a):=d.typing.rename hΔ ρ (hρ.typed hΔ)
      have hb (n:Expr S):=ihb (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D) (Expr.consSub n σ)
      simp only [Expr.consSub_liftRen] at hb
      have hv:(∀ n,Ω.HasType n ((D.rename ρ).subst σ) →
          ActL P C (Ω.profile ((E.rename (Expr.liftRen ρ)).subst (Expr.consSub n σ))) →
          (goodness Ω C (b.rename (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D)) (Expr.consSub n σ)).1) ↔
          (∀ n,Ω.HasType n (D.subst (σ ∘ ρ)) →
          ActL P C (Ω.profile (E.subst (Expr.consSub n (σ ∘ ρ)))) →
          (goodness Ω C b (Expr.consSub n (σ ∘ ρ))).1):=by
        simp only [Expr.subst_rename,Expr.consSub_liftRen,hb]
      apply Prod.ext
      · exact propext hv
      · change baseGood Ω C (Expr.lam D m |>.rename ρ) (T.rename ρ) σ _ = _
        exact (propext (baseGood_rename Ω C ρ σ _)).trans
          (congrArg (baseGood Ω C (.lam D m) T (σ ∘ ρ)) (propext hv))
  | @application Γ g n D E T ht f a hc ihf iha =>
      have hg:=ihf hΔ ρ hρ σ
      have hn:=iha hΔ ρ hρ σ
      have hv:(goodness Ω C ((TyTree.application ht f a hc).rename hΔ ρ hρ) σ).1 =
          (goodness Ω C (.application ht f a hc) (σ ∘ ρ)).1:=by
        change (if ActL P C (Ω.profile ((Expr.pi D E |>.rename ρ).subst σ)) then
          (goodness Ω C (f.rename hΔ ρ hρ) σ).1 ∧
            (ActL P C (Ω.profile ((D.rename ρ).subst σ)) → (goodness Ω C (a.rename hΔ ρ hρ) σ).1)
          else Neutral ((Expr.app g n).rename ρ)) =
          (if ActL P C (Ω.profile ((Expr.pi D E).subst (σ ∘ ρ))) then
            (goodness Ω C f (σ ∘ ρ)).1 ∧
              (ActL P C (Ω.profile (D.subst (σ ∘ ρ))) → (goodness Ω C a (σ ∘ ρ)).1)
            else Neutral (.app g n))
        rw [hg,hn]
        rw [Expr.subst_rename,Expr.subst_rename]
        split
        · rfl
        · exact propext Neutral.rename_iff
      apply Prod.ext hv
      change baseGood Ω C (Expr.app g n |>.rename ρ) (T.rename ρ) σ _ = _
      exact (propext (baseGood_rename Ω C ρ σ _)).trans
        (congrArg (baseGood Ω C (.app g n) T (σ ∘ ρ)) hv)
  | @product Γ D E a b c T ht d bt hr hc ihd ihb =>
      have hh:HasType P Δ (D.rename ρ) (.sort a):=d.typing.rename hΔ ρ (hρ.typed hΔ)
      have hd:=ihd hΔ ρ hρ σ
      have hb (n:Expr S):=ihb (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D) (Expr.consSub n σ)
      simp only [Expr.consSub_liftRen] at hb
      let g:Prop:=(Ω.profile ((D.rename ρ).subst σ) ∈ C →
          (goodness Ω C (d.rename hΔ ρ hρ) σ).2) ∧
          ∀ n,Ω.HasType n ((D.rename ρ).subst σ) →
            Ω.profile ((E.rename (Expr.liftRen ρ)).subst (Expr.consSub n σ)) ∈ C →
              (goodness Ω C (bt.rename (.cons hΔ hh) (Expr.liftRen ρ) (hρ.lift D)) (Expr.consSub n σ)).2
      let g':Prop:=(Ω.profile (D.subst (σ ∘ ρ)) ∈ C → (goodness Ω C d (σ ∘ ρ)).2) ∧
          ∀ n,Ω.HasType n (D.subst (σ ∘ ρ)) → Ω.profile (E.subst (Expr.consSub n (σ ∘ ρ))) ∈ C →
            (goodness Ω C bt (Expr.consSub n (σ ∘ ρ))).2
      have he:g = g':=by
        dsimp only [g,g']
        simp only [hd,hb,Expr.subst_rename,Expr.consSub_liftRen]
      change ((({c}:Set S) ∈ C ∧ Ω.profile ((Expr.pi D E |>.rename ρ).subst σ) ∈ C) → g,
        Ω.profile ((Expr.pi D E |>.rename ρ).subst σ) ∈ C → g) =
        ((({c}:Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst (σ ∘ ρ)) ∈ C) → g',
        Ω.profile (Expr.pi D E |>.subst (σ ∘ ρ)) ∈ C → g')
      simp only [Expr.subst_rename,he]
theorem valGood_retarget {Γ:List (Expr S)} {M T T':Expr S} (t:TyTree P Γ M T)
    (ht:HasType P Γ M T') (hc:Converts T' T) (σ:Nat → Expr S) :
    ValGood Ω C (t.retarget ht hc) σ ↔ ValGood Ω C t σ:=by
  cases t <;> exact Iff.rfl
end ObsVals
namespace CTower
variable {S:Type u} {P:Specification S} (Ω:CTower P)
theorem profile_converts {A B:Expr S} (hA:WeaklyNormalizing A) (hB:WeaklyNormalizing B)
    (hc:Converts A B):Ω.profile A = Ω.profile B:=by
  rw [← Ω.profile_nfTerm A,← Ω.profile_nfTerm B,Expr.nfTerm_converts hA hB hc]
variable (hw:SystemWeaklyNormalizing P)
include hw
theorem instantiate_profile_ascent {Γ:List (Expr S)} {D E n:Expr S} {s:S}
    (hp:S_wpc_barendregt_geuvers_klop.HasType P Γ (.pi D E) (.sort s))
    (hn:S_wpc_barendregt_geuvers_klop.HasType P Γ n D) {σ:Nat → Expr S} (hσ:Ω.TySub Γ σ) :
    PositivePath (PriEdge P) (Ω.profile ((E.instantiate n).subst σ))
      (Ω.profile (Expr.pi D E |>.subst σ)):=by
  have hp':=CTower.HasType.subst hp hσ
  have hn':=CTower.HasType.subst hn hσ
  obtain ⟨J,htr,hpath⟩:=Ω.frame_profiles hw hp' hn'
  rw [← Expr.instantiate_subst]
  exact hpath.trans (.single (.codomain htr))
theorem neutral_profile_ascent {Γ:List (Expr S)} {M T:Expr S}
    (hne:Neutral M) (ht:S_wpc_barendregt_geuvers_klop.HasType P Γ M T)
    {σ:Nat → Expr S} (hσ:Ω.TySub Γ σ) :
    ∃ n D,M.head = .var n ∧ Lookup Γ n D ∧
      PositivePath (PriEdge P) (Ω.profile (T.subst σ)) (Ω.profile (D.subst σ)):=by
  induction hne generalizing T with
  | var n =>
      obtain ⟨D,hd,hc⟩:=ht.generation
      refine ⟨n,D,rfl,hd,?_⟩
      rw [Ω.profile_converts ((CTower.HasType.subst ht hσ).type_weakNorm hw)
        ((CTower.HasType.subst (S_wpc_barendregt_geuvers_klop.HasType.lookup ht.valid hd) hσ).type_weakNorm hw)
        (hc.subst σ)]
      exact .refl
  | @app f a hnf ih =>
      obtain ⟨D,E,hf,ha,hc⟩:=ht.generation_app
      obtain ⟨s,hp⟩:=hf.product_type_sorted
      obtain ⟨n,A,hh,hl,hr⟩:=ih hf
      refine ⟨n,A,hh,hl,?_⟩
      rw [Ω.profile_converts ((CTower.HasType.subst ht hσ).type_weakNorm hw)
        ((CTower.HasType.subst (S_wpc_barendregt_geuvers_klop.HasType.application hf ha) hσ).type_weakNorm hw)
        (hc.subst σ)]
      exact (Ω.instantiate_profile_ascent hw hp ha hσ).trans hr
end CTower
namespace ObsVals
variable {S:Type u} {P:Specification S} (Ω:CTower P) (C:Set (Set S))
    (hw:SystemWeaklyNormalizing P)
def SubstitutionGuard (Γ:List (Expr S)) (σ ξ:Nat → Expr S):Prop :=
  ∀ n D,Lookup Γ n D → ¬ Neutral (σ n) → Ω.profile (D.subst ξ) ∈ ObsLayers P C →
    ActL P C (Ω.profile (D.subst ξ))
include hw
 theorem neutral_subst_of_inactive {Γ:List (Expr S)} {M T:Expr S}
    (hne:Neutral M) (ht:HasType P Γ M T) {σ ξ:Nat → Expr S}
    (hξ:Ω.TySub Γ ξ) (hguard:SubstitutionGuard Ω C Γ σ ξ)
    (hH:Ω.profile (T.subst ξ) ∈ ObsLayers P C)
    (hina:¬ ActL P C (Ω.profile (T.subst ξ))):Neutral (M.subst σ):=by
  apply hne.subst_of_head
  intro n hhead
  by_contra hn
  obtain ⟨i,D,hhead',hd,hpath⟩:=Ω.neutral_profile_ascent hw hne ht hξ
  have he:i = n:=Expr.var.inj (hhead'.symm.trans hhead)
  subst i
  have hI:=ObsLayers.positive hH hpath
  exact hina ((hguard n D hd hn hI).predecessor (ObsLayers.secondary hH hpath).reach)
 theorem skipped_application_subst {Γ:List (Expr S)} {f a D E T:Expr S}
    (h:HasType P Γ (.app f a) T) (hf:HasType P Γ f (.pi D E)) (ha:HasType P Γ a D)
    (hc:Converts T (E.instantiate a)) (hne:Neutral (.app f a))
    {σ ξ:Nat → Expr S} (hξ:Ω.TySub Γ ξ)
    (hguard:SubstitutionGuard Ω C Γ σ ξ)
    (hactive:ActL P C (Ω.profile (T.subst ξ)))
    (hina:¬ ActL P C (Ω.profile (Expr.pi D E |>.subst ξ))) :
    Neutral (Expr.app f a |>.subst σ):=by
  have hF:Ω.profile (Expr.pi D E |>.subst ξ) ∈ ObsLayers P C:=by
    obtain ⟨s,hp⟩:=hf.product_type_sorted
    have he:=Ω.profile_converts ((CTower.HasType.subst h hξ).type_weakNorm hw)
      ((CTower.HasType.subst (HasType.application hf ha) hξ).type_weakNorm hw) (hc.subst ξ)
    exact ObsLayers.positive (he ▸ hactive.layer) (Ω.instantiate_profile_ascent hw hp ha hξ)
  have hnf:Neutral f:=by cases hne; assumption
  exact .app (neutral_subst_of_inactive Ω C hw hnf hf hξ hguard hF hina)
 theorem skipped_read_subst {Γ:List (Expr S)} {M:Expr S} {s:S}
    (h:HasType P Γ M (.sort s)) (hne:Neutral M)
    {σ ξ:Nat → Expr S} (hξ:Ω.TySub Γ ξ)
    (hguard:SubstitutionGuard Ω C Γ σ ξ) (hs:({s}:Set S) ∈ C)
    (hina:¬ ActL P C (AxProfile P s)):Neutral (M.subst σ):=by
  have hH:AxProfile P s ∈ ObsLayers P C :=
    ⟨s,hs,Profile.neutral_axiom hne h,.refl⟩
  apply neutral_subst_of_inactive Ω C hw hne h hξ hguard
  · simpa only [Expr.subst,Ω.profile_sort] using hH
  · simpa only [Expr.subst,Ω.profile_sort] using hina
end ObsVals
end S_wpc_barendregt_geuvers_klop
namespace S_wpc_barendregt_geuvers_klop.ObsVals
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
theorem distinguished_base (T:ActTy Ω C) :
    RawValue.base (hw:=hw) Ω C hno (distinguished (hw:=hw) Ω C hno T).val = topBase Ω:=by
  unfold distinguished
  split
  · exact (ActPlain.schema hw).distinguished_base _ _ _
  · split
    · rfl
    · rfl
namespace PreRes
variable {Ω C hno} {Γ:List (Expr S)} {M:Expr S} {s:S}
    {e:ValEnv (hw:=hw) Ω C hno Γ}
theorem baseRead_eq (h:HasType P Γ M (.sort s))
    (v:ActL P C (Ω.profile (Expr.sort s |>.subst e.images).nfTerm) →
      Value (hw:=hw) Ω C hno (Expr.sort s |>.subst e.images).nfTerm)
    (hM:Ω.profile (M.subst e.images).nfTerm ∈ C) (hs:({s}:Set S) ∈ C)
    (ha:ActL P C (Ω.profile (Expr.sort s |>.subst e.images).nfTerm)) :
    (baseRead h v).val = ((RawValue.base Ω C hno (v ha).val) (e.actualExpression h)).val:=by
  have hex:∃ s',Expr.sort s = Expr.sort s' ∧ ({s'}:Set S) ∈ C:=⟨s,rfl,hs⟩
  simp only [baseRead,dif_pos hM,dif_pos hex,dif_pos ha]
theorem product_read_base {D E:Expr S} {a b c:S}
    (h:HasType P Γ (.pi D E) (.sort s))
    (hd:HasType P Γ D (.sort a)) (hb:HasType P (D :: Γ) E (.sort b))
    (hr:P.rule a b c) (hc:Converts (.sort s) (.sort c))
    (ed:Evaluator (hw:=hw) Ω C hno Γ D (.sort a))
    (eb:Evaluator (hw:=hw) Ω C hno (D :: Γ) E (.sort b))
    (e:ValEnv (hw:=hw) Ω C hno Γ)
    (hm:Ω.profile (Expr.pi D E |>.subst e.images).nfTerm ∈ C) (hs:({s}:Set S) ∈ C)
    (ha:ActL P C (Ω.profile (Expr.sort s |>.subst e.images).nfTerm)) :
    (product h hd hb hr hc ed eb e).read.val =
      ((RawValue.base Ω C hno ((product h hd hb hr hc ed eb e).val ha).val) (e.actualExpression h)).val:=by
  have hh:({c}:Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst e.images).nfTerm ∈ C:=⟨hc.sort_inj ▸ hs,hm⟩
  dsimp only [product]
  rw [if_pos hm,dif_pos hh,withBase_base]
  simp only [Base.update_same]
end PreRes
theorem preEval_read_base {Γ:List (Expr S)} {M:Expr S} {s:S}
    (t:TyTree P Γ M (.sort s)) (e:ValEnv (hw:=hw) Ω C hno Γ)
    (hM:Ω.profile (M.subst e.images).nfTerm ∈ C) (hs:({s}:Set S) ∈ C)
    (ha:ActL P C (Ω.profile (Expr.sort s |>.subst e.images).nfTerm)) :
    (preEval Ω C hno t e).read.val =
      ((RawValue.base Ω C hno ((preEval Ω C hno t e).val ha).val) (e.actualExpression t.typing)).val:=by
  cases t with
  | var ht hd hc => exact PreRes.baseRead_eq ht _ hM hs ha
  | sort ht hax hc =>
      change (Cands.Top Ω (Expr.sort _ |>.subst e.images).nfTerm) = _
      rw [show ((preEval Ω C hno (.sort ht hax hc) e).val ha).val =
        (distinguished Ω C hno (e.activeType ht ha)).val from rfl,distinguished_base]
      rfl
  | product ht d b hr hc => exact PreRes.product_read_base ht d.typing b.typing hr hc _ _ e hM hs ha
  | abstraction ht d b hp hc => exact PreRes.baseRead_eq ht _ hM hs ha
  | application ht f a hc => exact PreRes.baseRead_eq ht _ hM hs ha
omit hno [Fintype S] in
theorem baseGood_active_iff {M:Expr S} {s:S} {σ:Nat → Expr S} {v:Prop}
    (hm:Ω.profile (M.subst σ) ∈ C) (hs:({s}:Set S) ∈ C)
    (ha:ActL P C (Ω.profile (Expr.sort s |>.subst σ))) :
    baseGood Ω C M (.sort s) σ v ↔ v:=by
  constructor
  · intro h
    obtain ⟨s',_,_,hv,_⟩:=h hm
    exact hv ha
  · intro hv _
    exact ⟨s,rfl,hs,fun _ => hv,fun hn => False.elim (hn ha)⟩
omit hno [Fintype S] in
theorem readGood_active_iff {Γ:List (Expr S)} {M:Expr S} {s:S}
    (t:TyTree P Γ M (.sort s)) {σ:Nat → Expr S}
    (hm:Ω.profile (M.subst σ) ∈ C) (hs:({s}:Set S) ∈ C)
    (ha:ActL P C (Ω.profile (Expr.sort s |>.subst σ))) :
    ReadGood Ω C t σ ↔ ValGood Ω C t σ:=by
  cases t with
  | var ht hd hc => exact baseGood_active_iff Ω C hm hs ha
  | sort ht hax hc => exact Iff.rfl
  | product ht d b hr hc =>
      dsimp only [ReadGood,ValGood,goodness]
      have hc':=hc.sort_inj
      simp only [← hc',hm,hs,true_and,true_implies]
  | abstraction ht d b hp hc => exact baseGood_active_iff Ω C hm hs ha
  | application ht f a hc => exact baseGood_active_iff Ω C hm hs ha
end S_wpc_barendregt_geuvers_klop.ObsVals
end OMA
namespace OMA
namespace S_wpc_barendregt_geuvers_klop
universe u
namespace Expr
variable {S:Type u}
def compSub (σ ξ:Nat → Expr S):Nat → Expr S:=fun n => (σ n).subst ξ
@[simp] theorem subst_compSub (M:Expr S) (σ ξ:Nat → Expr S) :
    (M.subst σ).subst ξ = M.subst (compSub σ ξ):=subst_subst M ξ σ
@[simp] theorem lift_comp_cons (σ ξ:Nat → Expr S) (n:Expr S) :
    compSub (liftSub σ) (consSub n ξ) = consSub n (compSub σ ξ):=by
  funext i; cases i with
  | zero => rfl
  | succ i => simp only [compSub,liftSub_succ,subst_rename,Function.comp_def,consSub]
@[simp] theorem raise_subst_cons (M n:Expr S) (ξ:Nat → Expr S) :
    (M.rename Nat.succ).subst (consSub n ξ) = M.subst ξ:=by
  rw [subst_rename]; rfl
end Expr
namespace ObsVals
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) (C:Set (Set S))
namespace SubstitutionGuard
variable {Ω C} {Γ Δ:List (Expr S)} {σ ξ:Nat → Expr S}
theorem lift (hg:SubstitutionGuard Ω C Γ σ (Expr.compSub σ ξ)) (D n:Expr S) :
    SubstitutionGuard Ω C (D :: Γ) (Expr.liftSub σ)
      (Expr.compSub (Expr.liftSub σ) (Expr.consSub n ξ)):=by
  rw [Expr.lift_comp_cons]
  intro i A hi hne hH
  cases hi with
  | zero => exact False.elim (hne (.var 0))
  | succ D hi =>
      have hne':¬ Neutral (σ _):=fun h => hne (h.rename Nat.succ)
      simpa only [Expr.raise_subst_cons] using hg _ _ hi hne' (by
        simpa only [Expr.raise_subst_cons] using hH)
end SubstitutionGuard
def GoodReplacement {Γ Δ:List (Expr S)} {σ:Nat → Expr S}
    (ts:TyTree.StoredSubstitution P Γ Δ σ) (ξ:Nat → Expr S):Prop :=
  ∀ i A (hi:Lookup Γ i A),ActL P C (Ω.profile (A.subst (Expr.compSub σ ξ))) →
    ValGood Ω C (ts i A hi) ξ
 theorem goodReplacement_lift {Γ Δ:List (Expr S)} {σ ξ:Nat → Expr S}
    (ts:TyTree.StoredSubstitution P Γ Δ σ) (hg:GoodReplacement Ω C ts ξ)
    {D:Expr S} {s:S} (hD:HasType P Δ (D.subst σ) (.sort s)) (n:Expr S) :
    GoodReplacement Ω C (ts.lift hD) (Expr.consSub n ξ):=by
  intro i A hi ha
  cases i with
  | zero =>
      have he:A = D.rename Nat.succ:=by cases hi; rfl
      subst A
      exact True.intro
  | succ i =>
      let hex:∃ A',Lookup Γ i A' ∧ A = A'.rename Nat.succ:=by
        cases hi with | succ _ hi => exact ⟨_,hi,rfl⟩
      have he:=hex.choose_spec.2
      have hgood:=hg i hex.choose hex.choose_spec.1
      have hh:ActL P C (Ω.profile (hex.choose.subst (Expr.compSub σ ξ))):=by
        rw [Expr.lift_comp_cons,he,Expr.raise_subst_cons] at ha
        exact ha
      have hr:=congrArg Prod.fst (goodness_rename Ω C (ts i hex.choose hex.choose_spec.1)
        (.cons hD.valid hD) Nat.succ (TyTree.DeclRenaming.weaken _) (Expr.consSub n ξ))
      have hgr:ValGood Ω C ((ts i hex.choose hex.choose_spec.1).rename (.cons hD.valid hD)
          Nat.succ (TyTree.DeclRenaming.weaken _)) (Expr.consSub n ξ):=by
        rw [show ValGood Ω C _ _ = _ from hr]
        exact hgood hh
      let tt:=(ts i hex.choose hex.choose_spec.1).rename (.cons hD.valid hD)
        Nat.succ (TyTree.DeclRenaming.weaken _)
      have he':A.subst (Expr.liftSub σ) = (hex.choose.subst σ).rename Nat.succ:=by
        calc
          A.subst (Expr.liftSub σ) = (hex.choose.rename Nat.succ).subst (Expr.liftSub σ) :=
            congrArg (Expr.subst (Expr.liftSub σ)) he
          _ = (hex.choose.subst σ).rename Nat.succ:=by
            rw [Expr.subst_rename,Expr.rename_subst]; rfl
      exact (valGood_retarget Ω C tt (he'.symm ▸ tt.typing)
        (by rw [he']; exact .refl _) (Expr.consSub n ξ)).mpr hgr
 theorem neutral_readGood {Γ:List (Expr S)} {M:Expr S} {s:S}
    (t:TyTree P Γ M (.sort s)) (hne:Neutral M) (ξ:Nat → Expr S)
    (hs:({s}:Set S) ∈ C) (ha:¬ ActL P C (AxProfile P s)):ReadGood Ω C t ξ:=by
  have hbase (v:Prop):baseGood Ω C M (.sort s) ξ v:=by
    intro _
    refine ⟨s,rfl,hs,?_,fun _ => hne⟩
    intro hh
    exact False.elim (ha (by simpa only [Expr.subst,Ω.profile_sort] using hh))
  cases t with
  | var ht hd hc => exact hbase True
  | sort ht hax hc => cases hne
  | product ht d b hr hc => cases hne
  | abstraction ht d b hp hc => cases hne
  | application ht f a hc => exact hbase _
end ObsVals
end S_wpc_barendregt_geuvers_klop
namespace S_wpc_barendregt_geuvers_klop.ObsVals
section
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
namespace PreRes
variable {Ω C hno} {Γ:List (Expr S)} {M T U:Expr S}
 theorem sort_val_retarget {s t:S} (h:HasType P Γ (.sort s) T)
    (h':HasType P Γ (.sort s) U) (ht:P.sortAxioms s t) (hc:Converts T (.sort t))
    (hc':Converts U (.sort t)) (e:ValEnv (hw:=hw) Ω C hno Γ)
    (he:(T.subst e.images).nfTerm = (U.subst e.images).nfTerm)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (hb:ActL P C (Ω.profile (U.subst e.images).nfTerm)) :
    ((sort h ht hc e).val ha).val = ((sort h' ht hc' e).val hb).val :=
  distinguished_congr Ω C hno he
 theorem lookup_val_retarget {n:Nat} {A:Expr S} (h:HasType P Γ (.var n) T)
    (h':HasType P Γ (.var n) U) (hd:Lookup Γ n A) (hc:Converts T A)
    (hc':Converts U A) (e:ValEnv (hw:=hw) Ω C hno Γ)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (hb:ActL P C (Ω.profile (U.subst e.images).nfTerm)) :
    ((lookup h hd hc e).val ha).val = ((lookup h' hd hc' e).val hb).val:=by
  apply Option.some.inj
  rw [← parameter_eq _ ha,← parameter_eq _ hb,lookup_parameter,lookup_parameter]
 theorem abstractionAction_retarget {D m E:Expr S} {s:S}
    (h:HasType P Γ (.lam D m) T) (h':HasType P Γ (.lam D m) U)
    (hp:HasType P Γ (.pi D E) (.sort s)) (hc:Converts T (.pi D E))
    (hc':Converts U (.pi D E))
    (eb:Evaluator (hw:=hw) Ω C hno (D :: Γ) m E)
    (e:ValEnv (hw:=hw) Ω C hno Γ)
    (he:(T.subst e.images).nfTerm = (U.subst e.images).nfTerm)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (hb:ActL P C (Ω.profile (U.subst e.images).nfTerm))
    (a:FrameKey Ω C (e.activeType h ha)) (b:FrameKey Ω C (e.activeType h' hb))
    (hab:a.argument = b.argument) (p:Option (RawValue (hw:=hw) Ω C hno))
    (hpa:PayFits Ω C hno a.domain p) (hpb:PayFits Ω C hno b.domain p) :
    (abstractionAction h hp hc eb e ha a p hpa).val =
      (abstractionAction h' hp hc' eb e hb b p hpb).val:=by
  have hA:(e.activeType h ha).type = (ProdInst.ofFormation hp e).domainNF.pi
      (ProdInst.ofFormation hp e).bodyNF :=
    (Expr.nfTerm_converts ((CTower.HasType.subst h e.typed).type_weakNorm hw)
      ((CTower.HasType.subst hp e.typed).weakNorm hw) (hc.subst e.images)).trans
      (ProdInst.ofFormation hp e).product_nf
  have hB:(e.activeType h' hb).type = (ProdInst.ofFormation hp e).domainNF.pi
      (ProdInst.ofFormation hp e).bodyNF :=
    he.symm.trans hA
  have hee:(ProdInst.ofFormation hp e).frameValEnv hA a p hpa =
      (ProdInst.ofFormation hp e).frameValEnv hB b p hpb:=by
    dsimp only [ProdInst.frameValEnv,ProdInst.extend,ValEnv.cons]
    congr 1
    funext n
    cases n <;> simp only [hab]
  dsimp only [abstractionAction]
  apply val_congr
  exact congrArg (fun ee:ValEnv (hw:=hw) Ω C hno (D :: Γ) => (eb ee).parameter) hee
 theorem abstraction_val_retarget {D m E:Expr S} {s:S}
    (h:HasType P Γ (.lam D m) T) (h':HasType P Γ (.lam D m) U)
    (hp:HasType P Γ (.pi D E) (.sort s)) (hc:Converts T (.pi D E))
    (hc':Converts U (.pi D E))
    (eb:Evaluator (hw:=hw) Ω C hno (D :: Γ) m E)
    (e:ValEnv (hw:=hw) Ω C hno Γ)
    (he:(T.subst e.images).nfTerm = (U.subst e.images).nfTerm)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (hb:ActL P C (Ω.profile (U.subst e.images).nfTerm)) :
    ((abstraction h hp hc eb e).val ha).val = ((abstraction h' hp hc' eb e).val hb).val:=by
  apply lambdaValue_congr Ω C hno he
  exact abstractionAction_retarget h h' hp hc hc' eb e he ha hb
 theorem product_val_retarget {D E:Expr S} {a b c:S}
    (h:HasType P Γ (.pi D E) T) (h':HasType P Γ (.pi D E) U)
    (hd:HasType P Γ D (.sort a)) (hb:HasType P (D :: Γ) E (.sort b))
    (hr:P.rule a b c) (hc:Converts T (.sort c)) (hc':Converts U (.sort c))
    (ed:Evaluator (hw:=hw) Ω C hno Γ D (.sort a))
    (eb:Evaluator (hw:=hw) Ω C hno (D :: Γ) E (.sort b))
    (e:ValEnv (hw:=hw) Ω C hno Γ)
    (he:(T.subst e.images).nfTerm = (U.subst e.images).nfTerm)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (hu:ActL P C (Ω.profile (U.subst e.images).nfTerm)) :
    ((product h hd hb hr hc ed eb e).val ha).val = ((product h' hd hb hr hc' ed eb e).val hu).val:=by
  dsimp only [product]
  split
  · exact withBase_congr Ω C hno he _ _ rfl
  · exact distinguished_congr Ω C hno he
 theorem application_val_retarget {f n D E:Expr S}
    (h:HasType P Γ (.app f n) T) (h':HasType P Γ (.app f n) U)
    (hf:HasType P Γ f (.pi D E)) (hn:HasType P Γ n D)
    (hc:Converts T (E.instantiate n)) (hc':Converts U (E.instantiate n))
    (ef:Evaluator (hw:=hw) Ω C hno Γ f (.pi D E))
    (en:Evaluator (hw:=hw) Ω C hno Γ n D)
    (e:ValEnv (hw:=hw) Ω C hno Γ)
    (he:(T.subst e.images).nfTerm = (U.subst e.images).nfTerm)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (hu:ActL P C (Ω.profile (U.subst e.images).nfTerm)) :
    ((application h hf hn hc ef en e).val ha).val = ((application h' hf hn hc' ef en e).val hu).val:=by
  dsimp only [application,baseResult,applicationValue]
  split
  · rfl
  · exact distinguished_congr Ω C hno he
end PreRes
 theorem preEvaluate_retarget_val {Γ:List (Expr S)} {M T U:Expr S} (t:TyTree P Γ M T)
    (h:HasType P Γ M U) (hc:Converts U T) (e:ValEnv (hw:=hw) Ω C hno Γ)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (hb:ActL P C (Ω.profile (U.subst e.images).nfTerm)) :
    ((preEval Ω C hno t e).val ha).val =
      ((preEval Ω C hno (t.retarget h hc) e).val hb).val:=by
  have he:=e.type_convert_eq t.typing h (.symm _ _ hc)
  cases t with
  | var ht hd ht' => exact PreRes.lookup_val_retarget ht h hd ht' (.trans _ _ _ hc ht') e ha hb
  | sort ht ht' htc => exact PreRes.sort_val_retarget ht h ht' htc (.trans _ _ _ hc htc) e he ha hb
  | product ht d b hr htc => exact PreRes.product_val_retarget ht h d.typing b.typing hr htc (.trans _ _ _ hc htc) _ _ e he ha hb
  | abstraction ht d b hp htc => exact PreRes.abstraction_val_retarget ht h hp htc (.trans _ _ _ hc htc) _ e he ha hb
  | application ht f n htc => exact PreRes.application_val_retarget ht h f.typing n.typing htc (.trans _ _ _ hc htc) _ _ e he ha hb
 theorem preEvaluate_retarget_parameter {Γ:List (Expr S)} {M T U:Expr S}
    (t:TyTree P Γ M T) (h:HasType P Γ M U) (hc:Converts U T)
    (e:ValEnv (hw:=hw) Ω C hno Γ) :
    (preEval Ω C hno t e).parameter = (preEval Ω C hno (t.retarget h hc) e).parameter:=by
  apply PreRes.parameter_congr _ _ (e.type_convert_eq t.typing h (.symm _ _ hc))
  exact preEvaluate_retarget_val Ω C hno t h hc e
namespace ValEnv
variable {Ω C hno} {Γ Δ:List (Expr S)} {σ:Nat → Expr S}
structure Assigned (e:ValEnv (hw:=hw) Ω C hno Γ)
    (f:ValEnv (hw:=hw) Ω C hno Δ) (ts:TyTree.StoredSubstitution P Γ Δ σ):Prop where
  images:e.images = Expr.compSub σ f.images
  parameters:∀ i A (hi:Lookup Γ i A),
    e.parameters i = (preEval Ω C hno (ts i A hi) f).parameter
namespace Assigned
variable {e:ValEnv (hw:=hw) Ω C hno Γ} {f:ValEnv (hw:=hw) Ω C hno Δ}
variable {ts:TyTree.StoredSubstitution P Γ Δ σ} (he:e.Assigned f ts)
include he
 theorem raw_eq (M:Expr S):M.subst e.images = (M.subst σ).subst f.images:=by
  rw [he.images,Expr.subst_compSub]
 theorem normal_eq (M:Expr S) :
    (M.subst e.images).nfTerm = ((M.subst σ).subst f.images).nfTerm :=
  congrArg Expr.nfTerm (he.raw_eq M)
 theorem cons {D:Expr S} {s:S} (hD:HasType P Δ (D.subst σ) (.sort s))
    (n:Expr S) (hn:Ω.HasType n (D.subst e.images)) (hn':Ω.HasType n ((D.subst σ).subst f.images))
    (p:Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno (D.subst e.images).nfTerm p)
    (hp':PayFits Ω C hno ((D.subst σ).subst f.images).nfTerm p) :
    (e.cons hn p hp).Assigned (f.cons hn' p hp') (ts.lift hD):=by
  constructor
  · change Expr.consSub n e.images = Expr.compSub (Expr.liftSub σ) (Expr.consSub n f.images)
    rw [Expr.lift_comp_cons,he.images]
  · intro i A hi
    cases i with
    | zero =>
        have heA:A = D.rename Nat.succ:=by cases hi; rfl
        have he':A.subst (Expr.liftSub σ) = (D.subst σ).rename Nat.succ:=by
          rw [heA,Expr.subst_rename,Expr.rename_subst]; rfl
        exact (PreRes.lookup_parameter (he'.symm ▸ HasType.var hD) (.zero _ _)
          (by rw [he']; exact .refl _) (f.cons hn' p hp')).symm
    | succ i =>
        let hex:∃ A',Lookup Γ i A' ∧ A = A'.rename Nat.succ:=by
          cases hi with | succ _ hi => exact ⟨_,hi,rfl⟩
        let tt:=(ts i hex.choose hex.choose_spec.1).rename (.cons hD.valid hD)
          Nat.succ (TyTree.DeclRenaming.weaken _)
        have he':A.subst (Expr.liftSub σ) = (hex.choose.subst σ).rename Nat.succ:=by
          calc
            A.subst (Expr.liftSub σ) = (hex.choose.rename Nat.succ).subst (Expr.liftSub σ) :=
              congrArg (Expr.subst (Expr.liftSub σ)) hex.choose_spec.2
            _ = (hex.choose.subst σ).rename Nat.succ:=by
              rw [Expr.subst_rename,Expr.rename_subst]; rfl
        have hr:=(preEvaluate_rename Ω C hno (ts i hex.choose hex.choose_spec.1)
          (.cons hD.valid hD) Nat.succ (TyTree.DeclRenaming.weaken _) f (f.cons hn' p hp')
          (fun _ _ => ⟨rfl,rfl⟩)).1
        exact (he.parameters i hex.choose hex.choose_spec.1).trans
          (hr.trans (preEvaluate_retarget_parameter Ω C hno tt (he'.symm ▸ tt.typing)
            (by rw [he']; exact .refl _) (f.cons hn' p hp')))
end Assigned
end ValEnv
 theorem preEvaluate_read_outside {Γ:List (Expr S)} {M T:Expr S}
    (t:TyTree P Γ M T) (e:ValEnv (hw:=hw) Ω C hno Γ)
    (hm:Ω.profile (M.subst e.images).nfTerm ∉ C) :
    (preEval Ω C hno t e).read.val = Cands.Top Ω (M.subst e.images).nfTerm:=by
  cases t with
  | var ht hd hc => exact by simp only [preEval,PreRes.lookup,PreRes.baseResult,PreRes.baseRead,dif_neg hm]
  | sort ht ha hc => rfl
  | product ht d b hr hc => exact by simp only [preEval,PreRes.product,if_neg hm]
  | abstraction ht d b hp hc => exact by simp only [preEval,PreRes.abstraction,PreRes.baseResult,PreRes.baseRead,dif_neg hm]
  | application ht f a hc => exact by simp only [preEval,PreRes.application,PreRes.baseResult,PreRes.baseRead,dif_neg hm]
 theorem preEvaluate_neutral_read_inactive {Γ:List (Expr S)} {M:Expr S} {s:S}
    (t:TyTree P Γ M (.sort s)) (e:ValEnv (hw:=hw) Ω C hno Γ)
    (hne:Neutral M) (ha:¬ ActL P C (Ω.profile (Expr.sort s |>.subst e.images).nfTerm)) :
    (preEval Ω C hno t e).read.val = Cands.Top Ω (M.subst e.images).nfTerm:=by
  have hb (v:ActL P C (Ω.profile (Expr.sort s |>.subst e.images).nfTerm) →
      Value (hw:=hw) Ω C hno (Expr.sort s |>.subst e.images).nfTerm) :
      (PreRes.baseRead t.typing v).val = Cands.Top Ω (M.subst e.images).nfTerm:=by
    simp only [PreRes.baseRead,dif_neg ha]
    split <;> try rfl
    split <;> rfl
  cases t with
  | var ht hd hc => exact hb _
  | sort ht ha hc => cases hne
  | product ht d b hr hc => cases hne
  | abstraction ht d b hp hc => cases hne
  | application ht f a hc => exact hb _
end
section
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) (C:Set (Set S))
 theorem readGood_outside {Γ:List (Expr S)} {M T:Expr S} (t:TyTree P Γ M T)
    (ξ:Nat → Expr S) (hm:Ω.profile (M.subst ξ) ∉ C):ReadGood Ω C t ξ:=by
  cases t with
  | var ht hd hc => exact fun h => False.elim (hm h)
  | sort ht ha hc => trivial
  | product ht d b hr hc => exact fun h => False.elim (hm h)
  | abstraction ht d b hp hc => exact fun h => False.elim (hm h)
  | application ht f a hc => exact fun h => False.elim (hm h)
abbrev ProductGood {Γ:List (Expr S)} {D E:Expr S} {a b:S}
    (d:TyTree P Γ D (.sort a)) (e:TyTree P (D :: Γ) E (.sort b)) (ξ:Nat → Expr S):Prop :=
  (Ω.profile (D.subst ξ) ∈ C → ReadGood Ω C d ξ) ∧
    ∀ n,Ω.HasType n (D.subst ξ) → Ω.profile (E.subst (Expr.consSub n ξ)) ∈ C →
      ReadGood Ω C e (Expr.consSub n ξ)
 theorem goodness_subst (hw:SystemWeaklyNormalizing P)
    {Γ:List (Expr S)} {M T:Expr S} (t:TyTree P Γ M T)
    {Δ:List (Expr S)} (hΔ:ValidContext P Δ) (σ:Nat → Expr S)
    (ts:TyTree.StoredSubstitution P Γ Δ σ) (ξ:Nat → Expr S)
    (hξ:Ω.TySub Δ ξ)
    (hguard:SubstitutionGuard Ω C Γ σ (Expr.compSub σ ξ)) (hg:GoodReplacement Ω C ts ξ) :
    (ActL P C (Ω.profile (T.subst (Expr.compSub σ ξ))) →
      ValGood Ω C t (Expr.compSub σ ξ) → ValGood Ω C (t.subst hΔ σ ts) ξ) ∧
    (ReadGood Ω C t (Expr.compSub σ ξ) → ReadGood Ω C (t.subst hΔ σ ts) ξ):=by
  induction t generalizing Δ σ ξ with
  | @var Γ i A T ht hd hc =>
      have hcomp:=hξ.comp ts.typed
      have hprof:=Ω.profile_converts ((CTower.HasType.subst ht hcomp).type_weakNorm hw)
        ((CTower.HasType.subst (HasType.lookup ht.valid hd) hcomp).type_weakNorm hw)
        (hc.subst (Expr.compSub σ ξ))
      have hv:ActL P C (Ω.profile (T.subst (Expr.compSub σ ξ))) →
          ValGood Ω C ((TyTree.var ht hd hc).subst hΔ σ ts) ξ:=by
        intro ha
        change ValGood Ω C ((ts i A hd).retarget (ht.subst hΔ σ ts.typed) (hc.subst σ)) ξ
        exact (valGood_retarget Ω C _ _ _ _).mpr (hg i A hd (hprof ▸ ha))
      refine ⟨fun ha _ => hv ha,?_⟩
      intro hr
      by_cases hm:Ω.profile ((Expr.var i).subst (Expr.compSub σ ξ)) ∈ C
      · obtain ⟨s,he,hs,_,_⟩:=hr hm
        subst T
        by_cases ha:ActL P C (Ω.profile (Expr.sort s |>.subst (Expr.compSub σ ξ)))
        · exact (readGood_active_iff Ω C ((TyTree.var ht hd hc).subst hΔ σ ts)
            (by exact hm) hs (by exact ha)).mpr (hv ha)
        · apply neutral_readGood Ω C _ _ ξ hs (by simpa only [Expr.subst,Ω.profile_sort] using ha)
          exact skipped_read_subst Ω C hw ht (.var i) hcomp hguard hs
            (by simpa only [Expr.subst,Ω.profile_sort] using ha)
      · exact readGood_outside Ω C _ ξ hm
  | sort ht ha hc => exact ⟨fun _ _ => trivial,fun _ => trivial⟩
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hD:=d.typing.subst hΔ σ ts.typed
      let bs:=b.subst (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD)
      have hbody:ValGood Ω C (.abstraction ht d b hp hc) (Expr.compSub σ ξ) →
          ValGood Ω C ((TyTree.abstraction ht d b hp hc).subst hΔ σ ts) ξ:=by
        intro hb n hn ha
        have hn':Ω.HasType n (D.subst (Expr.compSub σ ξ)):=by simpa only [Expr.subst_compSub] using hn
        have hi:=(ihb (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD) (Expr.consSub n ξ)
          (hξ.cons hn) (hguard.lift D n) (goodReplacement_lift Ω C ts hg hD n)).1
        apply hi
        · simpa only [Expr.subst_compSub] using ha
        · rw [Expr.lift_comp_cons]
          exact hb n hn' (by simpa only [Expr.subst_compSub,Expr.lift_comp_cons] using ha)
      refine ⟨fun _ => hbody,?_⟩
      intro hr hm
      have hm':Ω.profile (Expr.lam D m |>.subst (Expr.compSub σ ξ)) ∈ C:=by
        simpa only [Expr.subst_compSub] using hm
      obtain ⟨s',he,hs,hv,hn⟩:=hr hm'
      subst T
      exact False.elim ht.lambda_cannot_have_sort_type
  | @application Γ f n D E T ht ft nt hc ihf ihn =>
      have hcomp:=hξ.comp ts.typed
      have hv:ActL P C (Ω.profile (T.subst (Expr.compSub σ ξ))) →
          ValGood Ω C (.application ht ft nt hc) (Expr.compSub σ ξ) →
          ValGood Ω C ((TyTree.application ht ft nt hc).subst hΔ σ ts) ξ:=by
        intro ha hg'
        change (if ActL P C (Ω.profile (Expr.pi D E |>.subst (Expr.compSub σ ξ))) then
          ValGood Ω C ft (Expr.compSub σ ξ) ∧
            (ActL P C (Ω.profile (D.subst (Expr.compSub σ ξ))) → ValGood Ω C nt (Expr.compSub σ ξ))
          else Neutral (.app f n)) at hg'
        change (if ActL P C (Ω.profile ((Expr.pi D E |>.subst σ).subst ξ)) then
          ValGood Ω C (ft.subst hΔ σ ts) ξ ∧
            (ActL P C (Ω.profile ((D.subst σ).subst ξ)) → ValGood Ω C (nt.subst hΔ σ ts) ξ)
          else Neutral ((Expr.app f n).subst σ))
        simp only [Expr.subst_compSub]
        split <;> rename_i hF
        · rw [if_pos hF] at hg'
          exact ⟨(ihf hΔ σ ts ξ hξ hguard hg).1 hF hg'.1,
            fun hA => (ihn hΔ σ ts ξ hξ hguard hg).1 hA (hg'.2 hA)⟩
        · rw [if_neg hF] at hg'
          exact skipped_application_subst Ω C hw ht ft.typing nt.typing hc hg' hcomp hguard ha hF
      refine ⟨hv,?_⟩
      intro hr hm
      have hm':Ω.profile (Expr.app f n |>.subst (Expr.compSub σ ξ)) ∈ C:=by
        simpa only [Expr.subst_compSub] using hm
      obtain ⟨s,he,hs,hval,hne⟩:=hr hm'
      subst T
      refine ⟨s,rfl,hs,?_,?_⟩
      · intro ha
        apply hv (by exact ha)
        exact hval (by exact ha)
      · intro ha
        have hax:¬ ActL P C (AxProfile P s):=by simpa only [Expr.subst,Ω.profile_sort] using ha
        exact skipped_read_subst Ω C hw ht (hne (by exact ha)) hcomp hguard hs hax
  | @product Γ D E a b c T ht d bt hr hc ihd ihb =>
      have hD:=d.typing.subst hΔ σ ts.typed
      have hpg:ProductGood Ω C d bt (Expr.compSub σ ξ) →
          ProductGood Ω C (d.subst hΔ σ ts) (bt.subst (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD)) ξ:=by
        intro hh
        constructor
        · intro hm
          exact (ihd hΔ σ ts ξ hξ hguard hg).2 (hh.1 (by simpa only [Expr.subst_compSub] using hm))
        · intro n hn hm
          have hn':Ω.HasType n (D.subst (Expr.compSub σ ξ)):=by simpa only [Expr.subst_compSub] using hn
          apply (ihb (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD) (Expr.consSub n ξ)
            (hξ.cons hn) (hguard.lift D n) (goodReplacement_lift Ω C ts hg hD n)).2
          rw [Expr.lift_comp_cons]
          exact hh.2 n hn' (by simpa only [Expr.subst_compSub,Expr.lift_comp_cons] using hm)
      constructor
      · intro _ hv hgate
        apply hpg
        apply hv
        change ({c}:Set S) ∈ C ∧ Ω.profile (((Expr.pi D E).subst σ).subst ξ) ∈ C at hgate
        simpa only [Expr.subst_compSub] using hgate
      · intro hr' hm
        apply hpg
        apply hr'
        change Ω.profile (((Expr.pi D E).subst σ).subst ξ) ∈ C at hm
        simpa only [Expr.subst_compSub] using hm
end
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
 theorem baseRead_substitution {Γ Δ:List (Expr S)} {M T:Expr S} {σ:Nat → Expr S}
    (ht:HasType P Γ M T) (t':TyTree P Δ (M.subst σ) (T.subst σ))
    (e:ValEnv (hw:=hw) Ω C hno Γ) (f:ValEnv (hw:=hw) Ω C hno Δ)
    (he:e.images = Expr.compSub σ f.images)
    (hg:SubstitutionGuard Ω C Γ σ e.images)
    (v:ActL P C (Ω.profile (T.subst e.images).nfTerm) →
      Value (hw:=hw) Ω C hno (T.subst e.images).nfTerm) (G:Prop)
    (hr:baseGood Ω C M T e.images G)
    (hv:∀ ha hb,G → (v ha).val = ((preEval Ω C hno t' f).val hb).val) :
    (PreRes.baseRead ht v).val = (preEval Ω C hno t' f).read.val:=by
  have hM:(M.subst e.images).nfTerm = ((M.subst σ).subst f.images).nfTerm:=by
    rw [he,Expr.subst_compSub]
  by_cases hm:Ω.profile (M.subst e.images).nfTerm ∈ C
  · have hm':Ω.profile ((M.subst σ).subst f.images).nfTerm ∈ C:=hM ▸ hm
    obtain ⟨s,hs,hsC,hval,hne⟩:=hr (by simpa only [Ω.profile_nfTerm] using hm)
    subst T
    by_cases ha:ActL P C (Ω.profile (Expr.sort s |>.subst e.images).nfTerm)
    · refine Eq.trans (PreRes.baseRead_eq ht v hm hsC ha)
        (Eq.trans ?_ (preEval_read_base Ω C hno t' f hm' hsC ha).symm)
      have hX:e.actualExpression ht = f.actualExpression t'.typing:=Subtype.ext hM
      rw [hv ha ha (hval (by simpa only [Ω.profile_nfTerm] using ha))]
      exact congrArg (fun X:ActualType Ω =>
        ((RawValue.base Ω C hno ((preEval Ω C hno t' f).val ha).val) X).val) hX
    · have hnew:=skipped_read_subst Ω C hw ht
        (hne (by simpa only [Ω.profile_nfTerm] using ha)) e.typed hg hsC
        (by simpa only [Expr.subst,Ω.profile_nfTerm,Ω.profile_sort] using ha)
      refine Eq.trans ?_ (preEvaluate_neutral_read_inactive Ω C hno t' f hnew ha).symm
      have hex:∃ s',Expr.sort s = Expr.sort s' ∧ ({s'}:Set S) ∈ C:=⟨s,rfl,hsC⟩
      simp only [PreRes.baseRead,dif_pos hm,dif_pos hex,dif_neg ha]
      exact congrArg (Cands.Top Ω) hM
  · have hm':Ω.profile ((M.subst σ).subst f.images).nfTerm ∉ C:=hM ▸ hm
    rw [preEvaluate_read_outside Ω C hno t' f hm']
    simp only [PreRes.baseRead,dif_neg hm]
    exact congrArg (Cands.Top Ω) hM
 theorem preEvaluate_subst {Γ:List (Expr S)} {M T:Expr S} (t:TyTree P Γ M T)
    {Δ:List (Expr S)} (hΔ:ValidContext P Δ) (σ:Nat → Expr S)
    (ts:TyTree.StoredSubstitution P Γ Δ σ)
    (e:ValEnv (hw:=hw) Ω C hno Γ) (f:ValEnv (hw:=hw) Ω C hno Δ)
    (he:e.Assigned f ts) (hg:SubstitutionGuard Ω C Γ σ e.images) :
    (∀ ha hb,ValGood Ω C t e.images →
      ((preEval Ω C hno t e).val ha).val =
        ((preEval Ω C hno (t.subst hΔ σ ts) f).val hb).val) ∧
    (ReadGood Ω C t e.images →
      (preEval Ω C hno t e).read.val = (preEval Ω C hno (t.subst hΔ σ ts) f).read.val):=by
  induction t generalizing Δ σ with
  | @var Γ i A T ht hd hc =>
      have hp:(preEval Ω C hno (.var ht hd hc) e).parameter =
          (preEval Ω C hno ((TyTree.var ht hd hc).subst hΔ σ ts) f).parameter:=by
        exact (PreRes.lookup_parameter ht hd hc e).trans
          ((he.parameters i A hd).trans (preEvaluate_retarget_parameter Ω C hno
            (ts i A hd) (ht.subst hΔ σ ts.typed) (hc.subst σ) f))
      have hv:∀ ha hb,ValGood Ω C (.var ht hd hc) e.images →
          ((preEval Ω C hno (.var ht hd hc) e).val ha).val =
            ((preEval Ω C hno ((TyTree.var ht hd hc).subst hΔ σ ts) f).val hb).val :=
        fun ha hb _ => PreRes.val_congr _ _ hp ha hb
      exact ⟨hv,fun hr => baseRead_substitution Ω C hno ht _ e f he.images hg _ _ hr hv⟩
  | sort ht ha hc =>
      exact ⟨fun _ _ _ => distinguished_congr Ω C hno (he.normal_eq _),
        fun _ => congrArg (Cands.Top Ω) (he.normal_eq _)⟩
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hD:=d.typing.subst hΔ σ ts.typed
      have hv:∀ ha hb,ValGood Ω C (.abstraction ht d b hp hc) e.images →
          ((preEval Ω C hno (.abstraction ht d b hp hc) e).val ha).val =
            ((preEval Ω C hno ((TyTree.abstraction ht d b hp hc).subst hΔ σ ts) f).val hb).val:=by
        intro ha hb hgood
        apply PreRes.abstraction_val_congr ht (ht.subst hΔ σ ts.typed) hp
          (hp.subst hΔ σ ts.typed) hc (hc.subst σ) _ _ e f (he.normal_eq _)
        intro n n' hn hn' hnn p hp hp' ha' hb'
        subst n'
        have hae:=he.cons hD n hn hn' p hp hp'
        have hgu:SubstitutionGuard Ω C (D :: Γ) (Expr.liftSub σ) (e.cons hn p hp).images:=by
          rw [hae.images]
          apply SubstitutionGuard.lift
          rwa [← he.images]
        exact (ihb (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD)
          (e.cons hn p hp) (f.cons hn' p hp') hae hgu).1 ha' hb'
          (hgood n hn (by
            change ActL P C (Ω.profile (E.subst (Expr.consSub n e.images)).nfTerm) at ha'
            simpa only [Ω.profile_nfTerm] using ha'))
      exact ⟨hv,fun hr => baseRead_substitution Ω C hno ht _ e f he.images hg _ _ hr hv⟩
  | @application Γ g n D E T ht gt nt hc ihg ihn =>
      have hv:∀ ha hb,ValGood Ω C (.application ht gt nt hc) e.images →
          ((preEval Ω C hno (.application ht gt nt hc) e).val ha).val =
            ((preEval Ω C hno ((TyTree.application ht gt nt hc).subst hΔ σ ts) f).val hb).val:=by
        intro ha hb hgood
        by_cases hF:ActL P C (Ω.profile (Expr.pi D E |>.subst e.images))
        · change (if ActL P C (Ω.profile (Expr.pi D E |>.subst e.images)) then
            ValGood Ω C gt e.images ∧ (ActL P C (Ω.profile (D.subst e.images)) → ValGood Ω C nt e.images)
            else Neutral (.app g n)) at hgood
          rw [if_pos hF] at hgood
          apply PreRes.application_val_congr ht (ht.subst hΔ σ ts.typed) gt.typing
            (gt.typing.subst hΔ σ ts.typed) nt.typing (nt.typing.subst hΔ σ ts.typed)
            hc _ _ _ _ _ e f (he.normal_eq _) (he.normal_eq _) (he.normal_eq _)
          · exact fun hA hB => (ihg hΔ σ ts e f he hg).1 hA hB hgood.1
          · apply PreRes.parameter_congr _ _ (he.normal_eq _)
            intro hA hB
            exact (ihn hΔ σ ts e f he hg).1 hA hB (hgood.2 (by simpa only [Ω.profile_nfTerm] using hA))
        · have hF':¬ ActL P C (Ω.profile (((Expr.pi D E).subst σ).subst f.images).nfTerm):=by
            rw [← he.normal_eq _ ,Ω.profile_nfTerm]
            exact hF
          have hF0:¬ ActL P C (Ω.profile (Expr.pi D E |>.subst e.images).nfTerm):=by
            simpa only [Ω.profile_nfTerm] using hF
          change ((PreRes.application ht gt.typing nt.typing hc _ _ e).val ha).val =
            ((PreRes.application (ht.subst hΔ σ ts.typed) (gt.typing.subst hΔ σ ts.typed)
              (nt.typing.subst hΔ σ ts.typed) _ _ _ f).val hb).val
          change ¬ ActL P C (Ω.profile ((Expr.pi (D.subst σ) (E.subst (Expr.liftSub σ))).subst f.images).nfTerm) at hF'
          simp only [PreRes.application,PreRes.baseResult,PreRes.applicationValue,dif_neg hF0,dif_neg hF']
          exact distinguished_congr Ω C hno (he.normal_eq T)
      exact ⟨hv,fun hr => baseRead_substitution Ω C hno ht _ e f he.images hg _ _ hr hv⟩
  | @product Γ D E a b c T ht d bt hr hc ihd ihb =>
      have hD:=d.typing.subst hΔ σ ts.typed
      have hB:=bt.typing.subst (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD).typed
      have hpc:ProductGood Ω C d bt e.images →
          (PreRes.productCandidate d.typing bt.typing hr (preEval Ω C hno d)
            (preEval Ω C hno bt) e).val =
          (PreRes.productCandidate hD hB hr (preEval Ω C hno (d.subst hΔ σ ts))
            (preEval Ω C hno (bt.subst (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD))) f).val:=by
        intro hgood
        have hDE:=Expr.pi.inj (he.raw_eq (.pi D E))
        apply PreRes.productCandidate_congr d.typing bt.typing hr hD hB hr _ _ _ _ e f
          (congrArg Expr.nfTerm hDE.1) (congrArg Expr.nfTerm hDE.2)
        · intro hm
          exact (ihd hΔ σ ts e f he hg).2 (hgood.1 (by simpa only [Ω.profile_nfTerm] using hm))
        · intro n hn hn' p hp hp' hm
          have hae:=he.cons hD n hn hn' p hp hp'
          have hgu:SubstitutionGuard Ω C (D :: Γ) (Expr.liftSub σ) (e.cons hn p hp).images:=by
            rw [hae.images]
            apply SubstitutionGuard.lift
            rwa [← he.images]
          exact (ihb (.cons hΔ hD) (Expr.liftSub σ) (ts.lift hD)
            (e.cons hn p hp) (f.cons hn' p hp') hae hgu).2
            (hgood.2 n hn (by
              change Ω.profile (E.subst (Expr.consSub n e.images)).nfTerm ∈ C at hm
              simpa only [Ω.profile_nfTerm] using hm))
      constructor
      · intro ha hb hv
        by_cases hs:({c}:Set S) ∈ C
        · apply PreRes.product_val_congr ht (ht.subst hΔ σ ts.typed) d.typing bt.typing hr
            hD hB hr hc (hc.subst σ) _ _ _ _ e f (he.normal_eq _) (he.normal_eq _) Iff.rfl
          intro hm
          exact hpc (hv ⟨hs,by simpa only [Ω.profile_nfTerm] using hm⟩)
        · have hgate:¬ (({c}:Set S) ∈ C ∧ Ω.profile (Expr.pi D E |>.subst e.images).nfTerm ∈ C):=fun h => hs h.1
          have hgate':¬ (({c}:Set S) ∈ C ∧ Ω.profile (((Expr.pi D E).subst σ).subst f.images).nfTerm ∈ C):=fun h => hs h.1
          change ((PreRes.product ht d.typing bt.typing hr hc _ _ e).val ha).val =
            ((PreRes.product (ht.subst hΔ σ ts.typed) hD hB hr (hc.subst σ) _ _ f).val hb).val
          change ¬ (({c}:Set S) ∈ C ∧ Ω.profile ((Expr.pi (D.subst σ) (E.subst (Expr.liftSub σ))).subst f.images).nfTerm ∈ C) at hgate'
          simp only [PreRes.product,dif_neg hgate,dif_neg hgate']
          exact distinguished_congr Ω C hno (he.normal_eq T)
      · intro hgood
        apply PreRes.product_read_congr ht (ht.subst hΔ σ ts.typed) d.typing bt.typing hr
          hD hB hr hc (hc.subst σ) _ _ _ _ e f (he.normal_eq _)
        intro hm
        exact hpc (hgood (by simpa only [Ω.profile_nfTerm] using hm))
end S_wpc_barendregt_geuvers_klop.ObsVals
namespace S_wpc_barendregt_geuvers_klop
universe u
namespace Expr
variable {S:Type u}
@[simp] theorem comp_single (n:Expr S) (ξ:Nat → Expr S) :
    compSub (single n) ξ = consSub (n.subst ξ) ξ:=by
  funext i; cases i <;> rfl
end Expr
namespace TyTree.StoredSubstitution
variable {S:Type u} {P:Specification S} {Γ:List (Expr S)} {n D:Expr S}
noncomputable def single (t:TyTree P Γ n D) :
    StoredSubstitution P (D :: Γ) Γ (Expr.single n) :=
  fun i => match i with
  | 0 => fun A hi => by
      have he:A = D.rename Nat.succ:=by cases hi; rfl
      have he':A.subst (Expr.single n) = D:=by rw [he,Expr.subst_lift_single]
      exact t.retarget (he'.symm ▸ t.typing) (by rw [he']; exact .refl _)
  | i+1 => fun A hi => by
      let hex:∃ B,Lookup Γ i B ∧ A = B.rename Nat.succ:=by
        cases hi with | succ _ hi => exact ⟨_,hi,rfl⟩
      have he:A.subst (Expr.single n) = hex.choose:=by
        exact (congrArg (Expr.subst (Expr.single n)) hex.choose_spec.2).trans
          (Expr.subst_lift_single hex.choose n)
      exact .var (he.symm ▸ HasType.lookup t.typing.valid hex.choose_spec.1)
        hex.choose_spec.1 (by rw [he]; exact .refl _)
end TyTree.StoredSubstitution
namespace ObsVals
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
omit [Fintype S] in
 theorem goodness_recontext {Γ:List (Expr S)} {M T:Expr S} (t:TyTree P Γ M T)
    {Δ:List (Expr S)} (h:ContextEquivalent P Γ Δ) (ξ:Nat → Expr S) :
    goodness Ω C (t.recontext h) ξ = goodness Ω C t ξ:=by
  induction t generalizing Δ ξ with
  | var ht hd hc => rfl
  | sort ht ha hc => rfl
  | @abstraction Γ D m E a s T ht d b hp hc ihd ihb =>
      have hv:(∀ n,Ω.HasType n (D.subst ξ) → ActL P C (Ω.profile (E.subst (Expr.consSub n ξ))) →
          (goodness Ω C (b.recontext (h.cons d.typing)) (Expr.consSub n ξ)).1) =
        (∀ n,Ω.HasType n (D.subst ξ) → ActL P C (Ω.profile (E.subst (Expr.consSub n ξ))) →
          (goodness Ω C b (Expr.consSub n ξ)).1):=by simp only [ihb]
      exact congrArg (fun G => (G,baseGood Ω C (.lam D m) T ξ G)) hv
  | @application Γ f n D E T ht ft nt hc ihf ihn =>
      have hv:(if ActL P C (Ω.profile ((Expr.pi D E).subst ξ)) then
          (goodness Ω C (ft.recontext h) ξ).1 ∧
            (ActL P C (Ω.profile (D.subst ξ)) → (goodness Ω C (nt.recontext h) ξ).1)
          else Neutral (.app f n)) =
        (if ActL P C (Ω.profile ((Expr.pi D E).subst ξ)) then
          (goodness Ω C ft ξ).1 ∧
            (ActL P C (Ω.profile (D.subst ξ)) → (goodness Ω C nt ξ).1)
          else Neutral (.app f n)):=by simp only [ihf,ihn]
      exact congrArg (fun G => (G,baseGood Ω C (.app f n) T ξ G)) hv
  | @product Γ D E a b c T ht d b hr hc ihd ihb =>
      have hg:((Ω.profile (D.subst ξ) ∈ C → (goodness Ω C (d.recontext h) ξ).2) ∧
          ∀ n,Ω.HasType n (D.subst ξ) → Ω.profile (E.subst (Expr.consSub n ξ)) ∈ C →
            (goodness Ω C (b.recontext (h.cons d.typing)) (Expr.consSub n ξ)).2) =
        ((Ω.profile (D.subst ξ) ∈ C → (goodness Ω C d ξ).2) ∧
          ∀ n,Ω.HasType n (D.subst ξ) → Ω.profile (E.subst (Expr.consSub n ξ)) ∈ C →
            (goodness Ω C b (Expr.consSub n ξ)).2):=by simp only [ihd,ihb]
      exact congrArg (fun G => ((({c}:Set S) ∈ C ∧ Ω.profile ((Expr.pi D E).subst ξ) ∈ C → G),
        (Ω.profile ((Expr.pi D E).subst ξ) ∈ C → G))) hg
omit [Fintype S] in
 theorem single_guard {Γ:List (Expr S)} {n D:Expr S} (ξ:Nat → Expr S)
    (ha:Ω.profile (D.subst ξ) ∈ ObsLayers P C → ActL P C (Ω.profile (D.subst ξ))) :
    SubstitutionGuard Ω C (D :: Γ) (Expr.single n) (Expr.consSub (n.subst ξ) ξ):=by
  intro i A hi hne hH
  cases hi with
  | zero => simpa only [Expr.raise_subst_cons] using ha (by simpa only [Expr.raise_subst_cons] using hH)
  | succ D hi => exact False.elim (hne (.var _))
omit [Fintype S] in
 theorem single_goodReplacement {Γ:List (Expr S)} {n D:Expr S}
    (t:TyTree P Γ n D) (ξ:Nat → Expr S)
    (hg:ActL P C (Ω.profile (D.subst ξ)) → ValGood Ω C t ξ) :
    GoodReplacement Ω C (TyTree.StoredSubstitution.single t) ξ:=by
  intro i A hi ha
  cases i with
  | zero =>
      have he:A = D.rename Nat.succ:=by cases hi; rfl
      have he':A.subst (Expr.single n) = D:=by rw [he,Expr.subst_lift_single]
      exact (valGood_retarget Ω C t (he'.symm ▸ t.typing) (by rw [he']; exact .refl _) ξ).mpr (hg (by
        simpa only [Expr.comp_single,he,Expr.raise_subst_cons] using ha))
  | succ i => exact True.intro
 theorem single_assigned {Γ:List (Expr S)} {n D:Expr S} (t:TyTree P Γ n D)
    (e:ValEnv (hw:=hw) Ω C hno Γ) :
    (e.cons (CTower.HasType.subst t.typing e.typed) (preEval Ω C hno t e).parameter
      (preEval Ω C hno t e).parameter_fits).Assigned e (TyTree.StoredSubstitution.single t):=by
  constructor
  · exact (Expr.comp_single n e.images).symm
  · intro i A hi
    cases i with
    | zero =>
        have he:A = D.rename Nat.succ:=by cases hi; rfl
        have he':A.subst (Expr.single n) = D:=by rw [he,Expr.subst_lift_single]
        exact preEvaluate_retarget_parameter Ω C hno t (he'.symm ▸ t.typing)
          (by rw [he']; exact .refl _) e
    | succ i =>
        let hex:∃ B,Lookup Γ i B ∧ A = B.rename Nat.succ:=by
          cases hi with | succ _ hi => exact ⟨_,hi,rfl⟩
        have he:A.subst (Expr.single n) = hex.choose:=by
          exact (congrArg (Expr.subst (Expr.single n)) hex.choose_spec.2).trans
            (Expr.subst_lift_single hex.choose n)
        exact (PreRes.lookup_parameter (he.symm ▸ HasType.lookup t.typing.valid hex.choose_spec.1)
          hex.choose_spec.1 (by rw [he]; exact .refl _) e).symm
end ObsVals
end S_wpc_barendregt_geuvers_klop
end OMA
namespace OMA
namespace S_wpc_barendregt_geuvers_klop.ObsVals
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
namespace Value
variable {Ω C hno}
@[simp] theorem asPlus_plus {T:Expr S} (hT:FreeL P C (Ω.profile T) false)
    (p:Plus (hw:=hw) Ω C hno):asPlus hT ⟨.plus p,hT⟩ = p :=
  RawValue.plus.inj (asPlus_spec hT ⟨.plus p,hT⟩).symm
@[simp] theorem asMinus_minus {T:Expr S} (hT:FreeL P C (Ω.profile T) true)
    (p:Minus (hw:=hw) Ω C hno):asMinus hT ⟨.minus p,hT⟩ = p :=
  RawValue.minus.inj (asMinus_spec hT ⟨.minus p,hT⟩).symm
end Value
theorem plain_beta (T:ActTy Ω C) (hT:PlainL P C (Ω.profile T.type))
    (act:LambdaAction (hw:=hw) Ω C hno T) (a:FrameKey Ω C T)
    (p:Option (RawValue (hw:=hw) Ω C hno)) (hp:PayFits Ω C hno a.domain p) :
    plainApply Ω C hno T hT (plainLambda Ω C hno T hT act) a p hp = act a p hp:=by
  simp only [plainApply,plainLambda,Value.asPlain_plain,Equiv.apply_symm_apply]
  simp only [ActualPlainKey.payload_parameters]
  exact Value.plain_asPlain (ActPlain.Key.target hw (a.plainKey hT)) (act a p hp)
theorem exitValue_tag (T:ActTy Ω C) (hT:PlainL P C (Ω.profile T.type))
    (v:Value (hw:=hw) Ω C hno T.type) :
    exitValue Ω C hno T (some (tagPlain Ω C hno T hT v)) = v:=by
  simp only [exitValue,tagPlain_spec,project_valid]
theorem lambdaExit_parameter {X:Type u}
    (decode:FreeObs.Payload (PlainValue (hw:=hw) Ω C hno) X →
      Option (RawValue (hw:=hw) Ω C hno))
    (T:ActTy Ω C) (act:LambdaAction (hw:=hw) Ω C hno T)
    (a:FrameKey Ω C T) (p:Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno a.domain p)
    (q:FreeObs.Payload (PlainValue (hw:=hw) Ω C hno) X) (hq:decode q = p)
    (ht:PlainL P C (Ω.profile (a.target hw).type)) :
    lambdaExit Ω C hno decode T act (a.argument,q) =
      some (tagPlain Ω C hno (a.target hw) ht (act a p hp)):=by
  have hg:Gate Ω C hno T a.argument (decode q) true :=
    ⟨a,rfl,hq.symm ▸ hp,⟨fun _ => rfl,fun _ => ht⟩⟩
  simp only [lambdaExit,dif_pos hg]
  subst p
  have H:∀ (k:FrameKey Ω C T),k = a →
      ∀ (hpk:PayFits Ω C hno k.domain (decode q))
        (htk:PlainL P C (Ω.profile (k.target hw).type)),
      some (tagPlain Ω C hno (k.target hw) htk (act k (decode q) hpk)) =
        some (tagPlain Ω C hno (a.target hw) ht (act a (decode q) hp)):=by
    intro k hk
    subst k
    intro hpk htk
    rfl
  exact H hg.frame (Gate.unique hg a rfl) hg.payload hg.plain
theorem plusContinue_gate (T:ActTy Ω C)
    (hT:FreeL P C (Ω.profile T.type) false) (act:LambdaAction (hw:=hw) Ω C hno T)
    (a:FrameKey Ω C T) (q:PlusFrame (hw:=hw) Ω C hno) (hqa:q.1 = a.argument)
    (p:Option (RawValue (hw:=hw) Ω C hno)) (hp:PayFits Ω C hno a.domain p)
    (hq:plusPayload Ω C hno q.2 = p)
    (ht:¬ PlainL P C (Ω.profile (a.target hw).type)) :
    plusContinue Ω C hno T hT act q = Value.asPlus (a.free_target hT ht) (act a p hp):=by
  rcases q with ⟨n,v⟩
  dsimp only at hqa hq
  subst n
  subst p
  have hg:Gate Ω C hno T a.argument (plusPayload Ω C hno v) false :=
    ⟨a,rfl,hp,⟨fun h => False.elim (ht h),fun h => Bool.noConfusion h⟩⟩
  simp only [plusContinue,dif_pos hg]
  have H:∀ (k:FrameKey Ω C T),k = a →
      ∀ (hpk:PayFits Ω C hno k.domain (plusPayload Ω C hno v))
        (htk:¬ PlainL P C (Ω.profile (k.target hw).type)),
      Value.asPlus (k.free_target hT htk) (act k (plusPayload Ω C hno v) hpk) =
        Value.asPlus (a.free_target hT ht) (act a (plusPayload Ω C hno v) hp):=by
    intro k hk
    subst k
    intro hpk htk
    rfl
  exact H hg.frame (Gate.unique hg a rfl) hg.payload hg.not_plain
 theorem plusContinue_parameter (T:ActTy Ω C)
    (hT:FreeL P C (Ω.profile T.type) false) (act:LambdaAction (hw:=hw) Ω C hno T)
    (a:FrameKey Ω C T) (p:Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno a.domain p)
    (ht:¬ PlainL P C (Ω.profile (a.target hw).type)) :
    plusContinue Ω C hno T hT act (a.argument,a.plusParam hT p hp) =
      Value.asPlus (a.free_target hT ht) (act a p hp) :=
  plusContinue_gate Ω C hno T hT act a _ rfl p hp (a.plusPayload_parameter hT p hp) ht
theorem minusContinue_gate (T:ActTy Ω C)
    (hT:FreeL P C (Ω.profile T.type) true) (act:LambdaAction (hw:=hw) Ω C hno T)
    (a:FrameKey Ω C T) (q:MinusFrame (hw:=hw) Ω C hno) (hqa:q.1 = a.argument)
    (p:Option (RawValue (hw:=hw) Ω C hno)) (hp:PayFits Ω C hno a.domain p)
    (hq:minusPayload Ω C hno q.2 = p)
    (ht:¬ PlainL P C (Ω.profile (a.target hw).type)) :
    minusContinue Ω C hno T hT act q = Value.asMinus (a.free_target hT ht) (act a p hp):=by
  rcases q with ⟨n,v⟩
  dsimp only at hqa hq
  subst n
  subst p
  have hg:Gate Ω C hno T a.argument (minusPayload Ω C hno v) false :=
    ⟨a,rfl,hp,⟨fun h => False.elim (ht h),fun h => Bool.noConfusion h⟩⟩
  simp only [minusContinue,dif_pos hg]
  have H:∀ (k:FrameKey Ω C T),k = a →
      ∀ (hpk:PayFits Ω C hno k.domain (minusPayload Ω C hno v))
        (htk:¬ PlainL P C (Ω.profile (k.target hw).type)),
      Value.asMinus (k.free_target hT htk) (act k (minusPayload Ω C hno v) hpk) =
        Value.asMinus (a.free_target hT ht) (act a (minusPayload Ω C hno v) hp):=by
    intro k hk
    subst k
    intro hpk htk
    rfl
  exact H hg.frame (Gate.unique hg a rfl) hg.payload hg.not_plain
 theorem minusContinue_parameter (T:ActTy Ω C)
    (hT:FreeL P C (Ω.profile T.type) true) (act:LambdaAction (hw:=hw) Ω C hno T)
    (a:FrameKey Ω C T) (p:Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno a.domain p)
    (ht:¬ PlainL P C (Ω.profile (a.target hw).type)) :
    minusContinue Ω C hno T hT act (a.argument,a.minusParam hT p hp) =
      Value.asMinus (a.free_target hT ht) (act a p hp) :=
  minusContinue_gate Ω C hno T hT act a _ rfl p hp (a.minusPayload_parameter hT p hp) ht
theorem plusLambda_slice (T:ActTy Ω C)
    (hT:FreeL P C (Ω.profile T.type) false) (act:LambdaAction (hw:=hw) Ω C hno T)
    (a:PlusFrame (hw:=hw) Ω C hno) :
    (plusLambda Ω C hno T hT act).slice a = plusContinue Ω C hno T hT act a:=by
  rfl
theorem minusLambda_slice (T:ActTy Ω C)
    (hT:FreeL P C (Ω.profile T.type) true) (act:LambdaAction (hw:=hw) Ω C hno T)
    (a:MinusFrame (hw:=hw) Ω C hno) :
    (minusLambdaBehavior Ω C hno T hT act).slice a =
      FreeObs.behavior _ _ _ _ (minusContinue Ω C hno T hT act a):=by
  rfl
theorem lambda_beta (T:ActTy Ω C) (act:LambdaAction (hw:=hw) Ω C hno T)
    (hr:∀ hT:FreeL P C (Ω.profile T.type) true,
      ∃ x,FreeObs.behavior _ _ _ _ x = minusLambdaBehavior Ω C hno T hT act)
    (a:FrameKey Ω C T) (p:Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno a.domain p) :
    applyValue Ω C hno T (lambdaValue Ω C hno T act) a p hp = act a p hp:=by
  by_cases hT:PlainL P C (Ω.profile T.type)
  · simp only [applyValue,lambdaValue,dif_pos hT]
    exact plain_beta Ω C hno T hT act a p hp
  · by_cases hF:FreeL P C (Ω.profile T.type) false
    · by_cases hA:PlainL P C (Ω.profile (a.target hw).type)
      · simp only [applyValue,lambdaValue,dif_neg hT,dif_pos hF,dif_pos hA,Value.asPlus_plus,plusLambda]
        rw [lambdaExit_parameter Ω C hno _ T act a p hp _ (a.plusPayload_parameter hF p hp) hA]
        exact exitValue_tag Ω C hno _ hA _
      · simp only [applyValue,lambdaValue,dif_neg hT,dif_pos hF,dif_neg hA,Value.asPlus_plus]
        apply Subtype.ext
        change RawValue.plus ((plusLambda Ω C hno T hF act).slice
          (a.argument,a.plusParam hF p hp)) = _
        rw [plusLambda_slice,plusContinue_parameter Ω C hno T hF act a p hp hA]
        exact (Value.asPlus_spec (a.free_target hF hA) (act a p hp)).symm
    · have hM:FreeL P C (Ω.profile T.type) true:=by
        rcases T.active.classify with h | h | h
        · exact False.elim (hT h)
        · exact False.elim (hF h)
        · exact h
      have hb:=packMinus_spec Ω C hno (minusLambdaBehavior Ω C hno T hM act) (hr hM)
      by_cases hA:PlainL P C (Ω.profile (a.target hw).type)
      · simp only [applyValue,lambdaValue,dif_neg hT,dif_neg hF,dif_pos hA,Value.asMinus_minus]
        rw [hb]
        change exitValue Ω C hno (a.target hw)
          (lambdaExit Ω C hno (minusPayload Ω C hno) T act (a.argument,a.minusParam hM p hp)) = _
        rw [lambdaExit_parameter Ω C hno _ T act a p hp _ (a.minusPayload_parameter hM p hp) hA]
        exact exitValue_tag Ω C hno _ hA _
      · simp only [applyValue,lambdaValue,dif_neg hT,dif_neg hF,dif_neg hA,Value.asMinus_minus]
        apply Subtype.ext
        change RawValue.minus (FreeObs.minusSlice
          (packMinus Ω C hno (minusLambdaBehavior Ω C hno T hM act))
          (a.argument,a.minusParam hM p hp)) = _
        rw [Value.asMinus_spec (a.free_target hM hA) (act a p hp)]
        apply congrArg RawValue.minus
        apply FreeObs.behavior_injective (topBase Ω) none
        rw [FreeObs.behavior_minusSlice,hb,minusLambda_slice,
          minusContinue_parameter Ω C hno T hM act a p hp hA]
namespace PreRes
variable {Ω C hno} {Γ:List (Expr S)} {T:Expr S}
theorem abstraction_beta {D m E:Expr S} {s:S} (h:HasType P Γ (.lam D m) T)
    (hp:HasType P Γ (.pi D E) (.sort s)) (hc:Converts T (.pi D E))
    (eb:Evaluator (hw:=hw) Ω C hno (D :: Γ) m E) {B:Nat → Nat}
    (hub:Uniform Ω C hno eb B) (e:ValEnv (hw:=hw) Ω C hno Γ)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (a:FrameKey Ω C (e.activeType h ha)) (p:Option (RawValue (hw:=hw) Ω C hno))
    (hpp:PayFits Ω C hno a.domain p) :
    applyValue Ω C hno (e.activeType h ha) ((abstraction h hp hc eb e).val ha) a p hpp =
      abstractionAction h hp hc eb e ha a p hpp:=by
  apply lambda_beta
  intro hT
  obtain ⟨k,hk⟩:=e.exists_bound
  obtain ⟨v,_,hv⟩:=minusLambda_representable Ω C hno hT (by have:=hub.growth k; omega)
    (abstractionAction_bounded h hp hc eb hub k e hk ha)
    (fun a p p' hp' hp'' hbp hbp' hpp =>
      abstractionAction_level h hp hc eb hub k e e hk hk (e.level_refl _) ha ha a a rfl
        p p' hp' hp'' hbp hbp' hpp)
  exact ⟨v,hv⟩
theorem application_frame {f n A B:Expr S} (h:HasType P Γ (.app f n) T)
    (hf:HasType P Γ f (.pi A B)) (hn:HasType P Γ n A) (hc:Converts T (B.instantiate n))
    (ef:Evaluator (hw:=hw) Ω C hno Γ f (.pi A B))
    (en:Evaluator (hw:=hw) Ω C hno Γ n A)
    (e:ValEnv (hw:=hw) Ω C hno Γ)
    (hF:ActL P C (Ω.profile ((Expr.pi A B).subst e.images).nfTerm))
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)) :
    ∃ (k:FrameKey Ω C (e.activeType hf hF))
      (hp:PayFits Ω C hno k.domain (en e).parameter),
      k.argument = (n.subst e.images).nfTerm ∧ k.domain = (A.subst e.images).nfTerm ∧
      ((application h hf hn hc ef en e).val ha).val =
        (applyValue Ω C hno _ ((ef e).val hF) k (en e).parameter hp).val:=by
  unfold application baseResult applicationValue
  simp only [dif_pos hF]
  exact ⟨_,(en e).parameter_fits,rfl,rfl,rfl⟩
theorem abstractionAction_raw {D m E:Expr S} {s:S}
    (h:HasType P Γ (.lam D m) T) (hp:HasType P Γ (.pi D E) (.sort s))
    (hc:Converts T (.pi D E)) (b:TyTree P (D :: Γ) m E)
    (hC:IsComp (PriEdge P) C)
    (e:ValEnv (hw:=hw) Ω C hno Γ)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm))
    (k:FrameKey Ω C (e.activeType h ha))
    (p:Option (RawValue (hw:=hw) Ω C hno)) (hpp:PayFits Ω C hno k.domain p)
    (n:Expr S) (hn:Ω.HasType n (D.subst e.images))
    (hp':PayFits Ω C hno (D.subst e.images).nfTerm p)
    (hkn:Converts k.argument n)
    (ha':ActL P C (Ω.profile (E.subst (Expr.consSub n e.images)).nfTerm)) :
    (abstractionAction h hp hc (preEval Ω C hno b) e ha k p hpp).val =
      ((preEval Ω C hno b (e.cons hn p hp')).val ha').val:=by
  unfold abstractionAction
  apply val_congr
  apply (preEval_compatible Ω C hno hC b _ _ ?_).1
  constructor
  · intro i hi
    cases i with
    | zero => exact hkn
    | succ i => exact .refl _
  · intro i hi
    cases i <;> rfl
end PreRes
 theorem application_abstraction_beta {Γ:List (Expr S)} {D m E A B n T:Expr S} {a s:S}
    (ht:HasType P Γ (.app (.lam D m) n) T)
    (hf:HasType P Γ (.lam D m) (.pi A B))
    (d:TyTree P Γ D (.sort a)) (b:TyTree P (D :: Γ) m E)
    (hp:HasType P Γ (.pi D E) (.sort s)) (hcF:Converts (.pi A B) (.pi D E))
    (nt:TyTree P Γ n A) (hc:Converts T (B.instantiate n))
    (hC:IsComp (PriEdge P) C) (e:ValEnv (hw:=hw) Ω C hno Γ)
    (hF:ActL P C (Ω.profile ((Expr.pi A B).subst e.images).nfTerm))
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)) :
    ∃ (hnD:Ω.HasType (n.subst e.images) (D.subst e.images))
      (hpp:PayFits Ω C hno (D.subst e.images).nfTerm (preEval Ω C hno nt e).parameter)
      (hb:ActL P C (Ω.profile (E.subst (Expr.consSub (n.subst e.images) e.images)).nfTerm)),
      (Ω.profile (D.subst e.images) ∈ ObsLayers P C → ActL P C (Ω.profile (D.subst e.images))) ∧
      ((preEval Ω C hno (.application ht (.abstraction hf d b hp hcF) nt hc) e).val ha).val =
        ((preEval Ω C hno b (e.cons hnD (preEval Ω C hno nt e).parameter hpp)).val hb).val:=by
  obtain ⟨k,hpk,hkn,hkD,hval⟩:=PreRes.application_frame ht hf nt.typing hc
    (preEval Ω C hno (.abstraction hf d b hp hcF)) (preEval Ω C hno nt) e hF ha
  have hnD:HasType P Γ n D:=.conversion nt.typing d.typing hcF.product_compatibility.1
  have hAD:=e.type_convert_eq nt.typing hnD hcF.product_compatibility.1
  have hpp:PayFits Ω C hno (D.subst e.images).nfTerm (preEval Ω C hno nt e).parameter :=
    hAD ▸ (preEval Ω C hno nt e).parameter_fits
  have hbT:Converts T (E.instantiate n):=.trans _ _ _ hc (hcF.product_compatibility.2.subst (Expr.single n))
  have heT:=e.type_convert_eq ht (b.typing.instantiate hnD) hbT
  have heT':(T.subst e.images).nfTerm =
      (E.subst (Expr.consSub (n.subst e.images) e.images)).nfTerm:=by
    simpa only [Expr.instantiate,Expr.subst_compSub,Expr.comp_single] using heT
  have hb:ActL P C (Ω.profile (E.subst (Expr.consSub (n.subst e.images) e.images)).nfTerm):=heT' ▸ ha
  refine ⟨CTower.HasType.subst hnD e.typed,hpp,hb,?_,?_⟩
  · intro hH
    have heD:Ω.profile k.domain = Ω.profile (D.subst e.images):=by rw [hkD,hAD,Ω.profile_nfTerm]
    rw [← heD]
    exact k.domain_active hw (heD.symm ▸ hH)
  · obtain ⟨F,hB⟩:=preEval_uniform Ω C hno hC b
    refine hval.trans ?_
    rw [show ((preEval Ω C hno (.abstraction hf d b hp hcF) e).val hF) =
      (PreRes.abstraction hf hp hcF (preEval Ω C hno b) e).val hF from rfl,
      PreRes.abstraction_beta hf hp hcF _ hB e hF k _ hpk]
    apply PreRes.abstractionAction_raw hf hp hcF b hC e hF k _ hpk
      (n.subst e.images) (CTower.HasType.subst hnD e.typed) hpp _ hb
    rw [hkn]
    exact .symm _ _ (Expr.nfTerm_spec ((CTower.HasType.subst nt.typing e.typed).weakNorm hw)).1.converts
structure GoodTransport {Γ:List (Expr S)} {M N T:Expr S}
    (t:TyTree P Γ M T) (t':TyTree P Γ N T):Prop where
  val:∀ (e:ValEnv (hw:=hw) Ω C hno Γ)
    (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)),
    ValGood Ω C t e.images → ValGood Ω C t' e.images ∧
      ((preEval Ω C hno t e).val ha).val = ((preEval Ω C hno t' e).val ha).val
  read:∀ (e:ValEnv (hw:=hw) Ω C hno Γ),ReadGood Ω C t e.images →
    ReadGood Ω C t' e.images ∧ (preEval Ω C hno t e).read.val = (preEval Ω C hno t' e).read.val
 theorem baseRead_transport {Γ:List (Expr S)} {M N T:Expr S}
    (ht:HasType P Γ M T) (t':TyTree P Γ N T)
    (e:ValEnv (hw:=hw) Ω C hno Γ)
    (hMN:(M.subst e.images).nfTerm = (N.subst e.images).nfTerm)
    (hne:Neutral M → Neutral N)
    (v:ActL P C (Ω.profile (T.subst e.images).nfTerm) →
      Value (hw:=hw) Ω C hno (T.subst e.images).nfTerm) (G:Prop)
    (hr:baseGood Ω C M T e.images G)
    (hv:∀ ha,G → ValGood Ω C t' e.images ∧ (v ha).val = ((preEval Ω C hno t' e).val ha).val) :
    ReadGood Ω C t' e.images ∧ (PreRes.baseRead ht v).val = (preEval Ω C hno t' e).read.val:=by
  by_cases hm:Ω.profile (M.subst e.images).nfTerm ∈ C
  · have hm':Ω.profile (N.subst e.images).nfTerm ∈ C:=hMN ▸ hm
    obtain ⟨s,hs,hsC,hval,hn⟩:=hr (by simpa only [Ω.profile_nfTerm] using hm)
    subst T
    by_cases ha:ActL P C (Ω.profile (Expr.sort s |>.subst e.images).nfTerm)
    · have hvg:=hv ha (hval (by simpa only [Ω.profile_nfTerm] using ha))
      refine ⟨(readGood_active_iff Ω C t' (by simpa only [Ω.profile_nfTerm] using hm') hsC
        (by simpa only [Ω.profile_nfTerm] using ha)).mpr hvg.1,?_⟩
      refine Eq.trans (PreRes.baseRead_eq ht v hm hsC ha)
        (Eq.trans ?_ (preEval_read_base Ω C hno t' e hm' hsC ha).symm)
      rw [hvg.2]
      exact congrArg (fun X:ActualType Ω =>
        ((RawValue.base Ω C hno ((preEval Ω C hno t' e).val ha).val) X).val) (Subtype.ext hMN)
    · have hn':=hne (hn (by simpa only [Ω.profile_nfTerm] using ha))
      refine ⟨neutral_readGood Ω C t' hn' e.images hsC (by simpa only [Expr.subst,Ω.profile_sort,Ω.profile_nfTerm] using ha),?_⟩
      have hex:∃ s',Expr.sort s = Expr.sort s' ∧ ({s'}:Set S) ∈ C:=⟨s,rfl,hsC⟩
      rw [preEvaluate_neutral_read_inactive Ω C hno t' e hn' ha]
      simp only [PreRes.baseRead,dif_pos hm,dif_pos hex,dif_neg ha]
      exact congrArg (Cands.Top Ω) hMN
  · have hm':Ω.profile (N.subst e.images).nfTerm ∉ C:=hMN ▸ hm
    refine ⟨readGood_outside Ω C t' e.images (by simpa only [Ω.profile_nfTerm] using hm'),?_⟩
    rw [preEvaluate_read_outside Ω C hno t' e hm']
    simp only [PreRes.baseRead,dif_neg hm]
    exact congrArg (Cands.Top Ω) hMN
 theorem root_transport {Γ:List (Expr S)} {D m E A B n T:Expr S} {a s:S}
    (ht:HasType P Γ (.app (.lam D m) n) T)
    (hf:HasType P Γ (.lam D m) (.pi A B))
    (d:TyTree P Γ D (.sort a)) (b:TyTree P (D :: Γ) m E)
    (hp:HasType P Γ (.pi D E) (.sort s)) (hcF:Converts (.pi A B) (.pi D E))
    (nt:TyTree P Γ n A) (hc:Converts T (B.instantiate n))
    (hC:IsComp (PriEdge P) C) :
    ∃ t':TyTree P Γ (m.instantiate n) T,
      GoodTransport (hw:=hw) Ω C hno (.application ht (.abstraction hf d b hp hcF) nt hc) t':=by
  have hnD:HasType P Γ n D:=.conversion nt.typing d.typing hcF.product_compatibility.1
  let ntD:=nt.retarget hnD (.symm _ _ hcF.product_compatibility.1)
  let ts:=TyTree.StoredSubstitution.single ntD
  let bt:=b.subst ht.valid (Expr.single n) ts
  have ht':=ht.subject_reduction (.head D m n)
  have hc':Converts T (E.instantiate n):=.trans _ _ _ hc (hcF.product_compatibility.2.subst (Expr.single n))
  let t':=bt.retarget ht' hc'
  refine ⟨t',?_⟩
  have hval:∀ (e:ValEnv (hw:=hw) Ω C hno Γ)
      (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)),
      ValGood Ω C (.application ht (.abstraction hf d b hp hcF) nt hc) e.images →
      ValGood Ω C t' e.images ∧
      ((preEval Ω C hno (.application ht (.abstraction hf d b hp hcF) nt hc) e).val ha).val =
        ((preEval Ω C hno t' e).val ha).val:=by
    intro e ha hg
    have hF:ActL P C (Ω.profile ((Expr.pi A B).subst e.images)):=by
      by_contra hh
      change (if ActL P C (Ω.profile ((Expr.pi A B).subst e.images)) then _ else _) at hg
      rw [if_neg hh] at hg
      cases hg with | app hf => cases hf
    change (if ActL P C (Ω.profile ((Expr.pi A B).subst e.images)) then _ else _) at hg
    rw [if_pos hF] at hg
    obtain ⟨hraw,hpp,hbody,hguard,hbeta⟩:=application_abstraction_beta Ω C hno ht hf d b hp hcF nt hc hC e
      (by simpa only [Ω.profile_nfTerm] using hF) ha
    let er:=e.cons (CTower.HasType.subst hnD e.typed) (preEval Ω C hno ntD e).parameter
      (preEval Ω C hno ntD e).parameter_fits
    have herimages:er.images = Expr.consSub (n.subst e.images) e.images:=by
      funext i; cases i <;> rfl
    have hpEq:(preEval Ω C hno nt e).parameter = (preEval Ω C hno ntD e).parameter :=
      preEvaluate_retarget_parameter Ω C hno nt hnD (.symm _ _ hcF.product_compatibility.1) e
    have heren:(e.cons hraw (preEval Ω C hno nt e).parameter hpp).Compatible er:=by
      constructor
      · intro i hi; exact .refl _
      · intro i hi; cases i with
        | zero => exact hpEq
        | succ i => rfl
    have hgoodB:ValGood Ω C b er.images:=hg.1 (n.subst e.images) hraw
      (by simpa only [Ω.profile_nfTerm] using hbody)
    have heT:=e.type_convert_eq ht bt.typing hc'
    have haBt:ActL P C (Ω.profile ((E.instantiate n).subst e.images).nfTerm):=heT ▸ ha
    have hsGuard:SubstitutionGuard Ω C (D :: Γ) (Expr.single n) er.images:=single_guard Ω C e.images hguard
    have hgoodN:GoodReplacement Ω C ts e.images:=single_goodReplacement Ω C ntD e.images (by
      intro hD
      apply (valGood_retarget Ω C nt hnD (.symm _ _ hcF.product_compatibility.1) e.images).mpr
      apply hg.2
      have heD:=e.type_convert_eq nt.typing hnD hcF.product_compatibility.1
      rw [← Ω.profile_nfTerm,heD,Ω.profile_nfTerm]
      exact hD)
    have hgoodBt:ValGood Ω C bt e.images:=(goodness_subst Ω C hw b ht.valid (Expr.single n) ts e.images e.typed
      (by simpa only [Expr.comp_single,←herimages] using hsGuard) hgoodN).1
      (by simpa only [Expr.comp_single,Ω.profile_nfTerm] using hbody)
      (by simpa only [Expr.comp_single,←herimages] using hgoodB)
    refine ⟨(valGood_retarget Ω C bt ht' hc' e.images).mpr hgoodBt,?_⟩
    refine hbeta.trans (Eq.trans ?_ (preEvaluate_retarget_val Ω C hno bt ht' hc' e haBt ha))
    refine Eq.trans (PreRes.val_congr _ _ (preEval_compatible Ω C hno hC b _ _ heren).1 hbody hbody) ?_
    exact (preEvaluate_subst Ω C hno b ht.valid (Expr.single n) ts er e (single_assigned Ω C hno ntD e) hsGuard).1
      hbody haBt hgoodB
  refine ⟨hval,?_⟩
  intro e hr
  apply baseRead_transport Ω C hno ht t' e
    (e.expression_convert_eq ht ht' (.rel _ _ (.head D m n)))
    (fun h => by cases h with | app hf => cases hf) _ _ hr
  exact hval e
namespace ValEnv
variable {Ω C hno} {Γ:List (Expr S)}
@[simp] theorem cons_images (e:ValEnv (hw:=hw) Ω C hno Γ) {D n:Expr S}
    (hn:Ω.HasType n (D.subst e.images)) p hp :
    (e.cons hn p hp).images = Expr.consSub n e.images:=by
  funext i; cases i <;> rfl
end ValEnv
namespace GoodTransport
variable {Ω C hno} {Γ:List (Expr S)} {M N T:Expr S}
 theorem refl (t:TyTree P Γ M T):GoodTransport (hw:=hw) Ω C hno t t :=
  ⟨fun _ _ h => ⟨h,rfl⟩,fun _ h => ⟨h,rfl⟩⟩
 theorem parameter_eq {t:TyTree P Γ M T} {t':TyTree P Γ N T}
    (h:GoodTransport (hw:=hw) Ω C hno t t') (e:ValEnv (hw:=hw) Ω C hno Γ)
    (hg:ActL P C (Ω.profile (T.subst e.images).nfTerm) → ValGood Ω C t e.images) :
    (preEval Ω C hno t e).parameter = (preEval Ω C hno t' e).parameter:=by
  apply PreRes.parameter_congr _ _ rfl
  intro ha ha'
  exact (h.val e ha (hg ha)).2
end GoodTransport
 theorem application_transport {Γ:List (Expr S)} {f n f' n' D E T:Expr S}
    (ht:HasType P Γ (.app f n) T) (ht':HasType P Γ (.app f' n') T)
    (ft:TyTree P Γ f (.pi D E)) (ft':TyTree P Γ f' (.pi D E))
    (nt:TyTree P Γ n D) (nt':TyTree P Γ n' D)
    (hc:Converts T (E.instantiate n)) (hc':Converts T (E.instantiate n'))
    (hf:GoodTransport (hw:=hw) Ω C hno ft ft') (hn:GoodTransport (hw:=hw) Ω C hno nt nt')
    (hff:Converts f f') (hnn:Converts n n') (hne:Neutral f → Neutral f') :
    GoodTransport (hw:=hw) Ω C hno (.application ht ft nt hc) (.application ht' ft' nt' hc'):=by
  have hval:∀ (e:ValEnv (hw:=hw) Ω C hno Γ)
      (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)),
      ValGood Ω C (.application ht ft nt hc) e.images →
      ValGood Ω C (.application ht' ft' nt' hc') e.images ∧
      ((preEval Ω C hno (.application ht ft nt hc) e).val ha).val =
      ((preEval Ω C hno (.application ht' ft' nt' hc') e).val ha).val:=by
    intro e ha hg
    change (if ActL P C (Ω.profile ((Expr.pi D E).subst e.images)) then _ else _) at hg
    change (if ActL P C (Ω.profile ((Expr.pi D E).subst e.images)) then _ else _) ∧ _
    by_cases hF:ActL P C (Ω.profile ((Expr.pi D E).subst e.images))
    · rw [if_pos hF] at hg ⊢
      have hFa:ActL P C (Ω.profile ((Expr.pi D E).subst e.images).nfTerm):=by
        simpa only [Ω.profile_nfTerm] using hF
      refine ⟨⟨(hf.val e hFa hg.1).1,fun haD => (hn.val e
        (by simpa only [Ω.profile_nfTerm] using haD) (hg.2 haD)).1⟩,?_⟩
      apply PreRes.application_val_congr ht ht' ft.typing ft'.typing nt.typing nt'.typing hc hc'
        _ _ _ _ e e rfl rfl (e.expression_convert_eq nt.typing nt'.typing hnn)
      · exact fun _ _ => (hf.val e hFa hg.1).2
      · exact hn.parameter_eq e (fun haD => hg.2 (by simpa only [Ω.profile_nfTerm] using haD))
    · rw [if_neg hF] at hg ⊢
      refine ⟨?_,?_⟩
      · cases hg with | app hg => exact .app (hne hg)
      · have hFa:¬ ActL P C (Ω.profile ((Expr.pi D E).subst e.images).nfTerm):=by
          simpa only [Ω.profile_nfTerm] using hF
        simp only [preEval,PreRes.application,PreRes.baseResult,PreRes.applicationValue,dif_neg hFa]
  refine ⟨hval,?_⟩
  intro e hr
  apply baseRead_transport Ω C hno ht (.application ht' ft' nt' hc') e
    (e.expression_convert_eq ht ht' (.app hff hnn))
    (fun hh => by cases hh with | app hh => exact .app (hne hh)) _ _ hr
  exact hval e
 theorem abstraction_transport {Γ:List (Expr S)} {D m E D' m' E' T:Expr S} {a a' s s':S}
    (ht:HasType P Γ (.lam D m) T) (ht':HasType P Γ (.lam D' m') T)
    (d:TyTree P Γ D (.sort a)) (d':TyTree P Γ D' (.sort a'))
    (b:TyTree P (D :: Γ) m E) (b':TyTree P (D' :: Γ) m' E')
    (hp:HasType P Γ (.pi D E) (.sort s)) (hp':HasType P Γ (.pi D' E') (.sort s'))
    (hc:Converts T (.pi D E)) (hc':Converts T (.pi D' E'))
    (hD:Converts D D') (hm:Converts m m') (hE:Converts E E')
    (hb:∀ (e:ValEnv (hw:=hw) Ω C hno Γ) n
      (hn:Ω.HasType n (D.subst e.images)) (hn':Ω.HasType n (D'.subst e.images))
      p hpp hpp' ha ha',ValGood Ω C b (e.cons hn p hpp).images →
        ValGood Ω C b' (e.cons hn' p hpp').images ∧
        ((preEval Ω C hno b (e.cons hn p hpp)).val ha).val =
        ((preEval Ω C hno b' (e.cons hn' p hpp')).val ha').val) :
    GoodTransport (hw:=hw) Ω C hno (.abstraction ht d b hp hc) (.abstraction ht' d' b' hp' hc'):=by
  have hval:∀ (e:ValEnv (hw:=hw) Ω C hno Γ)
      (ha:ActL P C (Ω.profile (T.subst e.images).nfTerm)),
      ValGood Ω C (.abstraction ht d b hp hc) e.images →
      ValGood Ω C (.abstraction ht' d' b' hp' hc') e.images ∧
      ((preEval Ω C hno (.abstraction ht d b hp hc) e).val ha).val =
      ((preEval Ω C hno (.abstraction ht' d' b' hp' hc') e).val ha).val:=by
    intro e ha hg
    have hnold {n:Expr S} (hn:Ω.HasType n (D'.subst e.images)):Ω.HasType n (D.subst e.images) :=
      .conversion hn (CTower.HasType.subst d.typing e.typed) (.symm _ _ (hD.subst e.images))
    have hEeq (n:Expr S) (hn:Ω.HasType n (D'.subst e.images)) :
        (E.subst (Expr.consSub n e.images)).nfTerm = (E'.subst (Expr.consSub n e.images)).nfTerm :=
      Expr.nfTerm_converts ((CTower.HasType.subst b.typing (e.typed.cons (hnold hn))).type_weakNorm hw)
        ((CTower.HasType.subst b'.typing (e.typed.cons hn)).type_weakNorm hw)
        (hE.subst (Expr.consSub n e.images))
    refine ⟨?_,?_⟩
    · intro n hn ha'
      have haold:ActL P C (Ω.profile (E.subst (Expr.consSub n e.images)).nfTerm):=by
        rw [hEeq n hn,Ω.profile_nfTerm]; exact ha'
      obtain ⟨pa,hpD⟩:=PayFits.exists_of_actual (hw:=hw) (C:=C) (hno:=hno) (e.actualExpression d.typing)
      have hDD:=e.expression_convert_eq d.typing d'.typing hD
      have hpD':PayFits Ω C hno (D'.subst e.images).nfTerm pa:=hDD ▸ hpD
      exact (hb e n (hnold hn) hn pa hpD hpD' haold
        (by simpa only [Ω.profile_nfTerm,ValEnv.cons_images] using ha') (hg n (hnold hn)
          (by simpa only [Ω.profile_nfTerm] using haold))).1
    · apply PreRes.abstraction_val_congr ht ht' hp hp' hc hc' _ _ e e rfl
      intro n n' hn hn' he p hpp hpp' haB haB'
      subst n'
      exact (hb e n hn hn' p hpp hpp' haB haB' (hg n hn
        (by simpa only [Ω.profile_nfTerm,ValEnv.cons_images] using haB))).2
  refine ⟨hval,?_⟩
  intro e hr
  apply baseRead_transport Ω C hno ht (.abstraction ht' d' b' hp' hc') e
    (e.expression_convert_eq ht ht' (.lam hD hm)) (fun hn => by cases hn) _ _ hr
  exact hval e
 theorem product_transport {Γ:List (Expr S)} {D E D' E' T:Expr S} {a q c:S}
    (ht:HasType P Γ (.pi D E) T) (ht':HasType P Γ (.pi D' E') T)
    (d:TyTree P Γ D (.sort a)) (d':TyTree P Γ D' (.sort a))
    (b:TyTree P (D :: Γ) E (.sort q)) (b':TyTree P (D' :: Γ) E' (.sort q))
    (hr:P.rule a q c) (hc:Converts T (.sort c))
    (hD:Converts D D') (hE:Converts E E')
    (hd:∀ (e:ValEnv (hw:=hw) Ω C hno Γ),ReadGood Ω C d e.images →
      ReadGood Ω C d' e.images ∧ (preEval Ω C hno d e).read.val = (preEval Ω C hno d' e).read.val)
    (hb:∀ (e:ValEnv (hw:=hw) Ω C hno Γ) n
      (hn:Ω.HasType n (D.subst e.images)) (hn':Ω.HasType n (D'.subst e.images))
      p hpp hpp',ReadGood Ω C b (e.cons hn p hpp).images →
        ReadGood Ω C b' (e.cons hn' p hpp').images ∧
        (preEval Ω C hno b (e.cons hn p hpp)).read.val =
        (preEval Ω C hno b' (e.cons hn' p hpp')).read.val) :
    GoodTransport (hw:=hw) Ω C hno (.product ht d b hr hc) (.product ht' d' b' hr hc):=by
  have hdata (e:ValEnv (hw:=hw) Ω C hno Γ) :
      (D.subst e.images).nfTerm = (D'.subst e.images).nfTerm ∧
      (E.subst (Expr.liftSub e.images)).nfTerm = (E'.subst (Expr.liftSub e.images)).nfTerm:=by
    have hpi:=e.expression_convert_eq ht ht' (.pi hD hE)
    have hwp:=(CTower.HasType.subst ht e.typed).weakNorm hw
    have hwp':=(CTower.HasType.subst ht' e.typed).weakNorm hw
    rw [Expr.subst,Expr.subst,Expr.nfTerm_pi hwp.pi_domain hwp.pi_body,
      Expr.nfTerm_pi hwp'.pi_domain hwp'.pi_body] at hpi
    exact Expr.pi.inj hpi
  have hchildren (e:ValEnv (hw:=hw) Ω C hno Γ)
      (hg:ProductGood Ω C d b e.images) :
      ProductGood Ω C d' b' e.images ∧
      (PreRes.productCandidate d.typing b.typing hr (preEval Ω C hno d) (preEval Ω C hno b) e).val =
      (PreRes.productCandidate d'.typing b'.typing hr (preEval Ω C hno d') (preEval Ω C hno b') e).val:=by
    have hnold {n:Expr S} (hn:Ω.HasType n (D'.subst e.images)):Ω.HasType n (D.subst e.images) :=
      .conversion hn (CTower.HasType.subst d.typing e.typed) (.symm _ _ (hD.subst e.images))
    have hEeq (n:Expr S) (hn:Ω.HasType n (D'.subst e.images)) :
        (E.subst (Expr.consSub n e.images)).nfTerm = (E'.subst (Expr.consSub n e.images)).nfTerm :=
      Expr.nfTerm_converts ((CTower.HasType.subst b.typing (e.typed.cons (hnold hn))).weakNorm hw)
        ((CTower.HasType.subst b'.typing (e.typed.cons hn)).weakNorm hw)
        (hE.subst (Expr.consSub n e.images))
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro hD'
      apply (hd e (hg.1 ?_)).1
      rw [← Ω.profile_nfTerm,(hdata e).1,Ω.profile_nfTerm]
      exact hD'
    · intro n hn hE'
      have hEold:Ω.profile (E.subst (Expr.consSub n e.images)) ∈ C:=by
        rw [← Ω.profile_nfTerm,hEeq n hn,Ω.profile_nfTerm]; exact hE'
      obtain ⟨p,hp⟩:=PayFits.exists_of_actual (hw:=hw) (C:=C) (hno:=hno) (e.actualExpression d.typing)
      have hp':PayFits Ω C hno (D'.subst e.images).nfTerm p:=(hdata e).1 ▸ hp
      have hh:=(hb e n (hnold hn) hn p hp hp' (by
        simpa only [ValEnv.cons_images] using hg.2 n (hnold hn) hEold)).1
      simpa only [ValEnv.cons_images] using hh
    · apply PreRes.productCandidate_congr d.typing b.typing hr d'.typing b'.typing hr _ _ _ _ e e
        (hdata e).1 (hdata e).2
      · intro hD
        exact (hd e (hg.1 (by simpa only [Ω.profile_nfTerm] using hD))).2
      · intro n hn hn' p hp hp' hE
        exact (hb e n hn hn' p hp hp' (hg.2 n hn
          (by simpa only [Ω.profile_nfTerm,ValEnv.cons_images] using hE))).2
  constructor
  · intro e ha hg
    have hM:=e.expression_convert_eq ht ht' (.pi hD hE)
    refine ⟨?_,?_⟩
    · intro hgate
      exact (hchildren e (hg ⟨hgate.1,by
        rw [← Ω.profile_nfTerm,hM,Ω.profile_nfTerm]; exact hgate.2⟩)).1
    · by_cases hs:({c}:Set S) ∈ C
      · apply PreRes.product_val_congr ht ht' d.typing b.typing hr d'.typing b'.typing hr hc hc
          _ _ _ _ e e rfl hM Iff.rfl
        intro hm
        exact (hchildren e (hg ⟨hs,by simpa only [Ω.profile_nfTerm] using hm⟩)).2
      · have hgate:¬ (({c}:Set S) ∈ C ∧ Ω.profile ((Expr.pi D E).subst e.images).nfTerm ∈ C) :=
          fun h => hs h.1
        have hgate':¬ (({c}:Set S) ∈ C ∧ Ω.profile ((Expr.pi D' E').subst e.images).nfTerm ∈ C) :=
          fun h => hs h.1
        simp only [preEval,PreRes.product,dif_neg hgate,dif_neg hgate']
  · intro e hg
    have hM:=e.expression_convert_eq ht ht' (.pi hD hE)
    refine ⟨?_,?_⟩
    · intro hm
      exact (hchildren e (hg (by rw [← Ω.profile_nfTerm,hM,Ω.profile_nfTerm]; exact hm))).1
    · apply PreRes.product_read_congr ht ht' d.typing b.typing hr d'.typing b'.typing hr hc hc
        _ _ _ _ e e hM
      intro hm
      exact (hchildren e (hg (by simpa only [Ω.profile_nfTerm] using hm))).2
 theorem reduction_transport (hC:IsComp (PriEdge P) C)
    {Γ:List (Expr S)} {M N T:Expr S} (t:TyTree P Γ M T) (hr:Beta M N) :
    ∃ t':TyTree P Γ N T,GoodTransport (hw:=hw) Ω C hno t t':=by
  induction hr generalizing Γ T with
  | head D m n =>
      cases t with
      | application ht ft nt hc =>
          cases ft with
          | abstraction hf d b hp hcF =>
              exact root_transport Ω C hno ht hf d b hp hcF nt hc hC
  | app_left hr ih =>
      cases t with
      | application ht ft nt hc =>
          obtain ⟨ft',hft⟩:=ih ft
          have ht':=ht.subject_reduction (.app_left hr)
          exact ⟨.application ht' ft' nt hc,application_transport Ω C hno ht ht' ft ft' nt nt hc hc
            hft (.refl nt) (.rel _ _ hr) (.refl _) (fun hn => hn.beta hr)⟩
  | app_right hr ih =>
      cases t with
      | @application Γ f n D E T ht ft nt hc =>
          obtain ⟨nt',hnt⟩:=ih nt
          have ht':=ht.subject_reduction (.app_right hr)
          have hc':Converts T (E.instantiate _):=.trans _ _ _ hc ((show Converts _ _ from .rel _ _ hr).instantiate_right E)
          exact ⟨.application ht' ft nt' hc',application_transport Ω C hno ht ht' ft ft nt nt' hc hc'
            (.refl ft) hnt (.refl _) (.rel _ _ hr) (fun hn => hn)⟩
  | @lam_domain D D' m hr ih =>
      cases t with
      | @abstraction Γ _ _ E a s T ht d b hp hc =>
          obtain ⟨d',_⟩:=ih d
          let hctx:=ContextEquivalent.head_conversion d.typing d'.typing (.rel _ _ hr)
          let b':=b.recontext hctx
          have ht':=ht.subject_reduction (.lam_domain hr)
          have hp':=hp.subject_reduction (.pi_domain hr)
          have hc':Converts T (.pi D' E):=.trans _ _ _ hc (.rel _ _ (.pi_domain hr))
          refine ⟨.abstraction ht' d' b' hp' hc',abstraction_transport Ω C hno ht ht' d d' b b' hp hp'
            hc hc' (.rel _ _ hr) (.refl _) (.refl _) ?_⟩
          intro e n hn hn' p hpp hpp' ha ha' hg
          refine ⟨?_,?_⟩
          · change (goodness Ω C (b.recontext hctx) (e.cons hn' p hpp').images).1
            rw [goodness_recontext]
            simpa only [ValEnv.cons_images] using hg
          · apply PreRes.val_congr
            exact (preEval_recontext Ω C hno b hctx (e.cons hn p hpp) (e.cons hn' p hpp') ⟨rfl,rfl⟩).1
  | lam_body hr ih =>
      cases t with
      | abstraction ht d b hp hc =>
          obtain ⟨b',hb⟩:=ih b
          have ht':=ht.subject_reduction (.lam_body hr)
          refine ⟨.abstraction ht' d b' hp hc,abstraction_transport Ω C hno ht ht' d d b b' hp hp
            hc hc (.refl _) (.rel _ _ hr) (.refl _) ?_⟩
          intro e n hn hn' p hpp hpp' ha ha' hg
          exact hb.val (e.cons hn p hpp) ha hg
  | @pi_domain D D' E hr ih =>
      cases t with
      | @product Γ _ _ a b c T ht d bt hrule hc =>
          obtain ⟨d',hd⟩:=ih d
          let hctx:=ContextEquivalent.head_conversion d.typing d'.typing (.rel _ _ hr)
          let b':=bt.recontext hctx
          have ht':=ht.subject_reduction (.pi_domain hr)
          refine ⟨.product ht' d' b' hrule hc,product_transport Ω C hno ht ht' d d' bt b' hrule hc
            (.rel _ _ hr) (.refl _) hd.read ?_⟩
          intro e n hn hn' p hpp hpp' hg
          refine ⟨?_,?_⟩
          · change (goodness Ω C (bt.recontext hctx) (e.cons hn' p hpp').images).2
            rw [goodness_recontext]
            simpa only [ValEnv.cons_images] using hg
          · exact (preEval_recontext Ω C hno bt hctx (e.cons hn p hpp) (e.cons hn' p hpp') ⟨rfl,rfl⟩).2
  | pi_body hr ih =>
      cases t with
      | product ht d bt hrule hc =>
          obtain ⟨b',hb⟩:=ih bt
          have ht':=ht.subject_reduction (.pi_body hr)
          refine ⟨.product ht' d b' hrule hc,product_transport Ω C hno ht ht' d d bt b' hrule hc
            (.refl _) (.rel _ _ hr) (fun e hg => ⟨hg,rfl⟩) ?_⟩
          intro e n hn hn' p hpp hpp' hg
          exact hb.read (e.cons hn p hpp) hg
namespace GoodTransport
variable {Ω C hno} {Γ:List (Expr S)} {M N L T:Expr S}
 theorem trans {t:TyTree P Γ M T} {t':TyTree P Γ N T} {t'':TyTree P Γ L T}
    (h:GoodTransport (hw:=hw) Ω C hno t t') (h':GoodTransport (hw:=hw) Ω C hno t' t'') :
    GoodTransport (hw:=hw) Ω C hno t t'':=by
  constructor
  · intro e ha hg
    have hh:=h.val e ha hg
    have hh':=h'.val e ha hh.1
    exact ⟨hh'.1,hh.2.trans hh'.2⟩
  · intro e hg
    have hh:=h.read e hg
    have hh':=h'.read e hh.1
    exact ⟨hh'.1,hh.2.trans hh'.2⟩
end GoodTransport
 theorem reduces_transport (hC:IsComp (PriEdge P) C)
    {Γ:List (Expr S)} {M N T:Expr S} (t:TyTree P Γ M T) (hr:Reduces M N) :
    ∃ t':TyTree P Γ N T,GoodTransport (hw:=hw) Ω C hno t t':=by
  induction hr with
  | refl => exact ⟨t,.refl t⟩
  | tail _ h ih =>
      obtain ⟨t',ht⟩:=ih
      obtain ⟨t'',ht'⟩:=reduction_transport Ω C hno hC t' h
      exact ⟨t'',ht.trans ht'⟩
theorem normalize_transport (hC:IsComp (PriEdge P) C)
    {Γ:List (Expr S)} {M T:Expr S} (t:TyTree P Γ M T) :
    ∃ t':TyTree P Γ M.nfTerm T,GoodTransport (hw:=hw) Ω C hno t t' :=
  reduces_transport Ω C hno hC t (Expr.nfTerm_spec (t.typing.weakNorm hw)).1
theorem good_normal_read (hC:IsComp (PriEdge P) C)
    {Γ:List (Expr S)} {M:Expr S} {s r:S} (t:TyTree P Γ M (.sort s))
    (t':TyTree P Γ M.nfTerm (.sort r))
    (e:ValEnv (hw:=hw) Ω C hno Γ) (hg:ReadGood Ω C t e.images) :
    (preEval Ω C hno t e).read.val = (preEval Ω C hno t' e).read.val:=by
  obtain ⟨tn,htn⟩:=normalize_transport Ω C hno hC t
  have hn:=(Expr.nfTerm_spec (t.typing.weakNorm hw)).2
  exact (htn.read e hg).2.trans ((normal_tree_independence Ω C hno tn hn t' e).2 s r rfl rfl)
end S_wpc_barendregt_geuvers_klop.ObsVals
end OMA
namespace OMA
namespace S_wpc_barendregt_geuvers_klop.ObsVals
section
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
theorem normal_subst_eq {Γ:List (Expr S)} {A:Expr S} {s:S}
    (hA:HasType P Γ A (.sort s)) (e:ValEnv (hw:=hw) Ω C hno Γ) :
    (A.nfTerm.subst e.images).nfTerm = (A.subst e.images).nfTerm :=
  Expr.nfTerm_converts ((CTower.HasType.subst (hA.nfTerm hw) e.typed).weakNorm hw)
    ((CTower.HasType.subst hA e.typed).weakNorm hw)
    (.symm _ _ ((Expr.nfTerm_spec (hA.weakNorm hw)).1.converts.subst e.images))
noncomputable def normalRead {Γ:List (Expr S)} {A:Expr S} {s:S}
    (hA:HasType P Γ A (.sort s)) (e:ValEnv (hw:=hw) Ω C hno Γ) :
    Candidate Ω (A.subst e.images).nfTerm :=
  ⟨(preEval Ω C hno (TyTree.ofTyping (hA.nfTerm hw)) e).read.val,
    normal_subst_eq Ω C hno hA e ▸ (preEval Ω C hno (TyTree.ofTyping (hA.nfTerm hw)) e).read.property⟩
theorem normalRead_eq {Γ:List (Expr S)} {A:Expr S} {s r:S}
    (hA:HasType P Γ A (.sort s)) (t:TyTree P Γ A.nfTerm (.sort r))
    (e:ValEnv (hw:=hw) Ω C hno Γ) :
    (normalRead Ω C hno hA e).val = (preEval Ω C hno t e).read.val :=
  (normal_tree_independence Ω C hno _ (Expr.nfTerm_spec (hA.weakNorm hw)).2 t e).2 s r rfl rfl
theorem preEval_read_cast_expr {Γ:List (Expr S)} {M N T:Expr S}
    (he:M = N) (t:TyTree P Γ M T)
    (e:ValEnv (hw:=hw) Ω C hno Γ) :
    (preEval Ω C hno (he ▸ t) e).read.val = (preEval Ω C hno t e).read.val:=by
  subst N
  rfl
theorem normalRead_eq_of_nf {Γ:List (Expr S)} {A N:Expr S} {s r:S}
    (hA:HasType P Γ A (.sort s)) (t:TyTree P Γ N (.sort r)) (hn:A.nfTerm = N)
    (e:ValEnv (hw:=hw) Ω C hno Γ) :
    (normalRead Ω C hno hA e).val = (preEval Ω C hno t e).read.val :=
  (normalRead_eq Ω C hno hA (hn.symm ▸ t) e).trans
    (preEval_read_cast_expr Ω C hno hn.symm t e)
theorem normalRead_congr {Γ:List (Expr S)} {A B:Expr S} {s r:S}
    (hA:HasType P Γ A (.sort s)) (hB:HasType P Γ B (.sort r)) (hc:Converts A B)
    (e:ValEnv (hw:=hw) Ω C hno Γ) :
    (normalRead Ω C hno hA e).val = (normalRead Ω C hno hB e).val:=by
  have he:=Expr.nfTerm_converts (hA.weakNorm hw) (hB.weakNorm hw) hc
  exact normalRead_eq_of_nf Ω C hno hA (TyTree.ofTyping (hB.nfTerm hw)) he e
theorem read_outside {Γ:List (Expr S)} {M T:Expr S} (t:TyTree P Γ M T)
    (e:ValEnv (hw:=hw) Ω C hno Γ) (ho:Ω.profile (M.subst e.images).nfTerm ∉ C) :
    (preEval Ω C hno t e).read.val = Cands.Top Ω (M.subst e.images).nfTerm:=by
  cases t <;> simp only [preEval,PreRes.lookup,PreRes.sort,PreRes.product,
    PreRes.abstraction,PreRes.application,PreRes.baseResult,PreRes.baseRead,ho,ite_false,dite_false]
theorem normalRead_outside {Γ:List (Expr S)} {A:Expr S} {s:S}
    (hA:HasType P Γ A (.sort s)) (e:ValEnv (hw:=hw) Ω C hno Γ)
    (ho:Ω.profile (A.subst e.images) ∉ C) :
    (normalRead Ω C hno hA e).val = Cands.Top Ω (A.subst e.images).nfTerm:=by
  have hh:=read_outside Ω C hno (TyTree.ofTyping (hA.nfTerm hw)) e (by
    rw [normal_subst_eq Ω C hno hA e,Ω.profile_nfTerm]; exact ho)
  exact hh.trans (congrArg (Cands.Top Ω) (normal_subst_eq Ω C hno hA e))
theorem normalRead_sort {Γ:List (Expr S)} {s r:S}
    (hs:HasType P Γ (.sort s) (.sort r)) (e:ValEnv (hw:=hw) Ω C hno Γ) :
    (normalRead Ω C hno hs e).val = Cands.Top Ω (.sort s):=by
  obtain ⟨t,ha,hc⟩:=hs.generation
  let tree:TyTree P Γ (.sort s) (.sort r):=.sort hs ha hc
  exact (normalRead_eq_of_nf Ω C hno hs tree (Expr.nfTerm_of_normal (Normal.sort s)) e).trans (by
    simp only [tree,preEval,PreRes.sort,Expr.subst,Expr.nfTerm_of_normal (Normal.sort s)])
noncomputable def R {Γ:List (Expr S)} (A:Expr S) (e:ValEnv (hw:=hw) Ω C hno Γ):Set (Expr S) :=
  if Profile P Γ A ∈ C then
    if hs:∃ s,HasType P Γ A (.sort s) then (normalRead Ω C hno hs.choose_spec e).val
    else Cands.Top Ω (A.subst e.images).nfTerm
  else Cands.Top Ω (A.subst e.images).nfTerm
theorem R_candidate {Γ:List (Expr S)} (A:Expr S) (e:ValEnv (hw:=hw) Ω C hno Γ) :
    Cands.IsCandidate Ω (A.subst e.images).nfTerm (R Ω C hno A e):=by
  unfold R
  split
  · split
    · exact (normalRead Ω C hno _ e).property
    · exact Cands.top_candidate
  · exact Cands.top_candidate
theorem R_of_sorted {Γ:List (Expr S)} {A:Expr S} {s:S}
    (hA:HasType P Γ A (.sort s)) (e:ValEnv (hw:=hw) Ω C hno Γ)
    (hg:Profile P Γ A ∈ C) :
    R Ω C hno A e = (normalRead Ω C hno hA e).val:=by
  simp only [R,hg,dite_true,show ∃ s,HasType P Γ A (.sort s) from ⟨s,hA⟩]
  exact normalRead_congr Ω C hno _ hA (.refl _) e
theorem R_outside {Γ:List (Expr S)} (A:Expr S) (e:ValEnv (hw:=hw) Ω C hno Γ)
    (ho:Profile P Γ A ∉ C ∨ Ω.profile (A.subst e.images) ∉ C) :
    R Ω C hno A e = Cands.Top Ω (A.subst e.images).nfTerm:=by
  unfold R
  split_ifs with hg hs
  · exact normalRead_outside Ω C hno hs.choose_spec e (ho.resolve_left (not_not.mpr hg))
  · rfl
  · rfl
theorem R_sort {Γ:List (Expr S)} (s:S) (e:ValEnv (hw:=hw) Ω C hno Γ) :
    R Ω C hno (.sort s) e = Cands.Top Ω (.sort s):=by
  unfold R
  split_ifs with hg hs
  · exact normalRead_sort Ω C hno hs.choose_spec e
  · simp only [Expr.subst,Expr.nfTerm_of_normal (Normal.sort s)]
  · simp only [Expr.subst,Expr.nfTerm_of_normal (Normal.sort s)]
namespace ValEnv
variable {Ω C hno}
noncomputable def ofImages {Γ:List (Expr S)} (σ:Nat → Expr S)
    (hσ:Ω.TySub Γ σ):ValEnv (hw:=hw) Ω C hno Γ where
  images:=σ
  typed:=hσ
  parameters:=fun i => if hi:∃ A,Lookup Γ i A then
    (PayFits.exists_of_actual (hno:=hno) ⟨_,(hσ _ _ hi.choose_spec).actual_type hw⟩).choose else none
  lawful:=by
    intro i A hi
    simp only [dif_pos (show ∃ B,Lookup Γ i B from ⟨A,hi⟩)]
    have he:=Lookup.unique (show Lookup Γ i (Exists.choose (show ∃ B,Lookup Γ i B from ⟨A,hi⟩)) from
      (show ∃ B,Lookup Γ i B from ⟨A,hi⟩).choose_spec) hi
    simpa only [he] using (PayFits.exists_of_actual (hno:=hno)
      ⟨_,(hσ _ _ (show ∃ B,Lookup Γ i B from ⟨A,hi⟩).choose_spec).actual_type hw⟩).choose_spec
def Ext {Γ:List (Expr S)} {D:Expr S} (e:ValEnv (hw:=hw) Ω C hno Γ)
    (f:ValEnv (hw:=hw) Ω C hno (D :: Γ)) (n:Expr S):Prop :=
  f.images = Expr.extend e.images n ∧ ∀ i,f.parameters (i+1) = e.parameters i
theorem Ext.reindexed {Γ:List (Expr S)} {D n:Expr S}
    {e:ValEnv (hw:=hw) Ω C hno Γ} {f:ValEnv (hw:=hw) Ω C hno (D :: Γ)}
    (he:e.Ext f n):e.Reindexed f Nat.succ:=by
  intro i _
  exact ⟨(congrFun he.1 (i+1)).symm,(he.2 i).symm⟩
theorem cons_ext {Γ:List (Expr S)} {D n:Expr S} (e:ValEnv (hw:=hw) Ω C hno Γ)
    (hn:Ω.HasType n (D.subst e.images)) (p:Option (RawValue (hw:=hw) Ω C hno))
    (hp:PayFits Ω C hno (D.subst e.images).nfTerm p):e.Ext (e.cons hn p hp) n :=
  ⟨rfl,fun _ => rfl⟩
theorem extend_exists {Γ:List (Expr S)} {D n:Expr S} (e:ValEnv (hw:=hw) Ω C hno Γ)
    (hn:Ω.HasType n (D.subst e.images)):∃ f:ValEnv (hw:=hw) Ω C hno (D :: Γ),e.Ext f n:=by
  obtain ⟨p,hp⟩:=PayFits.exists_of_actual (hno:=hno) ⟨_,hn.actual_type hw⟩
  exact ⟨e.cons hn p hp,e.cons_ext hn p hp⟩
theorem ext_data {Γ:List (Expr S)} {e f:ValEnv (hw:=hw) Ω C hno Γ}
    (hi:e.images = f.images) (hp:e.parameters = f.parameters):e = f:=by
  cases e; cases f
  cases hi; cases hp
  rfl
theorem Ext.payload {Γ:List (Expr S)} {D n:Expr S}
    {e:ValEnv (hw:=hw) Ω C hno Γ} {f:ValEnv (hw:=hw) Ω C hno (D :: Γ)}
    (he:e.Ext f n):PayFits Ω C hno (D.subst e.images).nfTerm (f.parameters 0):=by
  have hp:=f.lawful 0 _ (.zero D Γ)
  simpa only [he.1,Expr.subst_raise_extend] using hp
theorem Ext.eq_cons {Γ:List (Expr S)} {D n:Expr S}
    {e:ValEnv (hw:=hw) Ω C hno Γ} {f:ValEnv (hw:=hw) Ω C hno (D :: Γ)}
    (he:e.Ext f n) (hn:Ω.HasType n (D.subst e.images)) :
    f = e.cons hn (f.parameters 0) he.payload:=by
  apply ext_data he.1
  funext i
  cases i with
  | zero => rfl
  | succ i => exact he.2 i
end ValEnv
theorem R_sorted_conversion {Γ:List (Expr S)} {A B:Expr S} {s r:S}
    (hA:HasType P Γ A (.sort s)) (hB:HasType P Γ B (.sort r)) (hc:Converts A B)
    (e:ValEnv (hw:=hw) Ω C hno Γ):R Ω C hno A e = R Ω C hno B e:=by
  have hp:=Profile.converts (P:=P) (Γ:=Γ) (hA.weakNorm hw) (hB.weakNorm hw) hc
  by_cases ha:Profile P Γ A ∈ C
  · rw [R_of_sorted Ω C hno hA e ha,R_of_sorted Ω C hno hB e (hp ▸ ha)]
    exact normalRead_congr Ω C hno hA hB hc e
  · rw [R_outside Ω C hno A e (.inl ha),R_outside Ω C hno B e (.inl (hp ▸ ha))]
    exact congrArg (Cands.Top Ω) (Expr.nfTerm_converts
      ((CTower.HasType.subst hA e.typed).weakNorm hw)
      ((CTower.HasType.subst hB e.typed).weakNorm hw) (hc.subst e.images))
theorem R_nfTerm {Γ:List (Expr S)} {A:Expr S} (hA:Expected P Γ A)
    (e:ValEnv (hw:=hw) Ω C hno Γ):R Ω C hno A e = R Ω C hno A.nfTerm e:=by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · rw [Expr.nfTerm_of_normal (Normal.sort s)]
  · exact R_sorted_conversion Ω C hno hA (hA.nfTerm hw)
      (Expr.nfTerm_spec (hA.weakNorm hw)).1.converts e
theorem R_conversion {Γ:List (Expr S)} {A B:Expr S}
    (hA:Expected P Γ A) (hB:Expected P Γ B) (hc:Converts A B)
    (e:ValEnv (hw:=hw) Ω C hno Γ):R Ω C hno A e = R Ω C hno B e:=by
  rw [R_nfTerm Ω C hno hA e,R_nfTerm Ω C hno hB e,
    Expr.nfTerm_converts (hA.wn hw) (hB.wn hw) hc]
theorem normalRead_weaken {Γ:List (Expr S)} {A D:Expr S} {s r:S}
    (hA:HasType P Γ A (.sort s)) (hD:HasType P Γ D (.sort r))
    {e:ValEnv (hw:=hw) Ω C hno Γ} {f:ValEnv (hw:=hw) Ω C hno (D :: Γ)}
    {n:Expr S} (he:e.Ext f n) :
    (normalRead Ω C hno (HasType.weaken hA hD) f).val = (normalRead Ω C hno hA e).val:=by
  let t:=TyTree.ofTyping (hA.nfTerm hw)
  have hh:=normalRead_eq_of_nf Ω C hno (HasType.weaken hA hD)
    (t.rename (.cons hD.valid hD) Nat.succ (TyTree.DeclRenaming.weaken D))
    (Expr.nfTerm_rename (hA.weakNorm hw) Nat.succ) f
  exact hh.trans (preEvaluate_rename Ω C hno t (.cons hD.valid hD) Nat.succ
    (TyTree.DeclRenaming.weaken D) e f he.reindexed).2.symm
theorem R_weakening {Γ:List (Expr S)} {A D:Expr S} {r:S}
    (hA:Expected P Γ A) (hD:HasType P Γ D (.sort r))
    {e:ValEnv (hw:=hw) Ω C hno Γ} {f:ValEnv (hw:=hw) Ω C hno (D :: Γ)}
    {n:Expr S} (he:e.Ext f n):R Ω C hno (A.rename Nat.succ) f = R Ω C hno A e:=by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · exact (R_sort Ω C hno s f).trans (R_sort Ω C hno s e).symm
  · have hp:=Profile.weaken hw hA hD
    by_cases ha:Profile P Γ A ∈ C
    · rw [R_of_sorted Ω C hno (HasType.weaken hA hD) f (hp ▸ ha),R_of_sorted Ω C hno hA e ha]
      exact normalRead_weaken Ω C hno hA hD he
    · rw [R_outside Ω C hno _ f (.inl (hp ▸ ha)),R_outside Ω C hno _ e (.inl ha),
        he.1,Expr.subst_raise_extend]
theorem normalRead_recontext {Γ Δ:List (Expr S)} {A:Expr S} {s:S}
    (hA:HasType P Γ A (.sort s)) (h:ContextEquivalent P Γ Δ)
    (e:ValEnv (hw:=hw) Ω C hno Γ) (f:ValEnv (hw:=hw) Ω C hno Δ)
    (he:e.SameData f) :
    (normalRead Ω C hno hA e).val = (normalRead Ω C hno ((h.typing _ _).mp hA) f).val:=by
  let t:=TyTree.ofTyping (hA.nfTerm hw)
  exact (preEval_recontext Ω C hno t h e f he).2.trans
    (normalRead_eq Ω C hno ((h.typing _ _).mp hA) (t.recontext h) f).symm
theorem R_recontext {Γ Δ:List (Expr S)} {A:Expr S} (hA:Expected P Γ A)
    (h:ContextEquivalent P Γ Δ)
    (e:ValEnv (hw:=hw) Ω C hno Γ) (f:ValEnv (hw:=hw) Ω C hno Δ)
    (he:e.SameData f):R Ω C hno A e = R Ω C hno A f:=by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · exact (R_sort Ω C hno s e).trans (R_sort Ω C hno s f).symm
  · have hp:Profile P Γ A = Profile P Δ A:=by
      ext s; exact h.typing _ _
    by_cases ha:Profile P Γ A ∈ C
    · rw [R_of_sorted Ω C hno hA e ha,R_of_sorted Ω C hno ((h.typing _ _).mp hA) f (hp ▸ ha)]
      exact normalRead_recontext Ω C hno hA h e f he
    · rw [R_outside Ω C hno _ e (.inl ha),R_outside Ω C hno _ f (.inl (hp ▸ ha)),he.1]
end
section
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
variable (hC:IsComp (PriEdge P) C)
include hC
theorem R_eq_normalRead_relevant {Γ:List (Expr S)} {A:Expr S} {s:S}
    (hA:HasType P Γ A (.sort s)) (hr:Relevant (P:=P) C Γ A)
    (e:ValEnv (hw:=hw) Ω C hno Γ):R Ω C hno A e = (normalRead Ω C hno hA e).val:=by
  by_cases hg:Profile P Γ A ∈ C
  · exact R_of_sorted Ω C hno hA e hg
  · have ha:Ω.profile (A.subst e.images) ∉ C:=fun ha =>
      hg (relevant_actual_mem Ω C hw hC hA e.typed hr ha)
    exact (R_outside Ω C hno A e (.inl hg)).trans (normalRead_outside Ω C hno hA e ha).symm
theorem R_eq_read_normal {Γ:List (Expr S)} {A:Expr S} {s:S}
    (t:TyTree P Γ A (.sort s)) (hn:Normal A) (hr:Relevant (P:=P) C Γ A)
    (e:ValEnv (hw:=hw) Ω C hno Γ):R Ω C hno A e = (preEval Ω C hno t e).read.val :=
  (R_eq_normalRead_relevant Ω C hno hC t.typing hr e).trans
    (normalRead_eq_of_nf Ω C hno t.typing t (Expr.nfTerm_of_normal hn) e)
theorem R_eq_read_good {Γ:List (Expr S)} {A:Expr S} {s:S}
    (t:TyTree P Γ A (.sort s)) (hr:Relevant (P:=P) C Γ A)
    (e:ValEnv (hw:=hw) Ω C hno Γ) (hg:ReadGood Ω C t e.images) :
    R Ω C hno A e = (preEval Ω C hno t e).read.val :=
  (R_eq_normalRead_relevant Ω C hno hC t.typing hr e).trans
    (good_normal_read Ω C hno hC t (TyTree.ofTyping (t.typing.nfTerm hw)) e hg).symm
theorem normal_product_candidate {Γ:List (Expr S)} {D E:Expr S} {a b c:S}
    (d:TyTree P Γ D (.sort a)) (q:TyTree P (D :: Γ) E (.sort b)) (hr:P.rule a b c)
    (hn:Normal (.pi D E)) (hg:Profile P Γ (.pi D E) ∈ C)
    (e:ValEnv (hw:=hw) Ω C hno Γ) (ha:Ω.profile ((Expr.pi D E).subst e.images) ∈ C) :
    R Ω C hno (.pi D E) e = (PreRes.productCandidate d.typing q.typing hr
      (preEval Ω C hno d) (preEval Ω C hno q) e).val:=by
  let t:TyTree P Γ (.pi D E) (.sort c) :=
    .product (.product d.typing q.typing hr) d q hr (.refl _)
  have he:=R_eq_read_normal Ω C hno hC t hn ⟨_,hg,.refl _⟩ e
  exact he.trans (by
    simp only [t,preEval,PreRes.product,Ω.profile_nfTerm,ha,ite_true])
theorem normal_product_iff {Γ:List (Expr S)} {D E:Expr S} {s:S}
    (hp:HasType P Γ (.pi D E) (.sort s)) (hn:Normal (.pi D E))
    (hg:Profile P Γ (.pi D E) ∈ C) (e:ValEnv (hw:=hw) Ω C hno Γ)
    (ha:Ω.profile ((Expr.pi D E).subst e.images) ∈ C) (h:Expr S) :
    h ∈ R Ω C hno (.pi D E) e ↔
      h ∈ Cands.Top Ω ((Expr.pi D E).subst e.images).nfTerm ∧
      ∀ n,n ∈ R Ω C hno D e → ∀ f:ValEnv (hw:=hw) Ω C hno (D :: Γ),
        e.Ext f n → Expr.app h n ∈ R Ω C hno E f:=by
  obtain ⟨a,b,c,hD,hE,hr,_⟩:=hp.generation_pi
  let d:=TyTree.ofTyping hD
  let q:=TyTree.ofTyping hE
  let t:=PreRes.productData hD hE hr e
  let bd:t.BodyReads:=fun n hn p hp => (preEval Ω C hno q (t.extend hn p hp)).read
  have hf:=Profile.triple hw hp
  have hdrel:Relevant (P:=P) C Γ D:=⟨_,hg,.single (.domain hf)⟩
  have herel:Relevant (P:=P) C (D :: Γ) E:=⟨_,hg,.single (.codomain hf)⟩
  have hrd:=R_eq_read_normal Ω C hno hC d hn.pi_domain hdrel e
  have htest:t.testers (preEval Ω C hno d e).read = R Ω C hno D e:=by
    unfold ProdInst.testers
    split_ifs with hc
    · exact hrd.symm
    · exact (R_outside Ω C hno D e (.inr (by simpa only [t,PreRes.productData,
        ProdInst.domainNF,ProdInst.rawDomain,Ω.profile_nfTerm] using hc))).symm
  have hre:∀ f:ValEnv (hw:=hw) Ω C hno (D :: Γ),
      R Ω C hno E f = (preEval Ω C hno q f).read.val :=
    fun f => R_eq_read_normal Ω C hno hC q hn.pi_body herel f
  rw [normal_product_candidate Ω C hno hC d q hr hn hg e ha]
  change h ∈ (t.candidate (preEval Ω C hno d e).read bd).val ↔ _
  constructor
  · intro hh
    refine ⟨?_,?_⟩
    · exact t.product_nf.symm ▸ hh.1
    · intro n hnr f he
      have hnt:n ∈ t.testers (preEval Ω C hno d e).read:=htest.symm ▸ hnr
      have hnty:=(t.testers_top _ hnt).1
      have hfcons:=he.eq_cons (t.rawArgument hnty)
      rw [hfcons,hre]
      by_cases hc:Ω.profile (t.targetNF n) ∈ C
      · exact t.candidate_body _ bd hh hnt hc (f.parameters 0) he.payload
      · have hout:=t.candidate_outside _ bd hh hnt hc
        have heo:=read_outside Ω C hno q (t.extend hnty (f.parameters 0) he.payload) hc
        exact heo.symm ▸ hout
  · rintro ⟨hht,hbody⟩
    refine ⟨t.product_nf ▸ hht,?_⟩
    intro n hn U hU
    have hnty:=(t.testers_top _ hn).1
    have hnr:n ∈ R Ω C hno D e:=htest ▸ hn
    simp only [ProdInst.fibers,hnty,dite_true] at hU
    split_ifs at hU with hc
    · obtain ⟨p,hp,rfl⟩:=hU
      rw [← hre]
      exact hbody n hnr (t.extend hnty p hp) (e.cons_ext (t.rawArgument hnty) p hp)
    · have heU:U = Cands.Top Ω (t.targetNF n):=hU
      rw [heU]
      obtain ⟨p,hp⟩:=PayFits.exists_of_actual (hno:=hno) ⟨_,(t.rawArgument hnty).actual_type hw⟩
      have hmem:=hbody n hnr (t.extend hnty p hp) (e.cons_ext (t.rawArgument hnty) p hp)
      rw [hre,read_outside Ω C hno q (t.extend hnty p hp) hc] at hmem
      exact hmem
end
section
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
namespace ValEnv
variable {Ω C hno}
theorem Ext.argument {Γ:List (Expr S)} {D n:Expr S}
    {e:ValEnv (hw:=hw) Ω C hno Γ} {f:ValEnv (hw:=hw) Ω C hno (D :: Γ)}
    (he:e.Ext f n):Ω.HasType n (D.subst e.images):=by
  have hh:=f.typed 0 _ (.zero D Γ)
  simpa only [he.1,Expr.extend_zero,Expr.subst_raise_extend] using hh
theorem Ext.convert_domain {Γ:List (Expr S)} {D D' n:Expr S} {a b:S}
    (hD:HasType P Γ D (.sort a)) (hD':HasType P Γ D' (.sort b)) (hc:Converts D D')
    {e:ValEnv (hw:=hw) Ω C hno Γ} {f:ValEnv (hw:=hw) Ω C hno (D :: Γ)}
    (he:e.Ext f n):∃ g:ValEnv (hw:=hw) Ω C hno (D' :: Γ),e.Ext g n ∧ f.SameData g:=by
  have ht:=CTower.HasType.subst hD' e.typed
  have hnf:=Expr.nfTerm_converts ((CTower.HasType.subst hD e.typed).weakNorm hw)
    (ht.weakNorm hw) (hc.subst e.images)
  have hn:=he.argument.conversion ht (hc.subst e.images)
  let g:=e.cons hn (f.parameters 0) (hnf ▸ he.payload)
  refine ⟨g,e.cons_ext hn _ _,he.1,?_⟩
  funext i
  cases i with
  | zero => rfl
  | succ i => exact he.2 i
end ValEnv
theorem normalRead_compatible (hC:IsComp (PriEdge P) C)
    {Γ:List (Expr S)} {A:Expr S} {s:S} (hA:HasType P Γ A (.sort s))
    (e f:ValEnv (hw:=hw) Ω C hno Γ) (he:e.Compatible f) :
    (normalRead Ω C hno hA e).val = (normalRead Ω C hno hA f).val :=
  (preEval_compatible Ω C hno hC (TyTree.ofTyping (hA.nfTerm hw)) e f he).2
theorem R_compatible (hC:IsComp (PriEdge P) C)
    {Γ:List (Expr S)} {A:Expr S} (hA:Expected P Γ A)
    (e f:ValEnv (hw:=hw) Ω C hno Γ) (he:e.Compatible f) :
    R Ω C hno A e = R Ω C hno A f:=by
  rcases hA with ⟨s,rfl⟩ | ⟨s,hA⟩
  · exact (R_sort Ω C hno s e).trans (R_sort Ω C hno s f).symm
  · by_cases hc:Profile P Γ A ∈ C
    · rw [R_of_sorted Ω C hno hA e hc,R_of_sorted Ω C hno hA f hc]
      exact normalRead_compatible Ω C hno hC hA e f he
    · rw [R_outside Ω C hno A e (.inl hc),R_outside Ω C hno A f (.inl hc),
        e.actual_expr_eq he.1 hA]
theorem R_binder_conversion {Γ:List (Expr S)} {D D' E E' n:Expr S} {a b s r:S}
    (hD:HasType P Γ D (.sort a)) (hD':HasType P Γ D' (.sort b)) (hc:Converts D D')
    (hE:HasType P (D :: Γ) E (.sort s)) (hE':HasType P (D' :: Γ) E' (.sort r))
    (hh:Converts E E') (e:ValEnv (hw:=hw) Ω C hno Γ)
    (f:ValEnv (hw:=hw) Ω C hno (D :: Γ)) (g:ValEnv (hw:=hw) Ω C hno (D' :: Γ))
    (_he:e.Ext f n) (_he':e.Ext g n) (heq:f.SameData g) :
    R Ω C hno E f = R Ω C hno E' g:=by
  let hctx:=ContextEquivalent.head_conversion hD hD' hc
  exact (R_recontext Ω C hno (.sorted hE) hctx f g heq).trans
    (R_sorted_conversion Ω C hno ((hctx.typing _ _).mp hE) hE' hh g)
end
section
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
variable (hC:IsComp (PriEdge P) C)
include hC
theorem product_iff {Γ:List (Expr S)} {D E:Expr S} {s:S}
    (hp:HasType P Γ (.pi D E) (.sort s))
    (hg:Profile P Γ (.pi D E) ∈ C) (e:ValEnv (hw:=hw) Ω C hno Γ)
    (ha:Ω.profile ((Expr.pi D E).subst e.images) ∈ C) (h:Expr S) :
    h ∈ R Ω C hno (.pi D E) e ↔
      h ∈ Cands.Top Ω ((Expr.pi D E).subst e.images).nfTerm ∧
      ∀ n,n ∈ R Ω C hno D e → ∀ f:ValEnv (hw:=hw) Ω C hno (D :: Γ),
        e.Ext f n → Expr.app h n ∈ R Ω C hno E f:=by
  obtain ⟨a,b,c,hD,hE,hr,_⟩:=hp.generation_pi
  have hDN:=hD.nfTerm hw
  have hEN:=hE.nfTerm hw
  have cD:=(Expr.nfTerm_spec (hD.weakNorm hw)).1.converts
  have cE:=(Expr.nfTerm_spec (hE.weakNorm hw)).1.converts
  let ctx:=ContextEquivalent.head_conversion hD hDN cD
  have hEN':=(ctx.typing _ _).mp hEN
  have hpn:HasType P Γ (.pi D.nfTerm E.nfTerm) (.sort c):=.product hDN hEN' hr
  have nc:=Converts.pi cD cE
  have hn:Normal (.pi D.nfTerm E.nfTerm):=.pi
    (Expr.nfTerm_spec (hD.weakNorm hw)).2 (Expr.nfTerm_spec (hE.weakNorm hw)).2
  have hprof:=Profile.converts (P:=P) (Γ:=Γ) (hp.weakNorm hw) (hpn.weakNorm hw) nc
  have haprof:=Ω.profile_converts ((CTower.HasType.subst hp e.typed).weakNorm hw)
    ((CTower.HasType.subst hpn e.typed).weakNorm hw) (nc.subst e.images)
  have hnf:=Expr.nfTerm_converts ((CTower.HasType.subst hp e.typed).weakNorm hw)
    ((CTower.HasType.subst hpn e.typed).weakNorm hw) (nc.subst e.images)
  have hR:=R_sorted_conversion Ω C hno hp hpn nc e
  have hRD:=R_nfTerm Ω C hno (.sorted hD) e
  rw [hR,normal_product_iff Ω C hno hC hpn hn (hprof ▸ hg) e (haprof ▸ ha) h,hnf]
  constructor
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hnr f he
    obtain ⟨g,heg,hfg⟩:=he.convert_domain hD hDN cD
    have hmem:=hbody n (hRD ▸ hnr) g heg
    have heq:=R_binder_conversion Ω C hno hD hDN cD hE hEN' cE e f g he heg hfg
    exact heq.symm ▸ hmem
  · rintro ⟨ht,hbody⟩
    refine ⟨ht,?_⟩
    intro n hnr g heg
    obtain ⟨f,hef,hgf⟩:=heg.convert_domain hDN hD (.symm _ _ cD)
    have hmem:=hbody n (hRD.symm ▸ hnr) f hef
    have heq:=R_binder_conversion Ω C hno hD hDN cD hE hEN' cE e f g hef heg ⟨hgf.1.symm,hgf.2.symm⟩
    exact heq ▸ hmem
theorem product_intro {Γ:List (Expr S)} {D E:Expr S} {s:S}
    (e:ValEnv (hw:=hw) Ω C hno Γ) (hp:HasType P Γ (.pi D E) (.sort s))
    (hg:Profile P Γ (.pi D E) ∈ C) (ha:Ω.profile ((Expr.pi D E).subst e.images) ∈ C)
    (h:Expr S) (ht:h ∈ Cands.Top Ω ((Expr.pi D E).subst e.images).nfTerm)
    (hb:∀ n,n ∈ R Ω C hno D e → ∀ f:ValEnv (hw:=hw) Ω C hno (D :: Γ),
      e.Ext f n → Expr.app h n ∈ R Ω C hno E f):h ∈ R Ω C hno (.pi D E) e :=
  (product_iff Ω C hno hC hp hg e ha h).mpr ⟨ht,hb⟩
end
section
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
variable (hC:IsComp (PriEdge P) C)
include hC
theorem product_argument_active {Γ:List (Expr S)} {D E N:Expr S} {s:S}
    (hp:HasType P Γ (.pi D E) (.sort s)) (hN:HasType P Γ N D)
    (e:ValEnv (hw:=hw) Ω C hno Γ)
    (hpC:Ω.profile ((Expr.pi D E).subst e.images) ∈ C)
    (hNC:Ω.profile ((E.instantiate N).subst e.images) ∈ C)
    (hD:Ω.profile (D.subst e.images) ∈ ObsLayers P C) :
    ActL P C (Ω.profile (D.subst e.images)):=by
  obtain ⟨J,hf,hpath⟩:=Ω.frame_profiles hw (CTower.HasType.subst hp e.typed)
    (CTower.HasType.subst hN e.typed)
  have hJC:J ∈ C:=hC.between (by simpa only [Expr.instantiate_subst] using hNC)
    hpC hpath.reach (.single (.codomain hf))
  exact ⟨_,⟨hD,J,hJC,_,hpC,hf⟩,.refl _⟩
theorem R_instantiate_normal {Γ:List (Expr S)} {D E N:Expr S} {a b c:S}
    (hD:HasType P Γ D (.sort a)) (hE:HasType P (D :: Γ) E (.sort b)) (hr:P.rule a b c)
    (n:TyTree P Γ N D) (hnE:Normal E) (hnN:Normal N)
    (e:ValEnv (hw:=hw) Ω C hno Γ)
    (hg:Profile P Γ (.pi D E) ∈ C) (ha:Ω.profile ((Expr.pi D E).subst e.images) ∈ C)
    (hNC:Ω.profile ((E.instantiate N).subst e.images) ∈ C) :
    R Ω C hno E (e.cons (CTower.HasType.subst n.typing e.typed)
      (preEval Ω C hno n e).parameter (preEval Ω C hno n e).parameter_fits) =
    R Ω C hno (E.instantiate N) e:=by
  let q:=TyTree.ofTyping hE
  let f:=e.cons (CTower.HasType.subst n.typing e.typed)
    (preEval Ω C hno n e).parameter (preEval Ω C hno n e).parameter_fits
  let ts:=TyTree.StoredSubstitution.single n
  let qt:=q.subst hD.valid (Expr.single N) ts
  have hp:=HasType.product hD hE hr
  have hrel:Relevant (P:=P) C (D :: Γ) E:=⟨_,hg,.single (.codomain (Profile.triple hw hp))⟩
  have hrelN:Relevant (P:=P) C Γ (E.instantiate N) :=
    ⟨_,hg,(Profile.instantiate_product_path hw hp n.typing).reach⟩
  have hgood:ReadGood Ω C q f.images:=(normal_good Ω C hw hC q hnE f.images f.typed).2 b rfl hrel
  have hgN:ActL P C (Ω.profile (D.subst e.images)) → ValGood Ω C n e.images :=
    (normal_good Ω C hw hC n hnN e.images e.typed).1
  have hguard:SubstitutionGuard Ω C (D :: Γ) (Expr.single N) f.images :=
    single_guard Ω C e.images (product_argument_active Ω C hno hC hp n.typing e ha hNC)
  have hfi:f.images = Expr.consSub (N.subst e.images) e.images:=by
    funext i; cases i <;> rfl
  have hgR:=single_goodReplacement Ω C n e.images hgN
  have hgood':ReadGood Ω C qt e.images:=(goodness_subst Ω C hw q hD.valid (Expr.single N) ts
    e.images e.typed (by simpa only [Expr.comp_single,←hfi] using hguard) hgR).2
      (by simpa only [Expr.comp_single,←hfi] using hgood)
  have heval:=(preEvaluate_subst Ω C hno q hD.valid (Expr.single N) ts f e
    (single_assigned Ω C hno n e) hguard).2 hgood
  exact (R_eq_read_normal Ω C hno hC q hnE hrel f).trans (heval.trans
    (R_eq_read_good Ω C hno hC qt hrelN e hgood').symm)
theorem specialization {Γ:List (Expr S)} {D E N:Expr S} {s:S}
    (e:ValEnv (hw:=hw) Ω C hno Γ) (hp:HasType P Γ (.pi D E) (.sort s))
    (hN:HasType P Γ N D) (hg:Profile P Γ (.pi D E) ∈ C)
    (ha:Ω.profile ((Expr.pi D E).subst e.images) ∈ C) (h:Expr S)
    (hh:h ∈ R Ω C hno (.pi D E) e) (hn:N.subst e.images ∈ R Ω C hno D e) :
    Expr.app h (N.subst e.images) ∈ R Ω C hno (E.instantiate N) e:=by
  obtain ⟨a,b,c,hD,hE,hr,_⟩:=hp.generation_pi
  have hNN:=hN.nfTerm hw
  let n:=TyTree.ofTyping hNN
  let pn:=(preEval Ω C hno n e).parameter
  have pp:=(preEval Ω C hno n e).parameter_fits
  let f:=e.cons (CTower.HasType.subst hN e.typed) pn pp
  let g:=e.cons (CTower.HasType.subst hNN e.typed) pn pp
  have hm:=((product_iff Ω C hno hC hp hg e ha h).mp hh).2 (N.subst e.images) hn f
    (e.cons_ext _ pn pp)
  have hnE:=(Expr.nfTerm_spec (hE.weakNorm hw)).2
  have hnN:=(Expr.nfTerm_spec (hN.weakNorm hw)).2
  have cE:=(Expr.nfTerm_spec (hE.weakNorm hw)).1.converts
  have cN:=(Expr.nfTerm_spec (hN.weakNorm hw)).1.converts
  have hp':HasType P Γ (.pi D E.nfTerm) (.sort c):=.product hD (hE.nfTerm hw) hr
  have cP:Converts (.pi D E) (.pi D E.nfTerm):=.pi (.refl _) cE
  have cT:Converts (E.instantiate N) (E.nfTerm.instantiate N.nfTerm) :=
    .trans _ _ _ (cE.subst (Expr.single N)) (cN.instantiate_right E.nfTerm)
  have hT:=hE.instantiate hN
  have hT':=(hE.nfTerm hw).instantiate hNN
  have hRT:=R_sorted_conversion Ω C hno hT hT' cT e
  by_cases htC:Ω.profile ((E.nfTerm.instantiate N.nfTerm).subst e.images) ∈ C
  · have hgg:=Profile.converts (P:=P) (Γ:=Γ) (hp.weakNorm hw) (hp'.weakNorm hw) cP
    have haa:=Ω.profile_converts ((CTower.HasType.subst hp e.typed).weakNorm hw)
      ((CTower.HasType.subst hp' e.typed).weakNorm hw) (cP.subst e.images)
    have hfg:f.Compatible g:=by
      constructor
      · intro i hi
        cases i with
        | zero => exact cN.subst e.images
        | succ i => exact .refl _
      · intro i hi; cases i <;> rfl
    have hrE:=(R_nfTerm Ω C hno (.sorted hE) f).trans
      ((R_compatible Ω C hno hC (.sorted (hE.nfTerm hw)) f g hfg).trans
      (R_instantiate_normal Ω C hno hC hD (hE.nfTerm hw) hr n hnE hnN e (hgg ▸ hg) (haa ▸ ha) htC))
    exact hRT.symm ▸ (hrE ▸ hm)
  · have hmem:=(R_candidate Ω C hno E f).upper hm
    have he:(E.subst f.images).nfTerm = ((E.instantiate N).subst e.images).nfTerm:=by
      congr 1
      rw [← Expr.instantiate_subst,Expr.instantiate_liftSub]
      rfl
    have hnf:=Expr.nfTerm_converts ((CTower.HasType.subst hT e.typed).weakNorm hw)
      ((CTower.HasType.subst hT' e.typed).weakNorm hw) (cT.subst e.images)
    rw [hRT,R_outside Ω C hno _ e (.inr htC)]
    exact (hnf ▸ he ▸ hmem)
end
universe u
open Classical
variable {S:Type u} {P:Specification S} (Ω:CTower P) [Fintype S]
variable (C:Set (Set S)) {hw:SystemWeaklyNormalizing P} (hno:¬ ForbiddenConfiguration P C)
noncomputable def componentInterface (hC:IsComp (PriEdge P) C):ComponentInterface Ω hw C where
  Env:=ValEnv (hw:=hw) Ω C hno
  images:=ValEnv.images
  typed:=ValEnv.typed
  inhabit σ hσ:=⟨ValEnv.ofImages σ hσ,rfl⟩
  Ext:=ValEnv.Ext
  ext_images he:=he.1
  extend e _ _ hn:=e.extend_exists hn
  R:=R Ω C hno
  candidate e _:=R_candidate Ω C hno _ e
  conversion e ha hb hc:=R_conversion Ω C hno ha hb hc e
  outside e _ ho:=R_outside Ω C hno _ e ho
  weakening hd he hx:=R_weakening Ω C hno he hd hx
  product_intro e hp hg ha h ht hb:=product_intro Ω C hno hC e hp hg ha h ht hb
  specialization e hp hN hg ha h hh hn:=specialization Ω C hno hC e hp hN hg ha h hh hn
end S_wpc_barendregt_geuvers_klop.ObsVals
end OMA
namespace OMA.S_wpc_barendregt_geuvers_klop
universe u
private theorem feq {S:Type u} (P:Specification S) :
    (fun (i:Set S) => i.Nonempty ∧ ∃ Γ t,ValidContext P Γ ∧ Normal t ∧ i = {s | HasType P Γ t (.sort s)}) = FeasibleProfile P:=by
  funext i
  apply propext
  constructor <;> rintro ⟨hn,Γ,t,hg,ht,he⟩ <;> refine ⟨hn,Γ,t,hg,ht,?_⟩ <;> simpa [Profile,Expr.nfTerm_of_normal ht] using he.symm
private theorem teq {S:Type u} (P:Specification S) :
    (fun (i j k:Set S) => FeasibleProfile P i ∧ FeasibleProfile P j ∧ FeasibleProfile P k ∧ k = {c | ∃ a ∈ i,∃ b ∈ j,P.rule a b c}) = ProfileTriple P:=by
  funext i j k; apply propext
  constructor <;> rintro ⟨a,b,c,d⟩ <;> exact ⟨a,b,c,d⟩
private theorem eeq {S:Type u} (P:Specification S) :
    (fun (i k:Set S) (p:Bool) => if p then ∃ j,ProfileTriple P i j k else (FeasibleProfile P i ∧ FeasibleProfile P k ∧ k ⊂ i) ∨ ∃ j,ProfileTriple P j i k) = PriEdge P:=by
  funext i k p; apply propext; cases p
  · constructor
    · rintro (⟨a,b,c⟩ | ⟨j,hj⟩); exact .inclusion a b c; exact .codomain hj
    · intro h; cases h with
      | inclusion a b c => exact Or.inl ⟨a,b,c⟩
      | codomain h => exact Or.inr ⟨_,h⟩
  · constructor
    · rintro ⟨j,hj⟩; exact .domain hj
    · intro h; cases h with | domain h => exact ⟨_,h⟩
private theorem peq {V:Type u} :
    (fun (e:V → V → Bool → Prop) (i j:V) (b:Bool) => ∀ R:V → V → Bool → Prop,(∀ x,R x x false) → (∀ x y z p q,e x y p → R y z q → R x z (p.xor q)) → R i j b) = SignedPath:=by
  funext e i j b; apply propext
  constructor
  · intro h; exact h _ SignedPath.nil (fun _ _ _ _ _ a c => .cons a c)
  · intro h R hn hc; induction h with
    | nil x => exact hn x
    | cons h _ ih => exact hc _ _ _ _ _ h ih
end OMA.S_wpc_barendregt_geuvers_klop
open OMA.S_wpc_barendregt_geuvers_klop
theorem OMA.solution : OMA.R_wpc_barendregt_geuvers_klop_R1_H2_R1.H2:=by
  intro n P hw V F T E Path Cmp A Pos L G D
  have hF:F = FeasibleProfile P:=feq P
  have hT:T = ProfileTriple P:=by
    show (fun (i j k:V) => F i ∧ F j ∧ F k ∧ k = {c | ∃ a ∈ i,∃ b ∈ j,P.rule a b c}) = _
    rw [hF]; exact teq P
  have hE:E = PriEdge P:=by
    show (fun (i k:V) (p:Bool) => if p then ∃ j,T i j k else (F i ∧ F k ∧ k ⊂ i) ∨ ∃ j,T j i k) = _
    rw [hT,hF]; exact eeq P
  have hP:Path = SignedPath:=peq
  have hPos:Pos = PositivePath (PriEdge P):=by
    show Relation.ReflTransGen (fun i j => E i j false) = _
    rw [hE]; rfl
  have hL:L = fun C i => i ∈ ObsLayers P C:=by
    show (fun (C:Set V) i => ∃ s,{s} ∈ C ∧ (A s).Nonempty ∧ Pos (A s) i) = _
    rw [hPos]; rfl
  have hG:G = fun C => SecEdge P C:=by
    show (fun C i k (b:Bool) => L C i ∧ L C k ∧ (if b then ∃ j,L C j ∧ T i j k else E i k false)) = _
    rw [hL,hT,hE]
    funext C i k b
    apply propext
    cases b
    · constructor
      · rintro ⟨hi,hk,he⟩; exact .positive hi hk he
      · intro h; cases h with | positive hi hk he => exact ⟨hi,hk,he⟩
    · constructor
      · rintro ⟨hi,hk,j,hj,ht⟩; exact .negative hi hj hk ht
      · intro h; cases h with | negative hi hj hk ht => exact ⟨hi,hk,_,hj,ht⟩
  have hD:D = fun C i => DirectLayer P C i:=by
    show (fun (C:Set V) i => L C i ∧ ∃ j ∈ C,∃ k ∈ C,T i j k) = _
    rw [hL,hT]; rfl
  clear_value D G L Pos Path E T F
  subst hD hG hL hPos hP hE hT hF
  intro _ hn Γ f a D E hf ha sf sa
  obtain ⟨s,t,hat⟩:=hf.has_axiom
  let Ω:=ContextTowerConstruction.tower P hat
  apply application_sn_of_ground Ω hw _ hf ha sf sa
  apply all_ground_eq_top Ω hw
  intro C hC
  by_cases ho:∃ I ∈ C,SignedPath (PriEdge P) I I true
  · by_cases ht:∃ I J K,ProfileTriple P I J K ∧ I ∈ C ∧ J ∈ C ∧ K ∈ C
    · refine ⟨ObsVals.componentInterface Ω C ?_ hC⟩
      rintro ⟨U,hU,hpl,hneg,i,j,k,s,hijk,hj,hk,hs,hA,hpos⟩
      obtain ⟨I,J,K,h,hi,hj',hk'⟩:=ht
      refine hn ⟨C,hC,ho,⟨I,hi,J,hj',K,hk',h⟩,U,hU,?_,hneg,i,j,k,s,hijk,hj,hk,hs,hA,hpos⟩
      intro x hx b
      cases b
      · exact (hpl x hx).1
      · exact (hpl x hx).2
    · exact ⟨OneChildInterpretation.componentInterface Ω C hw hC
        (fun h hi hj hk => ht ⟨_,_,_,h,hi,hj,hk⟩)⟩
  · exact ⟨SignedInterpretation.componentInterface Ω hC hw (fun I hi hp => ho ⟨I,hi,hp⟩)⟩
