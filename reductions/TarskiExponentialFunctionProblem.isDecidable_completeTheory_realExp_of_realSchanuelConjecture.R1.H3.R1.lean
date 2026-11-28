import OMAReductions.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_realExp_of_realSchanuelConjecture_R1
import Mathlib.Computability.RE
import Mathlib.Computability.Primrec.List

/-! Finite premise search for the ordered exponential-field language. -/

namespace OMA.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_realExp_of_realSchanuelConjecture_R1_H3_R1

open FirstOrder Computable


private theorem realize_fold_imp {M : Type*} [Language.orderedExpField.Structure M] (Γ : List Language.orderedExpField.Sentence) (φ : Language.orderedExpField.Sentence) :
    M ⊨ Γ.foldr (fun ψ χ => ψ.imp χ) φ ↔ ((∀ ψ ∈ Γ, M ⊨ ψ) → M ⊨ φ) := by
  induction Γ with
  | nil => simp
  | cons a Γ ih =>
    rw [List.foldr_cons, Language.Sentence.realize_imp, ih]
    simp only [List.forall_mem_cons]
    tauto

private theorem finite_validity_iff (T : Language.orderedExpField.Theory) (φ : Language.orderedExpField.Sentence) :
    T ⊨ᵇ φ ↔ ∃ Γ : List Language.orderedExpField.Sentence, (∀ ψ ∈ Γ, ψ ∈ T) ∧
      (∅ : Language.orderedExpField.Theory) ⊨ᵇ Γ.foldr (fun ψ χ => ψ.imp χ) φ := by
  classical
  constructor
  · intro h
    obtain ⟨A, hA, hmodel⟩ := Language.Theory.models_iff_finset_models.mp h
    refine ⟨A.toList, fun ψ hψ => hA (Finset.mem_toList.mp hψ), ?_⟩
    rw [Language.Theory.models_sentence_iff]
    intro M
    apply (realize_fold_imp A.toList φ).mpr
    intro hΓ
    have hMA : M ⊨ (A : Language.orderedExpField.Theory) :=
      ⟨fun ψ hψ => hΓ ψ (Finset.mem_toList.mpr hψ)⟩
    exact hmodel.realize_sentence M
  · rintro ⟨Γ, hΓ, hmodel⟩
    rw [Language.Theory.models_sentence_iff]
    intro M
    have hMempty : M ⊨ (∅ : Language.orderedExpField.Theory) := (∅ : Language.orderedExpField.Theory).model_iff.mpr (by simp)
    exact (realize_fold_imp Γ φ).mp (hmodel.realize_sentence M)
      (fun ψ hψ => T.realize_sentence_of_mem (hΓ ψ hψ))

private theorem list_all_computable {f : ℕ → Bool} (hf : Computable f) :
    Computable (fun l : List ℕ => l.all f) := by
  let step : List ℕ × Bool → List ℕ × Bool := fun x =>
    (x.1.tail, x.2 && (x.1.head?.map f).getD true)
  have hhead : Computable (fun l : List ℕ => (l.head?.map f).getD true) :=
    (Computable.option_map Primrec.list_head?.to_comp (hf.comp snd).to₂).option_getD (const true)
  have hstep : Computable step :=
    (Primrec.list_tail.to_comp.comp fst).pair
      (Primrec.and.to_comp.comp snd (hhead.comp fst))
  have hiter : Computable (fun l : List ℕ => Nat.rec (motive := fun _ => List ℕ × Bool) (l, true)
      (fun _ x => step x) l.length) :=
    Computable.nat_rec list_length (Computable.id.pair (const true))
      (hstep.comp (snd.comp snd)).to₂
  refine (snd.comp hiter).of_eq fun l => ?_
  have hscan (n : ℕ) (l : List ℕ) (a : Bool) (hn : n = l.length) :
      (Nat.rec (motive := fun _ => List ℕ × Bool) (l, a) (fun _ x => step x) n).2 = (a && l.all f) := by
    subst n
    have hIter (k : ℕ) (v : List ℕ × Bool) :
        Nat.rec (motive := fun _ => List ℕ × Bool) v (fun _ x => step x) k = step^[k] v := by
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', ← ih]
    rw [hIter]
    induction l generalizing a with
    | nil => simp
    | cons b l ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [step, List.tail_cons, List.head?_cons, Option.map_some, Option.getD_some]
      rw [ih, List.all_cons, Bool.and_assoc]
  simpa using hscan l.length l true rfl

private theorem re_exists_certificate {test : ℕ × ℕ → Bool} (ht : Computable test) :
    REPred (fun n : ℕ => ∃ k : ℕ, test (n,k) = true) := by
  let check : ℕ → ℕ → Option Unit := fun n k => cond (test (n,k)) (some ()) none
  have hcheck : Computable₂ check := Computable.cond ht (const (some ())) (const none)
  apply (Partrec.rfindOpt hcheck).dom_re.of_eq
  intro n
  rw [Nat.rfindOpt_dom]
  apply exists_congr
  intro k
  unfold check
  cases test (n,k) <;> simp

/-- A computable proof checker for validity in the empty theory. -/
def H1 : Prop :=
  ∃ check : ℕ × ℕ → Bool, Computable check ∧
    ∀ n : ℕ, (∃ k, check (n,k) = true) ↔
      ∃ φ : Language.orderedExpField.Sentence, Encodable.encode φ = n ∧ (∅ : Language.orderedExpField.Theory) ⊨ᵇ φ

/-- The fixed encoding computes a signed implication with a finite premise list,
returning none when any input is an invalid sentence code. -/
def H2 : Prop :=
  ∃ foldCode : (List ℕ × ℕ × Bool) → Option ℕ, Computable foldCode ∧
    ∀ (a : List ℕ) (n : ℕ) (b : Bool) (m : ℕ),
      foldCode (a,n,b) = some m ↔
      ∃ (Γ : List Language.orderedExpField.Sentence) (φ : Language.orderedExpField.Sentence),
        Γ.map Encodable.encode = a ∧ Encodable.encode φ = n ∧
        Encodable.encode (Γ.foldr (fun ψ χ => ψ.imp χ) (if b then φ else φ.not)) = m

theorem main : H1 → H2 →
    OMA.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_realExp_of_realSchanuelConjecture_R1.H3 := by
  intro hvalid hfold T hT b
  obtain ⟨verify, hverify, hvalid⟩ := hvalid
  obtain ⟨foldCode, hfoldC, hfold⟩ := hfold
  obtain ⟨axiomCode, haxiomC, haxiom⟩ := hT
  let test : ℕ × ℕ → Bool := fun x =>
    let a := Denumerable.ofNat (List ℕ) x.2.unpair.1
    a.all axiomCode &&
      (foldCode (a, x.1, b)).elim false (fun m => verify (m, x.2.unpair.2))
  have ha : Computable (fun x : ℕ × ℕ => Denumerable.ofNat (List ℕ) x.2.unpair.1) :=
    (Computable.ofNat _).comp (fst.comp (unpair.comp snd))
  have hk : Computable (fun x : ℕ × ℕ => x.2.unpair.2) := snd.comp (unpair.comp snd)
  have hob : Computable (fun x : ℕ × ℕ =>
      foldCode (Denumerable.ofNat (List ℕ) x.2.unpair.1, x.1, b)) :=
    hfoldC.comp (ha.pair (fst.pair (const b)))
  have hcheck : Computable (fun x : ℕ × ℕ =>
      (foldCode (Denumerable.ofNat (List ℕ) x.2.unpair.1, x.1, b)).elim false
        (fun m => verify (m, x.2.unpair.2))) := by
    apply (Computable.option_casesOn hob (const false)
      ((hverify.comp (snd.pair (hk.comp fst))).to₂)).of_eq
    intro x
    cases foldCode (Denumerable.ofNat (List ℕ) x.2.unpair.1, x.1, b) <;> rfl
  have ht : Computable test :=
    Primrec.and.to_comp.comp ((list_all_computable haxiomC).comp ha) hcheck
  apply (re_exists_certificate ht).of_eq
  intro n
  constructor
  · rintro ⟨k, h⟩
    let a := Denumerable.ofNat (List ℕ) k.unpair.1
    change (a.all axiomCode && (foldCode (a,n,b)).elim false
      (fun m => verify (m,k.unpair.2))) = true at h
    rw [Bool.and_eq_true] at h
    cases hc : foldCode (a,n,b) with
    | none => simp [hc] at h
    | some m =>
      obtain ⟨Γ, φ, hΓ, hφ, hm⟩ := (hfold a n b m).mp hc
      obtain ⟨χ, hχ, hpure⟩ := (hvalid m).mp ⟨k.unpair.2, by simpa [hc] using h.2⟩
      have heq := Encodable.encode_injective (hχ.trans hm.symm)
      subst χ
      refine ⟨φ, hφ, (finite_validity_iff T _).mpr ⟨Γ, ?_, hpure⟩⟩
      intro ψ hψ
      apply (haxiom ψ).mp
      have hψ' : Encodable.encode ψ ∈ a := hΓ ▸ List.mem_map.mpr ⟨ψ,hψ,rfl⟩
      exact List.all_eq_true.mp h.1 _ hψ'
  · rintro ⟨φ, rfl, hφ⟩
    obtain ⟨Γ, hΓ, hpure⟩ := (finite_validity_iff T _).mp hφ
    let a : List ℕ := Γ.map Encodable.encode
    let χ := Γ.foldr (fun ψ χ => ψ.imp χ) (if b then φ else φ.not)
    obtain ⟨k, hk⟩ := (hvalid (Encodable.encode χ)).mpr ⟨χ,rfl,hpure⟩
    refine ⟨Nat.pair (Encodable.encode a) k, ?_⟩
    have hcode : foldCode (a,Encodable.encode φ,b) = some (Encodable.encode χ) :=
      (hfold _ _ _ _).mpr ⟨Γ,φ,rfl,rfl,rfl⟩
    have hall : a.all axiomCode = true := by
      apply List.all_eq_true.mpr
      intro t ht
      obtain ⟨ψ,hψ,rfl⟩ := List.mem_map.mp ht
      exact (haxiom ψ).mpr (hΓ ψ hψ)
    simp [test, Nat.unpair_pair, Denumerable.ofNat_encode, hcode, hk, hall]

end OMA.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_realExp_of_realSchanuelConjecture_R1_H3_R1
