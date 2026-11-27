import OMAReductions.R_Erdos78_erdos_78_variants_strongly_explicit_R1

/-! A two-stack machine replaces the first binary word with zeros followed by
one, leaving the remaining input on its original stack. -/
namespace PadMachine
open Turing Computability ComplexityTheory BitstringEncoding

private def tapePair (i t : List Bool) : Bool → List Bool
  | false => i
  | true => t

@[simp] private lemma updI (i t v : List Bool) :
    Function.update (tapePair i t) false v = tapePair v t := by funext k; cases k <;> rfl
@[simp] private lemma updT (i t v : List Bool) :
    Function.update (tapePair i t) true v = tapePair i v := by funext k; cases k <;> rfl
@[simp] private lemma getI (i t : List Bool) : tapePair i t false = i := rfl
@[simp] private lemma getT (i t : List Bool) : tapePair i t true = t := rfl

private abbrev Stmt := TM2.Stmt (fun _ : Bool => Bool) Bool Bool
private def jump (l : Bool) : Stmt := .load (fun _ => false) (.goto (fun _ => l))

private def prog : Bool → Stmt
  | false => .pop false (fun _ b => b.getD false)
      (.branch id
        (.pop false (fun r _ => r) (.push true (fun _ => true) (jump false)))
        (.push false (fun _ => false) (.push false (fun _ => true)
          (.push false (fun _ => true) (jump true)))))
  | true => .pop true (fun _ b => b.getD false)
      (.branch id (.push false (fun _ => false) (.push false (fun _ => true) (jump true)))
        (.load (fun _ => false) .halt))

private def machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ _ := Bool
  Λ := Bool
  main := false
  σ := Bool
  initialState := false
  m := prog

private abbrev Config := TM2.Cfg (fun _ : Bool => Bool) Bool Bool
private def cfg (l : Option Bool) (i t : List Bool) : Config := ⟨l,false,tapePair i t⟩
private def Runs (a b : Config) (n : ℕ) :=
  (fun o : Option Config => o.bind (TM2.step prog))^[n] (some a) = some b

private lemma step {a b c : Config} {n : ℕ} (h : TM2.step prog a = some b) (h' : Runs b c n) :
    Runs a c (n+1) := by
  unfold Runs at *
  rw [Function.iterate_succ_apply]
  simpa only [Option.bind_some,h] using h'

private lemma scan (w rest : List Bool) (t : ℕ) :
    Runs (cfg (some false) (delimit w ++ rest) (List.replicate t true))
      (cfg (some true) (delimit [true] ++ rest) (List.replicate (w.length+t) true)) (w.length+1) := by
  induction w generalizing t with
  | nil =>
    simp only [List.length_nil,zero_add]
    apply step _ (show Runs _ _ 0 from rfl)
    simp [cfg,prog,jump,delimit]
  | cons b w ih =>
    have h := ih (t+1)
    have heq : w.length + 1 + t = w.length + (t+1) := by omega
    simp only [List.length_cons, heq]
    apply step _ h
    simp [cfg,prog,jump,delimit,List.replicate_succ]

private lemma writeZeros (k : ℕ) (w rest : List Bool) :
    Runs (cfg (some true) (delimit w ++ rest) (List.replicate k true))
      (cfg none (delimit (List.replicate k false ++ w) ++ rest) []) (k+1) := by
  induction k generalizing w with
  | zero =>
    apply step _ (show Runs _ _ 0 from rfl)
    simp [cfg,prog]
  | succ k ih =>
    have heq : List.replicate (k+1) false ++ w = List.replicate k false ++ false :: w := by
      rw [List.replicate_succ',List.append_assoc]; rfl
    rw [heq]
    apply step _ (ih (false :: w))
    simp [cfg,prog,jump,delimit,List.replicate_succ]

private lemma encode_bits (n : ℕ) : encodeNat n = n.bits := by
  have pos (p : PosNum) : encodePosNum p = (p : ℕ).bits := by
    induction p with
    | one => rfl
    | bit0 p ih => simp [encodePosNum, PosNum.cast_bit0, ← two_mul, ih, (PosNum.to_nat_pos p).ne']
    | bit1 p ih => simp [encodePosNum, PosNum.cast_bit1, ← two_mul, ih]
  have num (p : Num) : encodeNum p = (p : ℕ).bits := by
    cases p with
    | zero => rfl
    | pos p => exact pos p
  simpa [encodeNat] using num (n : Num)

private lemma encode_power (k : ℕ) : encodeNat (2^k) = List.replicate k false ++ [true] := by
  rw [encode_bits]
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Nat.bit0_bits _ (by positivity), ih, List.replicate_succ]; rfl

end PadMachine

open PadMachine Turing Computability ComplexityTheory BitstringEncoding in
theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1.H3 := by
  refine ⟨{ tm := machine, inputAlphabet := Equiv.refl _, outputAlphabet := Equiv.refl _,
            time := Polynomial.X + Polynomial.C 2, outputsFun := ?_ }⟩
  rintro ⟨n,tail⟩
  let w := encodeNat n
  let rest := bitEncode tail
  let word := delimit w ++ rest
  let result := delimit (encodeNat (2^n.size)) ++ rest
  let steps := (w.length+1)+(w.length+1)
  refine ⟨⟨steps,?_⟩,?_⟩
  · have input : initList machine word = cfg (some false) word [] := by
      unfold initList cfg
      apply congrArg (fun st => (⟨some false,false,st⟩ : Config))
      funext k; cases k <;> rfl
    have output : haltList machine result = cfg none result [] := by
      unfold haltList cfg
      apply congrArg (fun st => (⟨none,false,st⟩ : Config))
      funext k; cases k <;> rfl
    change (fun o : Option Config => o.bind (TM2.step prog))^[steps]
      (some (initList machine (word.map id))) = some (haltList machine (result.map id))
    let run (v : Config) := (fun o : Option Config => o.bind (TM2.step prog))^[steps] (some v)
    have startEq := (congrArg (fun w : List Bool => initList machine w) (List.map_id word)).trans input
    have endEq := (congrArg (fun w : List Bool => haltList machine w) (List.map_id result)).trans output
    refine (congrArg run startEq).trans (Eq.trans ?_ (congrArg some endEq.symm))
    dsimp only [run]
    have h₁ := scan w rest 0
    have h₂ := writeZeros w.length [true] rest
    have hl : w.length = n.size := by rw [show w = n.bits from encode_bits n,Nat.size_eq_bits_len]
    simp only [List.replicate_zero, Nat.add_zero] at h₁
    unfold Runs at h₁ h₂
    dsimp only [steps,result,word]
    rw [Function.iterate_add_apply,h₁,encode_power,← hl]
    exact h₂
  · change steps ≤ Polynomial.eval word.length (Polynomial.X + Polynomial.C 2)
    simp [steps,word,BitstringEncoding.length_delimit]
    omega
