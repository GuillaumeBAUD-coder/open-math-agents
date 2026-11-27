import OMAReductions.R_Erdos78_erdos_78_variants_little_o_sqrt_R1

/-! # A polynomial-time machine reading paired binary words -/
-- Credit: @steveDOTdigital
namespace OMA.HexMachine
open Turing Computability ComplexityTheory StateTransition

private inductive Tape | input | temp | buffer deriving DecidableEq
private instance : Fintype Tape := ⟨{.input,.temp,.buffer},by intro k; cases k <;> simp⟩
private inductive Label | skip | copy | reverse | scan deriving DecidableEq
private instance : Fintype Label := ⟨{.skip,.copy,.reverse,.scan},by intro k; cases k <;> simp⟩
private abbrev Reg (S : Type) := Option Bool × Option Bool × S

private def blank {S : Type} (s : S) : Reg S := (none,none,s)
private def tapeLists (i t b : List Bool) : Tape → List Bool
  | .input => i
  | .temp => t
  | .buffer => b

@[simp] private lemma getI (i t b : List Bool) : tapeLists i t b .input = i := rfl
@[simp] private lemma getT (i t b : List Bool) : tapeLists i t b .temp = t := rfl
@[simp] private lemma getB (i t b : List Bool) : tapeLists i t b .buffer = b := rfl
@[simp] private lemma updI (i t b v : List Bool) :
    Function.update (tapeLists i t b) .input v = tapeLists v t b := by funext k; cases k <;> rfl
@[simp] private lemma updT (i t b v : List Bool) :
    Function.update (tapeLists i t b) .temp v = tapeLists i v b := by funext k; cases k <;> rfl
@[simp] private lemma updB (i t b v : List Bool) :
    Function.update (tapeLists i t b) .buffer v = tapeLists i t v := by funext k; cases k <;> rfl

private abbrev Statement (S : Type) := TM2.Stmt (fun _ : Tape => Bool) Label (Reg S)
private def jump {S : Type} (l : Label) : Statement S :=
  .load (fun v => blank v.2.2) (.goto (fun _ => l))

-- Skip the first delimited word, copy the second in reverse, restore its
-- original order, then scan it alongside the final undelimited word.
private def program {S : Type} (init : S) (tick : S → Bool → Bool → S)
    (finish : S → Bool) : Label → Statement S
  | .skip => .pop .input (fun v b => (b,none,v.2.2))
      (.branch (fun v => v.1.getD false)
        (.pop .input (fun v _ => v) (jump .skip)) (jump .copy))
  | .copy => .pop .input (fun v b => (b,none,v.2.2))
      (.branch (fun v => v.1.getD false)
        (.pop .input (fun v b => (b,none,v.2.2))
          (.push .temp (fun v => v.1.getD false) (jump .copy))) (jump .reverse))
  | .reverse => .pop .temp (fun v b => (b,none,v.2.2))
      (.branch (fun v => v.1.isSome)
        (.push .buffer (fun v => v.1.getD false) (jump .reverse)) (jump .scan))
  | .scan => .pop .buffer (fun v b => (b,none,v.2.2))
      (.pop .input (fun v b => (v.1,b,v.2.2))
        (.branch (fun v => v.1.isSome || v.2.1.isSome)
          (.load (fun v => blank (tick v.2.2 (v.1.getD false) (v.2.1.getD false))) (.goto (fun _ => .scan)))
          (.push .input (fun v => finish v.2.2) (.load (fun _ => blank init) .halt))))

private def machine {S : Type} [Fintype S] (init : S) (tick : S → Bool → Bool → S)
    (finish : S → Bool) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .input
  Γ _ := Bool
  Λ := Label
  main := .skip
  σ := Reg S
  initialState := blank init
  m := program init tick finish

private abbrev Config (S : Type) := TM2.Cfg (fun _ : Tape => Bool) Label (Reg S)
private def cfg {S : Type} (l : Option Label) (s : S) (i t b : List Bool) : Config S :=
  ⟨l,blank s,tapeLists i t b⟩

private def Runs {S : Type} (p : Label → Statement S) (a b : Config S) (n : ℕ) : Prop :=
  (fun v : Option (Config S) => v.bind (TM2.step p))^[n] (some a) = some b

private lemma next {S : Type} {p : Label → Statement S} {a b c : Config S} {n : ℕ}
    (one : TM2.step p a = some b) (h : Runs p b c n) : Runs p a c (n+1) := by
  unfold Runs at *
  rw [Function.iterate_succ_apply]
  simpa only [Option.bind_some,one] using h

private lemma once {S : Type} {p : Label → Statement S} {a b : Config S}
    (one : TM2.step p a = some b) : Runs p a b 1 := next one (show Runs p b b 0 from rfl)

private lemma chain {S : Type} {p : Label → Statement S} {a b c : Config S} {n m : ℕ}
    (h : Runs p a b n) (h' : Runs p b c m) : Runs p a c (m+n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply,h,h']

section
variable {S : Type} (init : S) (tick : S → Bool → Bool → S) (finish : S → Bool)


private lemma skip_word (s : S) (w rest : List Bool) :
    Runs (program init tick finish) (cfg (some .skip) s (BitstringEncoding.delimit w ++ rest) [] [])
      (cfg (some .copy) s rest [] []) (w.length+1) := by
  induction w with
  | nil => apply once; simp [cfg,program,jump,blank,BitstringEncoding.delimit]
  | cons b bs ih =>
    apply next _ ih
    simp [cfg,program,jump,blank,BitstringEncoding.delimit]

private lemma copy_word (s : S) (w rest buf : List Bool) :
    Runs (program init tick finish) (cfg (some .copy) s (BitstringEncoding.delimit w ++ rest) buf [])
      (cfg (some .reverse) s rest (w.reverse ++ buf) []) (w.length+1) := by
  induction w generalizing buf with
  | nil => apply once; simp [cfg,program,jump,blank,BitstringEncoding.delimit]
  | cons b bs ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
      (next (a := cfg (some .copy) s (BitstringEncoding.delimit (b::bs) ++ rest) buf [])
        (by simp [cfg,program,jump,blank,BitstringEncoding.delimit]) (ih (b::buf)))

private lemma reverse_word (s : S) (w rest buf : List Bool) :
    Runs (program init tick finish) (cfg (some .reverse) s rest w buf)
      (cfg (some .scan) s rest [] (w.reverse ++ buf)) (w.length+1) := by
  induction w generalizing buf with
  | nil => apply once; simp [cfg,program,jump,blank]
  | cons b bs ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
      (next (a := cfg (some .reverse) s rest (b::bs) buf)
        (by simp [cfg,program,jump,blank]) (ih (b::buf)))
end

-- Missing high bits are zero. The finite control processes one bit from each word per step.
private def runBits {S : Type} (tick : S → Bool → Bool → S) (s : S)
    (x y : List Bool) : S :=
  match x,y with
  | [],[] => s
  | a::as,[] => runBits tick (tick s a false) as []
  | [],b::bs => runBits tick (tick s false b) [] bs
  | a::as,b::bs => runBits tick (tick s a b) as bs
termination_by x.length+y.length

private lemma scan_words {S : Type} (init : S) (tick : S → Bool → Bool → S) (finish : S → Bool)
    (s : S) (x y : List Bool) :
    Runs (program init tick finish) (cfg (some .scan) s y [] x)
      (cfg none init [finish (runBits tick s x y)] [] []) (max x.length y.length+1) := by
  cases x with
  | nil =>
    cases y with
    | nil =>
      apply once
      simp [cfg,program,blank,runBits]
    | cons b bs =>
      simpa [runBits] using (next (a := cfg (some .scan) s (b::bs) [] [])
        (by simp [cfg,program,blank]) (scan_words init tick finish (tick s false b) [] bs))
  | cons a as =>
    cases y with
    | nil =>
      simpa [runBits] using (next (a := cfg (some .scan) s [] [] (a::as))
        (by simp [cfg,program,blank]) (scan_words init tick finish (tick s a false) as []))
    | cons b bs =>
      simpa [runBits,Nat.succ_max_succ] using (next (a := cfg (some .scan) s (b::bs) [] (a::as))
        (by simp [cfg,program,blank]) (scan_words init tick finish (tick s a b) as bs))
termination_by x.length + y.length

private lemma parser {S : Type} (init : S) (tick : S → Bool → Bool → S) (finish : S → Bool)
    (w x y : List Bool) :
    Runs (program init tick finish)
      (cfg (some .skip) init (BitstringEncoding.delimit w ++ (BitstringEncoding.delimit x ++ y)) [] [])
      (cfg none init [finish (runBits tick init x y)] [] [])
      ((max x.length y.length+1)+((x.length+1)+((x.length+1)+(w.length+1)))) := by
  have skip := skip_word init tick finish init w (BitstringEncoding.delimit x ++ y)
  have copy := copy_word init tick finish init x y []
  have rev := reverse_word init tick finish init x.reverse y []
  have scan := scan_words init tick finish init x y
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at copy rev
  exact chain (chain (chain skip copy) rev) scan

private theorem poly_scan {S : Type} [Fintype S] (s₀ : S) (tick : S → Bool → Bool → S)
    (finish : S → Bool) :
    IsPolyTime (fun p : List Bool × ℕ × ℕ => finish (runBits tick s₀
      (Computability.encodeNat p.2.1) (Computability.encodeNat p.2.2))) := by
  let tm := machine s₀ tick finish
  refine ⟨{
    tm := tm
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 4 * Polynomial.X + Polynomial.C 4
    outputsFun := ?_ }⟩
  rintro ⟨w,a,b⟩
  let x := Computability.encodeNat a
  let y := Computability.encodeNat b
  let u := BitstringEncoding.bitEncode w
  let word := BitstringEncoding.delimit u ++ (BitstringEncoding.delimit x ++ y)
  let result := finish (runBits tick s₀ x y)
  let steps := (max x.length y.length+1)+((x.length+1)+((x.length+1)+(u.length+1)))
  refine ⟨⟨steps,?_⟩,?_⟩
  · have input : initList tm word = cfg (some .skip) s₀ word [] [] := by
      unfold initList cfg
      apply congrArg (fun st => (⟨some Label.skip,blank s₀,st⟩ : Config S))
      funext k
      cases k <;> rfl
    have output : haltList tm [result] = cfg none s₀ [result] [] [] := by
      unfold haltList cfg
      apply congrArg (fun st => (⟨none,blank s₀,st⟩ : Config S))
      funext k
      cases k <;> rfl
    change (fun o : Option (Config S) => o.bind (TM2.step (program s₀ tick finish)))^[steps]
      (some (initList tm (List.map (id : Bool → Bool) word))) = some (haltList tm [result])
    have startEq : initList tm (List.map (id : Bool → Bool) word) = cfg (some .skip) s₀ word [] [] :=
      (congrArg (fun w : List Bool => initList tm w) (List.map_id word)).trans input
    let iterateFrom (c : Config S) := (fun o : Option (Config S) =>
      o.bind (TM2.step (program s₀ tick finish)))^[steps] (some c)
    have run : iterateFrom (cfg (some .skip) s₀ word [] []) = some (cfg none s₀ [result] [] []) :=
      parser s₀ tick finish u x y
    exact (congrArg iterateFrom startEq).trans (run.trans (congrArg some output.symm))
  · change steps ≤ Polynomial.eval word.length (Polynomial.C 4 * Polynomial.X + Polynomial.C 4)
    simp [steps,word,BitstringEncoding.length_delimit]
    omega

-- The finite control remembers up to three bit pairs. A different pair of
-- complete hexadecimal digits determines the answer permanently.
private inductive Phase
  | fresh
  | one (a b : Bool)
  | two (a b c d : Bool)
  | three (a b c d e f : Bool)
  | done (answer : Bool)
  deriving DecidableEq

private def phaseCode : Phase → Fin 5 × (Bool × Bool × Bool × Bool × Bool × Bool)
  | .fresh => (0,false,false,false,false,false,false)
  | .one a b => (1,a,b,false,false,false,false)
  | .two a b c d => (2,a,b,c,d,false,false)
  | .three a b c d e f => (3,a,b,c,d,e,f)
  | .done a => (4,a,false,false,false,false,false)

private noncomputable instance : Fintype Phase :=
  Fintype.ofInjective phaseCode (by rintro x y eq; cases x <;> cases y <;> simp_all [phaseCode])

private def value : List Bool → ℕ
  | [] => 0
  | bit::bs => bit.toNat + 2 * value bs

private def nib (a b c d : Bool) := a.toNat+2*b.toNat+4*c.toNat+8*d.toNat
private def digit (x y : ℕ) : Bool :=
  decide (((x+17-y)%17) ∈ ([1,2,4,8,9,13,15,16] : List ℕ))

private lemma digit_self (x : ℕ) : digit x x = false := by
  simp [digit]

private def tick : Phase → Bool → Bool → Phase
  | .fresh,a,b => .one a b
  | .one a b,c,d => .two a b c d
  | .two a b c d,e,f => .three a b c d e f
  | .three a b c d e f,g,h =>
    if nib a c e g = nib b d f h then .fresh else .done (digit (nib a c e g) (nib b d f h))
  | .done b,_,_ => .done b

private def finish : Phase → Bool
  | .fresh => false
  | .one a b => digit (nib a false false false) (nib b false false false)
  | .two a b c d => digit (nib a c false false) (nib b d false false)
  | .three a b c d e f => digit (nib a c e false) (nib b d f false)
  | .done b => b

private def hd (l : List Bool) := l.head?.getD false
private def low (l : List Bool) := nib (hd l) (hd l.tail) (hd l.tail.tail) (hd l.tail.tail.tail)
private def rest (l : List Bool) := l.tail.tail.tail.tail

private lemma value_step (l : List Bool) : value l = (hd l).toNat + 2*value l.tail := by
  cases l <;> rfl

private lemma value_decomp (l : List Bool) : value l = low l + 16*value (rest l) := by
  dsimp [low,nib,rest]
  linarith only [value_step l,value_step l.tail,value_step l.tail.tail,value_step l.tail.tail.tail]

private lemma low_lt (l : List Bool) : low l < 16 := by
  unfold low nib
  cases hd l <;> cases hd l.tail <;> cases hd l.tail.tail <;> cases hd l.tail.tail.tail <;> decide

private lemma zeros (s : Phase) : finish (tick s false false) = finish s := by
  cases s with
  | fresh => exact digit_self _
  | one a b => rfl
  | two a b c d => rfl
  | three a b c d e f =>
    change finish (if nib a c e false = nib b d f false then .fresh else .done _) = _
    split
    next h => simp [finish,h,digit_self]
    next => rfl
  | done b => rfl

private def evaluate (s : Phase) (x y : List Bool) := finish (runBits tick s x y)

private lemma advance (s : Phase) (x y : List Bool) :
    evaluate s x y = evaluate (tick s (hd x) (hd y)) x.tail y.tail := by
  cases x <;> cases y <;> simp [evaluate,runBits,hd,zeros]

private lemma frozen (b : Bool) (x y : List Bool) : evaluate (.done b) x y = b := by
  cases x with
  | nil =>
    cases y with
    | nil => simp [evaluate,runBits,finish]
    | cons y ys => rw [advance]; exact frozen b [] ys
  | cons x xs =>
    cases y with
    | nil => rw [advance]; exact frozen b xs []
    | cons y ys => rw [advance]; exact frozen b xs ys
termination_by x.length+y.length

private lemma four_bits (x y : List Bool) :
    evaluate .fresh x y =
      (if low x = low y then evaluate .fresh (rest x) (rest y) else digit (low x) (low y)) := by
  calc
    _ = evaluate (tick .fresh (hd x) (hd y)) x.tail y.tail := advance _ _ _
    _ = evaluate (tick _ (hd x.tail) (hd y.tail)) x.tail.tail y.tail.tail := advance _ _ _
    _ = evaluate (tick _ (hd x.tail.tail) (hd y.tail.tail)) x.tail.tail.tail y.tail.tail.tail := advance _ _ _
    _ = evaluate (tick _ (hd x.tail.tail.tail) (hd y.tail.tail.tail)) (rest x) (rest y) := advance _ _ _
    _ = _ := by
      change evaluate (if low x = low y then .fresh else .done (digit (low x) (low y))) _ _ = _
      split <;> simp_all [frozen]

private def oracle (u v : ℕ) : Bool :=
  if eq : u = v then false else if u%16 = v%16 then oracle (u/16) (v/16) else digit (u%16) (v%16)
termination_by u+v
decreasing_by omega

private lemma oracle_self (u : ℕ) : oracle u u = false := by rw [oracle]; simp

private lemma correct (x y : List Bool) : evaluate .fresh x y = oracle (value x) (value y) := by
  by_cases both : x = [] ∧ y = []
  · obtain ⟨rfl,rfl⟩ := both
    rw [oracle_self]; simp [evaluate,runBits,finish]
  have xx := value_decomp x
  have yy := value_decomp y
  have bx := low_lt x
  have by' := low_lt y
  have xm : value x % 16 = low x := by omega
  have ym : value y % 16 = low y := by omega
  have xd : value x / 16 = value (rest x) := by omega
  have yd : value y / 16 = value (rest y) := by omega
  rw [four_bits,oracle,xm,ym]
  by_cases same : value x = value y
  · have a : low x = low y := by omega
    have b : value (rest x) = value (rest y) := by omega
    rw [if_pos a,dif_pos same,correct (rest x) (rest y),b,oracle_self]
  · rw [dif_neg same]
    split
    · rw [correct (rest x) (rest y),xd,yd]
    · rfl
termination_by x.length+y.length
decreasing_by
  all_goals
    simp only [rest,List.length_tail]
    have : 0 < x.length + y.length := by
      by_contra! e
      exact both ⟨List.length_eq_zero_iff.mp (by omega),List.length_eq_zero_iff.mp (by omega)⟩
    omega

private lemma encoded_value (n : ℕ) : value (Computability.encodeNat n) = n := by
  have pos (p : PosNum) : value (Computability.encodePosNum p) = (p:ℕ) := by
    induction p with
    | one => rfl
    | bit0 p ih => simp [Computability.encodePosNum,value,ih,PosNum.cast_bit0]; omega
    | bit1 p ih => simp [Computability.encodePosNum,value,ih,PosNum.cast_bit1]; omega
  have num (p : Num) : value (Computability.encodeNum p) = (p:ℕ) := by
    cases p with
    | zero => rfl
    | pos p => exact pos p
  simpa [Computability.encodeNat] using num (n:Num)

private theorem oracle_poly :
    IsPolyTime (fun p : List Bool × ℕ × ℕ => oracle p.2.1 p.2.2) := by
  have h := poly_scan Phase.fresh tick finish
  have e : (fun p : List Bool × ℕ × ℕ => finish (runBits tick Phase.fresh
      (Computability.encodeNat p.2.1) (Computability.encodeNat p.2.2))) =
      (fun p => oracle p.2.1 p.2.2) := by
    funext p
    simpa [evaluate,encoded_value] using correct (Computability.encodeNat p.2.1) (Computability.encodeNat p.2.2)
  rwa [e] at h

end OMA.HexMachine

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_little_o_sqrt_R1.H1 := by
  refine ⟨OMA.HexMachine.oracle,OMA.HexMachine.oracle_poly,?_⟩
  intro u v
  rw [OMA.HexMachine.oracle]
  by_cases eq : u = v <;> simp [eq,OMA.HexMachine.digit]
