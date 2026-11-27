import FormalConjectures.ErdosProblems.«78»

/-! # A finite base graph and its hexadecimal lexicographic powers (Erdős Problem 78)
Combined from the merged reduction and step proofs:
- reductions/Erdos78.erdos_78.variants.little_o_sqrt.R1.lean
- proofs/Erdos78.erdos_78.variants.little_o_sqrt.R1.H1.lean
- proofs/Erdos78.erdos_78.variants.little_o_sqrt.R1.H2.lean
- proofs/Erdos78.erdos_78.variants.little_o_sqrt.R1.H3.lean
-/

-- Credit: @steveDOTdigital
namespace OMA.Erdos78R1
open Erdos78 Filter ComplexityTheory
open scoped Asymptotics

-- The first unequal hexadecimal digits decide adjacency using quadratic residues modulo 17.
private def H1 : Prop := ∃ color : ℕ → ℕ → Bool,
    IsPolyTime (fun p : List Bool × ℕ × ℕ => color p.2.1 p.2.2) ∧
    ∀ u v : ℕ, color u v =
      (if u = v then false else if u%16 = v%16 then color (u/16) (v/16)
       else decide (((u%16+17-v%16)%17) ∈ ([1,2,4,8,9,13,15,16] : List ℕ)))

-- In each digit, a homogeneous set occupies at most three of the sixteen classes.
private def H2 : Prop := ∀ color : ℕ → ℕ → Bool,
    (∀ u v : ℕ, color u v =
      (if u = v then false else if u%16 = v%16 then color (u/16) (v/16)
       else decide (((u%16+17-v%16)%17) ∈ ([1,2,4,8,9,13,15,16] : List ℕ)))) →
    ∀ d n : ℕ, n ≤ 16^d →
      NoHomogeneousSet (explicitGraph (fun p => color p.2.1 p.2.2) n) (3^d+1)

-- The digit bound grows strictly more slowly than the square root of the graph order.
private def H3 : Prop := ∃ f : ℕ → ℝ, f =o[atTop] (fun n ↦ Real.sqrt (n : ℝ)) ∧
    ∀ᶠ n : ℕ in atTop, ∃ d : ℕ, n ≤ 16^d ∧ 3^d+1 ≤ ⌈f n⌉₊

private theorem main : H1 → H2 → H3 → type_of% @Erdos78.erdos_78.variants.little_o_sqrt := by
  rintro ⟨color,poly,rule⟩ powers ⟨f,limit,eventually⟩
  refine ⟨f,limit,(fun p => color p.2.1 p.2.2),poly,?_⟩
  filter_upwards [eventually] with n hn
  obtain ⟨d,nd,fd⟩ := hn
  obtain ⟨cl,ind⟩ := powers color rule d n nd
  exact ⟨cl.mono fd,ind.mono fd⟩

end OMA.Erdos78R1

/- # A polynomial-time machine reading paired binary words -/
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

private theorem h1_proof : OMA.Erdos78R1.H1 := by
  refine ⟨OMA.HexMachine.oracle,OMA.HexMachine.oracle_poly,?_⟩
  intro u v
  rw [OMA.HexMachine.oracle]
  by_cases eq : u = v <;> simp [eq,OMA.HexMachine.digit]

/- # Homogeneous sets in hexadecimal graph powers -/
-- Credit: @steveDOTdigital
namespace OMA.HexPowers
open Finset Erdos78

private def digit (a b : ℕ) : Bool :=
  decide (((a+17-b)%17) ∈ ([1,2,4,8,9,13,15,16] : List ℕ))

private lemma symmetric_digit : ∀ a b : Fin 16, digit a b = digit b a := by decide

-- Four increasing digits cannot have all six edges the same color.
private def fourOK (a b c d : Fin 16) : Prop :=
  a < b → b < c → c < d →
    ¬ (digit a c = digit a b ∧ digit a d = digit a b ∧ digit b c = digit a b ∧
       digit b d = digit a b ∧ digit c d = digit a b)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1400000 in
private lemma four : ∀ a b c d, fourOK a b c d := by
  intro a
  fin_cases a <;> unfold fourOK <;> decide

private lemma digit_bound (s : Finset ℕ) (small : ∀ x ∈ s, x < 16) (b : Bool)
    (h : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → digit u v = b) : s.card ≤ 3 := by
  by_contra! big
  obtain ⟨T,sub,size⟩ := exists_subset_card_eq (show 4 ≤ s.card by omega)
  let e : Fin 4 ↪o ℕ := T.orderEmbOfFin size
  have mem (i : Fin 4) : e i ∈ s := sub (T.orderEmbOfFin_mem size i)
  let p (i : Fin 4) : Fin 16 := ⟨e i,small _ (mem i)⟩
  have inc {i j : Fin 4} (lt : i < j) : p i < p j := e.strictMono lt
  have col {i j : Fin 4} (ne : i ≠ j) : digit (p i) (p j) = b :=
    h _ (mem i) _ (mem j) (e.injective.ne ne)
  have no := four (p 0) (p 1) (p 2) (p 3)
    (inc (by decide)) (inc (by decide)) (inc (by decide))
  exact no ⟨(col (by decide)).trans (col (by decide)).symm,
    (col (by decide)).trans (col (by decide)).symm,(col (by decide)).trans (col (by decide)).symm,
    (col (by decide)).trans (col (by decide)).symm,(col (by decide)).trans (col (by decide)).symm⟩

private def Rule (color : ℕ → ℕ → Bool) : Prop := ∀ u v : ℕ, color u v =
  (if u = v then false else if u%16 = v%16 then color (u/16) (v/16) else digit (u%16) (v%16))

private lemma symmetric {color : ℕ → ℕ → Bool} (rule : Rule color) (u v : ℕ) :
    color u v = color v u := by
  by_cases eq : u = v
  · subst v; rfl
  by_cases rem : u%16 = v%16
  · rw [rule u v,rule v u,if_neg eq,if_neg (Ne.symm eq),if_pos rem,if_pos rem.symm]
    exact symmetric rule (u/16) (v/16)
  · rw [rule u v,rule v u,if_neg eq,if_neg (Ne.symm eq),if_neg rem,if_neg (Ne.symm rem)]
    exact symmetric_digit ⟨_,Nat.mod_lt _ (by decide)⟩ ⟨_,Nat.mod_lt _ (by decide)⟩
termination_by u+v
decreasing_by omega

private lemma power_bound {color : ℕ → ℕ → Bool} (rule : Rule color) (d : ℕ) (s : Finset ℕ)
    (small : ∀ x ∈ s, x < 16^d) (b : Bool) (mono : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → color x y = b) :
    s.card ≤ 3^d := by
  classical
  induction d generalizing s with
  | zero =>
    have sub : s ⊆ {0} := by
      intro x hx
      have := small x hx
      have eq : x = 0 := by simpa using this
      simp [eq]
    simpa using card_le_card sub
  | succ d ih =>
    let R := s.image (fun x => x%16)
    have digits : R.card ≤ 3 := by
      apply digit_bound R (by rintro x hx; obtain ⟨v,_,rfl⟩ := mem_image.mp hx; omega) b
      intro i hi j hj ne
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hi
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hj
      have xy : x ≠ y := by rintro rfl; exact ne rfl
      have h := mono x hx y hy xy
      simpa only [rule x y,if_neg xy,if_neg ne] using h
    have each (r : ℕ) (_ : r ∈ R) : (s.filter (fun x => x%16=r)).card ≤ 3^d := by
      let T := s.filter fun x => x%16=r
      let Q := T.image fun x => x/16
      have inj : Set.InjOn (fun x : ℕ => x/16) (T : Set ℕ) := by
        intro x hx y hy eq
        have rx := (mem_filter.mp hx).2
        have ry := (mem_filter.mp hy).2
        change x/16 = y/16 at eq
        change x%16 = r at rx
        change y%16 = r at ry
        omega
      have card : Q.card = T.card := card_image_of_injOn inj
      change T.card ≤ _
      rw [←card]
      apply ih Q
      · intro q hq
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hq
        have lt := small x (mem_filter.mp hx).1
        rw [pow_succ] at lt
        exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 16)).mpr lt
      · intro q hq p hp ne
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hq
        obtain ⟨y,hy,rfl⟩ := mem_image.mp hp
        have xy : x ≠ y := by rintro rfl; exact ne rfl
        have rem := (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
        have h := mono x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 xy
        simpa only [rule x y,if_neg xy,if_pos rem] using h
    calc
      s.card = ∑ r ∈ R, (s.filter fun x => x%16=r).card :=
        card_eq_sum_card_fiberwise (f := fun x : ℕ => x%16) (fun x hx => mem_image_of_mem _ hx)
      _ ≤ ∑ _r ∈ R, 3^d := sum_le_sum each
      _ ≤ 3^(d+1) := by simpa [pow_succ,mul_comm] using Nat.mul_le_mul_right (3^d) digits

private lemma fin_bound {color : ℕ → ℕ → Bool} (rule : Rule color) (d n : ℕ) (hn : n ≤ 16^d)
    (s : Finset (Fin n)) (b : Bool)
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → color x.val y.val = b) : s.card ≤ 3^d := by
  let S := s.map Fin.valEmbedding
  have cap (i : ℕ) (hi : i ∈ S) : i < 16^d := by
    obtain ⟨x,_,rfl⟩ := mem_map.mp hi
    exact x.isLt.trans_le hn
  have homo : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → color i j = b := by
    intro i hi j hj ne
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hi
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hj
    exact h x hx y hy (by rintro rfl; exact ne rfl)
  simpa [S] using power_bound rule d S cap b homo

theorem powers (color : ℕ → ℕ → Bool) (rule : Rule color) (d n : ℕ) (hn : n ≤ 16^d) :
    NoHomogeneousSet (explicitGraph (fun p => color p.2.1 p.2.2) n) (3^d+1) := by
  let G := explicitGraph (fun p => color p.2.1 p.2.2) n
  have adj {x y : Fin n} (ne : x ≠ y) : G.Adj x y ↔ color x.val y.val = true := by
    change (x ≠ y ∧ (color x.val y.val = true ∨ color y.val x.val = true)) ↔ _
    rw [symmetric rule y.val x.val]
    simp [ne]
  constructor
  · intro s cl
    have h := fin_bound rule d n hn s true (fun x hx y hy ne => (adj ne).mp (cl.isClique hx hy ne))
    have card := cl.card_eq
    omega
  · intro s cl
    have h := fin_bound rule d n hn s false (by
      intro x hx y hy ne
      have a := (cl.isClique hx hy ne).2
      cases bit : color x.val y.val <;> first | rfl | exact False.elim (a ((adj ne).mpr bit)))
    have card := cl.card_eq
    omega

end OMA.HexPowers

/- # Logarithmic digit depth and the homogeneous-set bound -/
-- Credit: @steveDOTdigital
namespace OMA.HexDepth
open Filter Asymptotics
open scoped Topology

theorem bound : ∃ f : ℕ → ℝ, f =o[atTop] (fun n ↦ Real.sqrt (n : ℝ)) ∧
    ∀ᶠ n : ℕ in atTop, ∃ d : ℕ, n ≤ 16^d ∧ 3^d+1 ≤ ⌈f n⌉₊ := by
  let L := Nat.log 16
  let f (n : ℕ) : ℝ := 4 * 3^(L n)
  refine ⟨f,?_,?_⟩
  · have logtop : Tendsto L atTop atTop := by
      refine tendsto_atTop.2 fun b => ?_
      filter_upwards [eventually_ge_atTop (16^b)] with n hn
      exact Nat.le_log_of_pow_le (by decide) hn
    have lim : Tendsto (fun n : ℕ => 4*((3/4:ℝ)^(L n))) atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (3/4:ℝ)) (by norm_num)).comp logtop).const_mul 4
    apply isLittleO_of_tendsto'
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact fun h => False.elim ((Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))).ne' h)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds lim
    · filter_upwards with n
      change 0 ≤ f n / Real.sqrt n
      dsimp [f]
      positivity
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have power : (16:ℝ)^(L n) ≤ n := by exact_mod_cast Nat.pow_log_le_self 16 (by omega : n ≠ 0)
      have square : ((4:ℝ)^(L n))^2 ≤ n := by
        rw [pow_two,← mul_pow]
        norm_num at *
        exact power
      have root := Real.sq_sqrt (Nat.cast_nonneg n : 0 ≤ (n:ℝ))
      have lb : (4:ℝ)^(L n) ≤ Real.sqrt n := by
        nlinarith [Real.sqrt_nonneg (n:ℝ), show 0 ≤ (4:ℝ)^(L n) by positivity]
      change f n / Real.sqrt n ≤ _
      calc
        _ ≤ f n / 4^(L n) := div_le_div_of_nonneg_left (by dsimp [f]; positivity) (by positivity) lb
        _ = _ := by rw [div_pow]; dsimp [f]; ring
  · filter_upwards with n
    refine ⟨L n+1,(Nat.lt_pow_succ_log_self (by decide : 1 < 16) n).le,?_⟩
    have exactF : f n = ((4*3^(L n) : ℕ) : ℝ) := by simp [f]
    rw [exactF,Nat.ceil_natCast,pow_succ]
    have : 0 < 3^(L n) := by positivity
    omega
end OMA.HexDepth

theorem OMA.solution : type_of% @Erdos78.erdos_78.variants.little_o_sqrt :=
  OMA.Erdos78R1.main h1_proof OMA.HexPowers.powers OMA.HexDepth.bound
