import FormalConjectures.Other.Rule30

/-!
Two avoidance questions for finite factors of the center column.
A positive period makes every factor in its repeating word recur with bounded gaps.
The two hypotheses therefore force isolated black bursts of length one or two,
each followed by at least eleven white cells. An eight-cell right-window
calculation synchronizes the neighboring column for every mixture of these bursts.
Two repeating adjacent columns contradict the expanding left edge.
-/
open Rule30
namespace OMA.R_Rule30_centerColumn_not_eventually_periodic_R1

private theorem tick (t : ℕ) (i : ℤ) :
    state (t+1) i = xor (state t (i-1)) (state t i || state t (i+1)) := rfl

private theorem outsideLeft (t : ℕ) (i : ℤ) (h : i < -(t : ℤ)) : state t i = false := by
  induction t generalizing i with
  | zero => simp [show i ≠ 0 by omega]
  | succ t ih =>
    rw [tick, ih (i-1) (by omega), ih i (by omega), ih (i+1) (by omega)]
    rfl

private theorem leftEdge (t : ℕ) : state t (-(t : ℤ)) = true := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [tick, outsideLeft t _ (by omega), outsideLeft t _ (by omega)]
    rw [show -(↑(t+1) : ℤ) + 1 = -(t : ℤ) by omega, ih]
    rfl

private theorem outsideRight (t : ℕ) (i : ℤ) (h : (t : ℤ) < i) : state t i = false := by
  induction t generalizing i with
  | zero => simp [show i ≠ 0 by omega]
  | succ t ih =>
    rw [tick, ih (i-1) (by omega), ih i (by omega), ih (i+1) (by omega)]
    rfl

private theorem rightEdge (t : ℕ) : state t (t : ℤ) = true := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [tick, outsideRight t (↑(t+1)) (by omega), outsideRight t (↑(t+1)+1) (by omega)]
    rw [show (↑(t+1) : ℤ) - 1 = (t : ℤ) by omega, ih]
    rfl

private theorem sideways (t : ℕ) (i : ℤ) :
    state t (i-1) = xor (state (t+1) i) (state t i || state t (i+1)) := by
  rw [tick]
  generalize state t (i-1) = a
  generalize (state t i || state t (i+1)) = b
  cases a <;> cases b <;> rfl

/-- A temporal window on two adjacent columns determines the left tip of its triangle. -/
private theorem twoColumnTip (d a b : ℕ) (i : ℤ)
    (h : ∀ j ≤ d, state (a+j) i = state (b+j) i ∧
        state (a+j) (i+1) = state (b+j) (i+1)) :
    state a (i-(d : ℤ)) = state b (i-(d : ℤ)) := by
  induction d generalizing i with
  | zero => simpa using (h 0 (by omega)).1
  | succ d ih =>
    rw [show i - (↑(d+1) : ℤ) = (i-1) - (d : ℤ) by omega]
    apply ih (i-1)
    intro j hj
    obtain ⟨h0,h1⟩ := h j (by omega)
    have hn := (h (j+1) (by omega)).1
    constructor
    · rw [sideways (a+j) i, sideways (b+j) i, h0, h1]
      simpa [Nat.add_assoc] using congrArg (fun x => xor x (state (b+j) i || state (b+j) (i+1))) hn
    · simpa using h0

/-- The observation at the right is needed only when the center is white.
The edge of row b witnesses distinct initial left tips. -/
private theorem maskedDefect (a b : ℕ) (hab : a < b)
    (hc : ∀ j ≤ b, centerColumn (a+j) = centerColumn (b+j)) :
    ∃ j < b, centerColumn (a+j) = false ∧ state (a+j) 1 ≠ state (b+j) 1 := by
  by_contra! hg
  have eqL (j : ℕ) (hj : j < b) : state (a+j) (-1) = state (b+j) (-1) := by
    have hn := hc (j+1) (by omega)
    have hh := hc j (by omega)
    change state (a+(j+1)) 0 = state (b+(j+1)) 0 at hn
    change state (a+j) 0 = state (b+j) 0 at hh
    rw [← show (0:ℤ)-1 = -1 from rfl, sideways (a+j) 0, sideways (b+j) 0]
    simp only [zero_add, Nat.add_assoc, hn]
    cases he : state (a+j) 0 with
    | false =>
      have e := hg j hj (show centerColumn (a+j) = false from he)
      simp [←hh, he, e]
    | true => simp [←hh, he]
  have key := twoColumnTip (b-1) a b (-1) (by
    intro j hj
    exact ⟨eqL j (by omega), hc j (by omega)⟩)
  rw [show (-1 : ℤ) - ↑(b-1) = -(b:ℤ) by omega,
    outsideLeft a _ (by omega), leftEdge] at key
  contradiction

/-- One step of erosion of a white interval attached to a white wall. -/
private theorem whiteStrip (t n : ℕ) (wall : state t 0 = false) :
    (∀ i : ℕ, 1 ≤ i → i ≤ n+1 → state (t+1) i = false) ↔
    (∀ i : ℕ, 1 ≤ i → i ≤ n+2 → state t i = false) := by
  constructor
  · intro h
    have grow (j : ℕ) (hj : j ≤ n+1) : state t j = false ∧ state t (↑j+1) = false := by
      induction j with
      | zero =>
        have e := h 1 (by omega) (by omega)
        rw [tick] at e
        simp [wall] at e
        exact ⟨wall, by simpa using e.1⟩
      | succ j ih =>
        have prev := ih (by omega)
        have e := h (j+1) (by omega) hj
        rw [tick] at e
        simp [prev.1, prev.2] at e
        exact ⟨by simpa using prev.2, by simpa using e⟩
    intro i hi hn
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    simpa using (grow j (by omega)).2
  · intro h i hi hn
    rw [tick]
    have hl : state t (↑i-1) = false := by
      by_cases hi1 : i = 1
      · subst i; simpa using wall
      · rw [show (↑i : ℤ)-1 = ↑(i-1) by omega]
        exact h _ (by omega) (by omega)
    rw [hl, h i hi (by omega), show (↑i : ℤ)+1 = ↑(i+1) from rfl, h (i+1) (by omega) (by omega)]
    rfl

/-- The gated neighbor remains white exactly until the nearest black pixel
on the right arrives at the wall. -/
private theorem whiteArrival (a k : ℕ) (h : ∀ j < k, centerColumn (a+j) = false) :
    state (a+k) 1 = false ↔ ∀ i : ℕ, 1 ≤ i → i ≤ k+1 → state a i = false := by
  have aux (d w t : ℕ) (hc : ∀ j < d, centerColumn (t+j) = false) :
      (∀ i : ℕ, 1 ≤ i → i ≤ w+1 → state (t+d) i = false) ↔
      (∀ i : ℕ, 1 ≤ i → i ≤ w+d+1 → state t i = false) := by
    induction d generalizing t w with
    | zero => simp
    | succ d ih =>
      have wall := hc 0 (by omega)
      have hh (j : ℕ) (hj : j < d) : centerColumn (t+1+j) = false := by
        rw [show t+1+j = t+(j+1) by omega]
        exact hc _ (by omega)
      rw [show t+(d+1) = t+1+d by omega, ih w (t+1) hh,
        whiteStrip t (w+d) (by simpa only [centerColumn, Nat.add_zero] using wall)]
      simp only [Nat.add_assoc]
  have e := aux k 0 a h
  simp only [Nat.zero_add] at e
  constructor
  · intro hw
    apply e.mp
    intro i hl hu
    have hi : i = 1 := by omega
    simpa only [hi, Nat.cast_one] using hw
  · intro hw
    exact (e.mpr hw) 1 (by omega) (by omega)

/-- No constant tail. For a white wall, the advancing right edge supplies
a black neighbor in finite time, and it stays black thereafter. -/
private theorem noConstant (N : ℕ) (v : Bool) (hc : ∀ t ≥ N, centerColumn t = v) : False := by
  cases v with
  | true =>
    obtain ⟨j, _, hj, _⟩ := maskedDefect N (N+1) (by omega)
      (fun j _ => (hc _ (by omega)).trans (hc _ (by omega)).symm)
    rw [hc _ (by omega)] at hj
    contradiction
  | false =>
    let a := N+1
    have hr (s : ℕ) (hs : 2*a ≤ s) : state s 1 = true := by
      by_contra! h
      have hh : state (a+(s-a)) 1 = false := by
        rw [show a+(s-a) = s by omega]
        cases e : state s 1 <;> simp_all
      have hw (j : ℕ) (_ : j < s-a) : centerColumn (a+j) = false := hc _ (by dsimp [a]; omega)
      have bad := (whiteArrival a (s-a) hw).mp hh a (by dsimp [a]; omega) (by omega)
      rw [rightEdge] at bad
      contradiction
    obtain ⟨j, _, _, hj⟩ := maskedDefect (2*a) (2*a+1) (by omega)
      (fun j _ => (hc _ (by dsimp [a]; omega)).trans (hc _ (by dsimp [a]; omega)).symm)
    exact hj ((hr _ (by omega)).trans (hr _ (by omega)).symm)

private theorem spread (P : ℕ → Prop) (N p : ℕ) (hp : 0 < p)
    (hper : ∀ t ≥ N, P (t+p) ↔ P t) (windows : ∀ L, ∃ a, ∀ j < L, P (a+j)) :
    ∀ t ≥ N, P t := by
  intro t ht
  have many (k : ℕ) : P (t+k*p) ↔ P t := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, ← Nat.add_assoc]
      exact (hper _ (by omega)).trans ih
  obtain ⟨a, ha⟩ := windows (t+p+1)
  have bit := ha (t+(p-a%p)) (by omega)
  have hd := Nat.mod_add_div a p
  have hr := Nat.mod_lt a hp
  have idx : a+(t+(p-a%p)) = t+(a/p+1)*p := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (a/p) p]; omega
  rw [idx] at bit
  exact (many _).mp bit

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem exclusionOfLocalRules (p N : ℕ) (hp : 0 < p)
    (rep : ∀ n ≥ N, centerColumn (n+p) = centerColumn n)
    (short : ∀ m ≥ N, centerColumn m = true → centerColumn (m+1) = true →
      centerColumn (m+2) = false)
    (gap : ∀ m ≥ N, centerColumn m = true → centerColumn (m+1) = false →
      ∀ k < 11, centerColumn (m+1+k) = false) : False := by
  let window (t : ℕ) : BitVec 8 :=
    BitVec.ofBoolListLE [state t 1, state t 2, state t 3, state t 4,
                          state t 5, state t 6, state t 7, state t 8]

  let tick8 (x : BitVec 8) (b e : Bool) : BitVec 8 :=
    x.shiftConcat b ^^^ (x ||| (x >>> 1) ||| (if e then 128 else 0))

  have windowStep (t : ℕ) :
      window (t+1) = tick8 (window t) (centerColumn t) (state t 9) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> cases he : state t 9 <;>
      simp [window, tick8, centerColumn, BitVec.getLsbD_shiftConcat, state_succ, step,
        -BitVec.getLsbD_eq_getElem, List.getD, he]

  have bit0 (t : ℕ) : (window t).getLsbD 0 = state t 1 := by
    simp [window, -BitVec.getLsbD_eq_getElem, List.getD]

  let Fits (m : Nat) (x : BitVec 8) : Prop := m.testBit x.toNat = true

  let Moves (m : Nat) (b : Bool) (n : Nat) : Prop :=
    ∀ i : Fin 256, ∀ e : Bool, Fits m (BitVec.ofFin i) →
      Fits n (tick8 (BitVec.ofFin i) b e)

  let nextPhase (q : Fin 23) (b : Bool) : Fin 23 :=
    if b then (if q = 0 then 1 else 12)
    else if q = 0 ∨ q = 11 ∨ q = 22 then 0 else q+1

  let allowed (q : Fin 23) (b : Bool) : Prop := b = false ∨ q = 0 ∨ q = 1

  let warm : Array Nat := #[
    0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
    0xfbebfaebbb6afaebebeb9a6abb6afaebfaebfaeba96a9a6aebeb9a6abb6afaeb,
    0xaa6aba6aab6aba2b2a29926aab6aba6baa6aaa6b292a926a2a29926aab6aba6b,
    0xa86aba6aab62ba2928299262ab6aaa2baa6aa86b2928922228299262aa6aaa2b,
    0xa86ab26aa322322928298262ab2aa22baa6aa06b2928922228298262aa2aa22b,
    0xa86ab22aa122322928298222a92aa22ba86aa02b2920922228298262a82aa22b,
    0xa86ab22aa122322928298222a92a222ba86aa02b2920122228298262a82a222b,
    0xa868b22aa120322928298222a928222ba868a02b2920122228298262a828222b,
    0xa868b22aa120322920298222a128222ba868a02b2120122220298262a028222b,
    0xa868b02aa120302920298022a128222ba868a02b2120102220298062a028222b,
    0x2868302aa120302920290022a128222b2868202b2120102220290062a028222b]

  let cool : Array Nat := #[
    0xd596f0977690f0d6d0d60095769595d69596905656906095d0d60095709595d6,
    0xc3ebcae9984acacacbcb006a984a5aca42eb4a89884a886acbcb006a98425aca,
    0x2a2a2a6aab4a9a2a2a29824aab6a9a2aaa2a2a28290a924a2a29824aab6a9a2a,
    0xa86a9a2aab62b22828289222ab62a22a8a6aa82a2928922228289222aa62a22a,
    0xa86ab26aa022322828288262a82aa22aa06aa06a2828922228288262a82aa22a,
    0xa86aa22aa022222828288222a82a222aa86aa02a2820022228288262a82a222a,
    0xa828a22aa020222828288222a828222aa828a02a2820022228288222a828222a,
    0xa028a22aa020222820288222a020222aa028a02a2020022220288222a020222a,
    0xa028a02aa020202820288022a020202aa028a02a2020002220288022a020202a,
    0x2028202a20202028202800222020202a2028202a20200022202800222020202a,
    0x2028202820202028202800202020202820282028202000202028002020202028,
    0x2020202020202020202000202020202020202020202000202020002020202020]

  let stable : Array Nat := #[
    0x2020202020202020202000202020202020202020202000202020002020202020,
    0x1010101000101010101000100010101010101000001000101010001000101010,
    0x4040400000404040404000400040404040404000004000404040004000404040,
    0x808080000080808080800080008080808080800000800080008000800080808,
    0x2020002022000020202002002200022002200020200000002000020022000220,
    0x802080002020200080208020a0200000a00000008020200080208020a020,
    0x2022200200222020202000220022202020222002000000222020002200222000,
    0x2828200800202020282800200820002020282008082000200828002008200020,
    0x2020220020202200202002202020222020202000202002000020022020202220,
    0xa0208020802020202020802080202020a0208000002000200020802080202020,
    0x2020200200202000202000020020202220202002002000022020000200202022,
    0x28000800202028002800200020202800280008002000200028002000202028,
    0x8080800000808080808000800080808080808000008000808080008000808080,
    0x202020000020202020200020002020202020200000200020002000200020202,
    0x808000888000008080880008800800880080008080000000800800088008008,
    0x20200020220002002022002022200000022000002020020020220020222,
    0x880880288020200828088020802020088008a008082000002808802080002008,
    0x2020000220200220202000222020022220200022202002222020002220200222,
    0xa0282028802020282028002080202028a0082008002000202028002080202028,
    0x2020200220202020202000222020202220202020202000222020002220202022,
    0x2028202800202028202800200020202820282008002000202028002000202028,
    0x2020200020202020202000202020202020202020202000202020002020202020,
    0x2020202000202020202000200020202020202000002000202020002000202020]

  let firstWarm : Nat := 0x1494301552103016101600115214111614941016121020111016009150141116

  let output : Array Bool := #[true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]




  have universal : ∀ i : Fin 256, Fits warm[0]! (BitVec.ofFin i) := by decide
  have warmStep : ∀ k : Fin 10, Moves warm[k.val]! false warm[k.val+1]! := by
    intro k; fin_cases k <;> decide
  have startSingle : Moves warm[10]! true cool[0]! := by decide
  have startDouble : Moves warm[10]! true firstWarm := by decide
  have finishDouble : Moves firstWarm true cool[0]! := by decide
  have coolStep : ∀ k : Fin 11, Moves cool[k.val]! false cool[k.val+1]! := by
    intro k; fin_cases k <;> decide
  have readyOfCool : ∀ i : Fin 256, Fits cool[11]! (BitVec.ofFin i) →
      Fits stable[0]! (BitVec.ofFin i) := by decide
  have stableStep : ∀ (q : Fin 23) (b : Bool), allowed q b →
      Moves stable[q.val]! b stable[(nextPhase q b).val]! := by
    intro q b; fin_cases q <;> cases b <;> first | exact fun h => False.elim ((by decide : ¬ _) h) | exact fun _ => by decide
  have stableBit : ∀ (q : Fin 23) (i : Fin 256), Fits stable[q.val]! (BitVec.ofFin i) →
      (BitVec.ofFin (w := 8) i).getLsbD 0 = output[q.val]! := by
    intro q; fin_cases q <;> decide

  let Run (t n : ℕ) (b : Bool) : Prop := ∀ j < n, centerColumn (t+j) = b

  have movesWindow {m n : ℕ} {b : Bool} (h : Moves m b n) (t : ℕ)
      (hwin : Fits m (window t)) (hbit : centerColumn t = b) : Fits n (window (t+1)) := by
    rw [windowStep, hbit]
    exact h (window t).toFin (state t 9) hwin

  have runTable {t n : ℕ} {b : Bool} (tab : Array Nat)
      (hm : ∀ k : Fin n, Moves tab[k.val]! b tab[k.val+1]!)
      (h0 : Fits tab[0]! (window t)) (h : Run t n b) : Fits tab[n]! (window (t+n)) := by
    have advance (k : ℕ) (hk : k ≤ n) : Fits tab[k]! (window (t+k)) := by
      induction k with
      | zero => simpa using h0
      | succ k ih => exact movesWindow (hm ⟨k, by omega⟩) (t+k) (ih (by omega)) (h k (by omega))
    exact advance n le_rfl

  /- A marker consisting of ten white cells, one or two black cells, then
  eleven white cells puts the right prefix into the invariant at phase zero. -/
  have markerReady (t s : ℕ) (hs : s = 1 ∨ s = 2)
      (a : Run t 10 false) (b : Run (t+10) s true) (c : Run (t+10+s) 11 false) :
      Fits stable[0]! (window (t+10+s+11)) := by
    have ha := runTable warm warmStep (universal (window t).toFin) a
    have hb : Fits cool[0]! (window (t+10+s)) := by
      rcases hs with rfl | rfl
      · exact movesWindow startSingle _ ha (b 0 (by decide))
      · exact movesWindow finishDouble _ (movesWindow startDouble _ ha (b 0 (by decide))) (b 1 (by decide))
    exact readyOfCool _ (runTable cool coolStep hb c)

  /- Phase zero may wait on white or start a burst. Phase one may take a
  second black cell. Each burst must be followed by at least eleven whites. -/
  let Follows (a : ℕ) (phase : ℕ → Fin 23) : Prop :=
    phase 0 = 0 ∧ ∀ j, allowed (phase j) (centerColumn (a+j)) ∧
      phase (j+1) = nextPhase (phase j) (centerColumn (a+j))

  have decoded {a : ℕ} {q : ℕ → Fin 23} (h : Follows a q)
      (h0 : Fits stable[0]! (window a)) (j : ℕ) : state (a+j) 1 = output[(q j).val]! := by
    have inv (k : ℕ) : Fits stable[(q k).val]! (window (a+k)) := by
      induction k with
      | zero => simpa [h.1] using h0
      | succ k ih =>
        rw [(h.2 k).2]
        exact movesWindow (stableStep _ _ (h.2 k).1) _ ih rfl
    rw [← bit0]
    exact stableBit _ _ (inv j)

  /- No eventual period, with any threshold or period length, can have a tail
  made of one- and two-black bursts with at least eleven whites between them.
  The hypotheses give one marker within the periodic part and the phase path
  after it. The path may have arbitrary waiting times and mix both burst lengths. -/
  have noSparsePulseTail (t p s : ℕ) (hp : 0 < p) (hs : s = 1 ∨ s = 2)
      (rep : ∀ n ≥ t, centerColumn (n+p) = centerColumn n)
      (a : Run t 10 false) (b : Run (t+10) s true) (c : Run (t+10+s) 11 false)
      (q : ℕ → Fin 23) (path : Follows (t+10+s+11) q) : False := by
    let u := t+10+s+11
    have shift (k : ℕ) (hk : t ≤ k) (n : ℕ) (v : Bool) (h : Run k n v) : Run (k+p) n v := by
      intro j hj
      rw [show k+p+j = k+j+p by omega, rep _ (by omega)]
      exact h j hj
    have ready := markerReady t s hs a b c
    have ready' : Fits stable[0]! (window (u+p)) := by
      have h1 := shift _ (by omega) _ _ a
      have h2 := shift _ (by omega) _ _ b
      have h3 := shift _ (by omega) _ _ c
      rw [show u+p = (t+p)+10+s+11 by dsimp [u]; omega]
      exact markerReady (t+p) s hs h1
        (by rw [show t+p+10 = t+10+p by omega]; exact h2)
        (by rw [show t+p+10+s = t+10+s+p by omega]; exact h3)
    have eqc (j : ℕ) : centerColumn (u+p+j) = centerColumn (u+j) := by
      rw [show u+p+j = u+j+p by omega, rep _ (by dsimp [u]; omega)]
    have path' : Follows (u+p) q :=
      ⟨path.1, fun j => by rw [eqc]; exact path.2 j⟩
    obtain ⟨j, _, _, hne⟩ := maskedDefect u (u+p) (by omega) (fun j _ => (eqc j).symm)
    exact hne ((decoded path ready j).trans (decoded path' ready' j).symm)

  have sparsePath (N u : ℕ) (hu : N ≤ u)
      (short : ∀ m ≥ N, centerColumn m = true → centerColumn (m+1) = true →
        centerColumn (m+2) = false)
      (gap : ∀ m ≥ N, centerColumn m = true → centerColumn (m+1) = false →
        ∀ k < 11, centerColumn (m+1+k) = false) :
      ∃ q, Follows u q := by
    let q : ℕ → Fin 23 := Nat.rec 0 (fun j last => nextPhase last (centerColumn (u+j)))
    have qstep (j : ℕ) : q (j+1) = nextPhase (q j) (centerColumn (u+j)) := rfl
    let valid (s : Fin 23) (m : ℕ) : Prop :=
      if s = 0 then True else if s = 1 then ∃ n ≥ N, m = n+1 ∧ centerColumn n = true
      else ∀ k < (if s.val < 12 then 12-s.val else 23-s.val), centerColumn (m+k) = false
    have advance (m : ℕ) (hm : N ≤ m) (s : Fin 23) (ok : valid s m) :
        allowed s (centerColumn m) ∧ valid (nextPhase s (centerColumn m)) (m+1) := by
      by_cases h0 : s = 0
      · subst s
        cases he : centerColumn m
        · exact ⟨Or.inl rfl, trivial⟩
        · exact ⟨Or.inr (Or.inl rfl), m, hm, rfl, he⟩
      by_cases h1 : s = 1
      · subst s
        obtain ⟨n, hn, rfl, hblack⟩ := ok
        refine ⟨Or.inr (Or.inr rfl), ?_⟩
        cases he : centerColumn (n+1) with
        | false =>
          change ∀ k < 10, centerColumn (n+1+1+k) = false
          intro k hk
          simpa only [Nat.add_assoc] using gap n hn hblack he (1+k) (by omega)
        | true =>
          change ∀ k < 11, centerColumn (n+1+1+k) = false
          exact gap (n+1) (by omega) he (short n hn hblack he)
      have s0 : s.val ≠ 0 := fun h => h0 (Fin.ext h)
      have s1 : s.val ≠ 1 := fun h => h1 (Fin.ext h)
      have whites : ∀ k < (if s.val < 12 then 12-s.val else 23-s.val),
          centerColumn (m+k) = false := by simpa [valid, h0, h1] using ok
      have current := whites 0 (by split <;> omega)
      simp only [Nat.add_zero] at current
      refine ⟨Or.inl current, ?_⟩
      rw [current]
      by_cases he : s = 11 ∨ s = 22
      · have e : nextPhase s false = 0 := by simp [nextPhase, he]
        simp [e, valid]
      · have he11 : s.val ≠ 11 := fun h => he (Or.inl (Fin.ext h))
        have he22 : s.val ≠ 22 := fun h => he (Or.inr (Fin.ext h))
        have e : nextPhase s false = s+1 := by simp [nextPhase, h0, he]
        have v : (s+1).val = s.val+1 := by
          change (s.val+1)%23 = s.val+1
          apply Nat.mod_eq_of_lt; omega
        have ne0 : s+1 ≠ (0 : Fin 23) := by intro h; have := congrArg Fin.val h; simp [v] at this
        have ne1 : s+1 ≠ (1 : Fin 23) := by intro h; have := congrArg Fin.val h; simp [v, s0] at this
        simp only [valid, e, if_neg ne0, if_neg ne1, v]
        intro k hk
        rw [show m+1+k = m+(1+k) by omega]
        apply whites
        split at hk <;> split <;> omega
    have inv (j : ℕ) : valid (q j) (u+j) := by
      induction j with
      | zero => trivial
      | succ j ih => exact (advance (u+j) (by omega) (q j) ih).2
    exact ⟨q, rfl, fun j => ⟨(advance (u+j) (by omega) _ (inv j)).1, qstep j⟩⟩

  have black (n : ℕ) : ∃ j, centerColumn (n+j) = true := by
    by_contra! h
    apply noConstant n false
    intro t ht
    simpa [Nat.add_sub_of_le ht] using h (t-n)
  obtain ⟨j,hj⟩ := black N
  have endRun (i : ℕ) (hi : N ≤ i) (hb : centerColumn i = true) :
      ∃ s, (s = 1 ∨ s = 2) ∧ Run i s true ∧ Run (i+s) 11 false := by
    cases he : centerColumn (i+1) with
    | false =>
      refine ⟨1, Or.inl rfl, ?_, gap i hi hb he⟩
      intro k hk
      have hk0 : k = 0 := by omega
      simpa [hk0] using hb
    | true =>
      refine ⟨2, Or.inr rfl, ?_, gap (i+1) (by omega) he (short i hi hb he)⟩
      intro k hk; interval_cases k <;> assumption
  obtain ⟨a,ha,_,white⟩ := endRun (N+j) (by omega) hj
  let v := N+j+a
  let z := Nat.find (black v)
  have hz : centerColumn (v+z) = true := Nat.find_spec (black v)
  have prior (i : ℕ) (hi : i < z) : centerColumn (v+i) = false := by
    have h := Nat.find_min (black v) hi
    cases e : centerColumn (v+i) <;> simp_all
  have hz11 : 11 ≤ z := by
    by_contra! hh
    have e : centerColumn (v+z) = false := white _ hh
    rw [e] at hz; contradiction
  obtain ⟨s,hs,bst,wht⟩ := endRun (v+z) (by dsimp [v]; omega) hz
  let t := v+(z-10)
  have ht : N ≤ t := by dsimp [v,t]; omega
  have eql : t+10 = v+z := by dsimp [t]; omega
  obtain ⟨q,path⟩ := sparsePath N (t+10+s+11) (by omega) short gap
  apply noSparsePulseTail t p s hp hs (fun n hn => rep n (by omega)) _ _ _ q path
  · intro k hk
    rw [show t+k = v+(z-10+k) by dsimp [t]; omega]
    exact prior _ (by omega)
  · rwa [eql]
  · rwa [eql]


/-- Arbitrarily long intervals without three consecutive black centers. -/
def H1 : Prop := ∀ L : ℕ, ∃ a : ℕ, ∀ j < L,
    centerColumn (a+j) = true → centerColumn (a+j+1) = true → centerColumn (a+j+2) = false

/-- Arbitrarily long intervals on which every black-to-white transition
starts at least eleven consecutive white cells. -/
def H2 : Prop := ∀ L : ℕ, ∃ a : ℕ, ∀ j < L,
    centerColumn (a+j) = true → centerColumn (a+j+1) = false →
    ∀ k < 11, centerColumn (a+j+1+k) = false

theorem main : H1 → H2 → type_of% @Rule30.centerColumn_not_eventually_periodic := by
  rintro hShort hGap ⟨p, hp, N, rep⟩
  have shift (t k : ℕ) (ht : N ≤ t) : centerColumn (t+p+k) = centerColumn (t+k) := by
    rw [show t+p+k = t+k+p by omega, rep _ (by omega)]
  apply exclusionOfLocalRules p N hp rep
  · apply spread (fun t => centerColumn t = true → centerColumn (t+1) = true →
        centerColumn (t+2) = false) N p hp _ hShort
    intro t ht
    simp only [rep t ht, shift t 1 ht, shift t 2 ht]
  · apply spread (fun t => centerColumn t = true → centerColumn (t+1) = false →
        ∀ k < 11, centerColumn (t+1+k) = false) N p hp _ hGap
    intro t ht
    have shift' (k : ℕ) : centerColumn (t+p+1+k) = centerColumn (t+1+k) := by
      simpa only [Nat.add_assoc] using shift t (1+k) ht
    simp only [rep t ht, shift t 1 ht, shift']

end OMA.R_Rule30_centerColumn_not_eventually_periodic_R1
