import OMAReductions.R_Erdos107_erdos_107_R1_H1_R1

/-!
# Five points in convex position among nine

The 84 increasing triples and the 126 increasing quadruples are numbered in
lexicographic order, with the triples first. The triple variables record the
orientation. A quadruple variable records agreement of its two outer pairs
of orientations. Each increasing quadruple contributes twelve clauses:
eight exclude words with more than one change, and four require the
quadruple variable for convex words. A counterexample would make at least
one of the five quadruple variables false on every five-element subset.

The resulting formula has 1,638 clauses. The certificate gives each learned
clause together with indices of earlier clauses. To check an inference, make
the learned clause false and perform unit propagation along those indices.
Finding a false earlier clause proves the inference. The last inference
derives the empty clause. The numerical checks use kernel reduction.
-/

-- Credit: @zarnab222-dev

namespace E107Finite

private def lit (a : ℕ → Bool) (l : ℕ) : Bool := if l%2 = 0 then a (l/2) else !a (l/2)
private def opposite (l : ℕ) := if l%2 = 0 then l+1 else l-1
private theorem lit_opp (a : ℕ → Bool) (l : ℕ) : lit a (opposite l) = !lit a l := by
  by_cases h : l%2 = 0
  · have odd : (l+1)%2 ≠ 0 := by omega
    have same : (l+1)/2 = l/2 := by omega
    simp [lit,opposite,h,odd,same]
  · have even : (l-1)%2 = 0 := by omega
    have same : (l-1)/2 = l/2 := by omega
    simp [lit,opposite,h,even,same]

private def scan (lookup : ℕ → Option (List ℕ)) (fixed : List ℕ) : List ℕ → Bool
  | [] => false
  | j :: js =>
    match lookup j with
    | none => false
    | some c =>
      match c.filter (fun x => !fixed.contains x) with
      | [] => true
      | [x] => scan lookup (opposite x :: fixed) js
      | _ => false

private theorem scan_false (a : ℕ → Bool) (lookup : ℕ → Option (List ℕ))
    (ok : ∀ j c, lookup j = some c → ∃ l ∈ c, lit a l = true)
    (fixed : List ℕ) (hf : ∀ l ∈ fixed, lit a l = false) (js : List ℕ) :
    scan lookup fixed js = false := by
  induction js generalizing fixed with
  | nil => rfl
  | cons j js ih =>
    cases h : lookup j with
    | none => simp [scan,h]
    | some c =>
      obtain ⟨l,hl,ht⟩ := ok j c h
      have outside : l ∉ fixed := fun z => by simpa [ht] using hf l z
      have left : l ∈ c.filter (fun x => !fixed.contains x) := by simp [hl,outside]
      cases g : c.filter (fun x => !fixed.contains x) with
      | nil => rw [g] at left; exact False.elim (List.not_mem_nil left)
      | cons x xs =>
        cases xs with
        | cons y ys => simp only [scan,h,g]
        | nil =>
          rw [g] at left
          have lx : l = x := by simpa using left
          simp only [scan,h,g]
          apply ih
          intro k hk
          rcases List.mem_cons.mp hk with rfl | old
          · simp [lit_opp,← lx,ht]
          · exact hf k old

private def fixedMask : List Nat → Nat
  | [] => 0
  | x :: xs => (2 ^ x) ||| fixedMask xs

private theorem mask_test (xs : List Nat) (l : Nat) :
    (fixedMask xs).testBit l = xs.contains l := by
  induction xs with
  | nil => simp [fixedMask]
  | cons x xs ih => simp [fixedMask, Nat.testBit_two_pow, ih,eq_comm]

private def scanBits (lookup : Nat → Option (List Nat)) (fixed : Nat) : List Nat → Bool
  | [] => false
  | j :: js =>
    match lookup j with
    | none => false
    | some c =>
      match c.filter (fun x => !fixed.testBit x) with
      | [] => true
      | [x] => scanBits lookup ((2 ^ opposite x) ||| fixed) js
      | _ => false

private theorem scanBits_eq (lk : Nat → Option (List Nat)) (fixed js : List Nat) :
    scanBits lk (fixedMask fixed) js = scan lk fixed js := by
  induction js generalizing fixed with
  | nil => rfl
  | cons j js ih =>
    cases src : lk j with
    | none => simp [scan,scanBits,src]
    | some c =>
      simp only [scan,scanBits,src,mask_test]
      cases rest : c.filter (fun x => !fixed.contains x) with
      | nil => rfl
      | cons x xs =>
        cases xs with
        | nil => exact ih (opposite x :: fixed)
        | cons y ys => rfl

private abbrev Steps := Nat → List Nat × List Nat
private def source (base : Nat → Option (List Nat)) (steps : Steps) (s i j : Nat) :=
  if j < s then base j else if j - s < i then some (steps (j-s)).1 else none
private def stepOK (base : Nat → Option (List Nat)) (steps : Steps) (s i : Nat) :=
  scanBits (source base steps s i) (fixedMask (steps i).1) (steps i).2

private theorem steps_sound (base : Nat → Option (List Nat)) (steps : Steps)
    (s k : Nat) (ok : ∀ i < k, stepOK base steps s i = true) (a : Nat → Bool)
    (sat : ∀ j d, base j = some d → ∃ l ∈ d, lit a l = true) (i : Nat) (hi : i < k) :
    ∃ l ∈ (steps i).1, lit a l = true := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_contra! none
    have hf (l) (hl : l ∈ (steps i).1) : lit a l = false := by simpa using none l hl
    have earlier (j d) (he : source base steps s i j = some d) : ∃ l ∈ d, lit a l = true := by
      by_cases before : j < s
      · exact sat j d (by simpa only [source,if_pos before] using he)
      · by_cases prior : j - s < i
        · have eq : (steps (j-s)).1 = d := by simpa [source,before,prior] using he
          exact eq ▸ ih _ prior (by omega)
        · simp [source,before,prior] at he
    have valid := ok i hi
    rw [stepOK,scanBits_eq] at valid
    exact Bool.noConfusion (valid.symm.trans (scan_false a _ earlier _ hf _))

private theorem pass_range (p : Nat → Bool) (a len : Nat)
    (h : (List.range' a len).all p = true) : ∀ i, a ≤ i → i < a+len → p i = true := by
  intro i ha hb
  exact List.all_eq_true.mp h i (List.mem_range'_1.mpr ⟨ha,hb⟩)

private theorem pass_merge {p : Nat → Bool} {a b c : Nat}
    (left : ∀ i, a ≤ i → i < b → p i = true)
    (right : ∀ i, b ≤ i → i < c → p i = true) :
    ∀ i, a ≤ i → i < c → p i = true := by
  intro i ha hc
  by_cases hb : i < b
  · exact left i ha hb
  · exact right i (by omega) hc


private abbrev Col := Fin 9 → Fin 9 → Fin 9 → Bool
private def regular (a b c d : Bool) : Prop :=
  (a=b ∧ b=c) ∨ (a=b ∧ c=d) ∨ (b=c ∧ c=d)
private def cv (a b c d : Bool) := (a == b) && (c == d)
private def cvQ (f : Col) (a b c d : Fin 9) :=
  cv (f a b c) (f a b d) (f a c d) (f b c d)
private def witness (f : Col) : Prop :=
  ∃ T : Finset (Fin 9), T.card = 5 ∧ ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T,
    a < b → b < c → c < d → f a b c = f a b d ∧ f a c d = f b c d
private def endPoint (f : Col) (a b c d e : Fin 9) :=
  !(cvQ f a b c d && cvQ f a b c e && cvQ f a b d e &&
    cvQ f a c d e && cvQ f b c d e)
set_option maxHeartbeats 4000000 in
private theorem pent_excluded (f : Col) (bad : ¬witness f) (a b c d e : Fin 9)
    (h₁ : a < b) (h₂ : b < c) (h₃ : c < d) (h₄ : d < e) :
    endPoint f a b c d e = true := by
  by_contra! h
  simp [endPoint,cvQ,cv] at h
  apply bad
  refine ⟨{a,b,c,d,e},?_,?_⟩
  · have hn : [a,b,c,d,e].Nodup := by simp; omega
    simpa using List.toFinset_card_of_nodup hn
  · intro i hi j hj k hk l hl hij hjk hkl
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi hj hk hl
    have ord : (i=a ∧ j=b ∧ k=c ∧ l=d) ∨ (i=a ∧ j=b ∧ k=c ∧ l=e) ∨
        (i=a ∧ j=b ∧ k=d ∧ l=e) ∨ (i=a ∧ j=c ∧ k=d ∧ l=e) ∨
        (i=b ∧ j=c ∧ k=d ∧ l=e) := by
      clear bad h
      rcases hi with rfl|rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl|rfl <;>
        first | (exfalso; clear hk hl; omega) | skip
      all_goals rcases hk with rfl|rfl|rfl|rfl|rfl <;>
        first | (exfalso; clear hl; omega) | skip
      all_goals rcases hl with rfl|rfl|rfl|rfl|rfl <;> omega
    rcases ord with ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ |
      ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ <;> tauto

private def quadRows (a b c d z : Nat) : List (List Nat) :=
  [[2*a,2*b,2*c,2*d,2*z],[2*a,2*b,2*c+1,2*d],[2*a,2*b,2*c+1,2*d+1,2*z],
   [2*a,2*b+1,2*c,2*d],[2*a,2*b+1,2*c,2*d+1],[2*a,2*b+1,2*c+1,2*d],
   [2*a+1,2*b,2*c,2*d+1],[2*a+1,2*b,2*c+1,2*d],[2*a+1,2*b,2*c+1,2*d+1],
   [2*a+1,2*b+1,2*c,2*d,2*z],[2*a+1,2*b+1,2*c,2*d+1],[2*a+1,2*b+1,2*c+1,2*d+1,2*z]]
private def pentRows (a b c d e : Nat) : List (List Nat) :=
  [[2*a+1,2*b+1,2*c+1,2*d+1,2*e+1]]

private theorem lit_pos (v : ℕ → Bool) (i : ℕ) : lit v (2*i) = v i := by simp [lit]
private theorem lit_neg (v : ℕ → Bool) (i : ℕ) : lit v (2*i+1) = !v i := by
  have h : (2*i+1)/2=i := by omega
  simp [lit,h]

private def satRows (v : Nat → Bool) (rows : List (List Nat)) :=
  rows.all (fun row => row.any (lit v)) = true

private theorem quadOK (v : Nat → Bool) (a b c d z : Nat)
    (h : regular (v a) (v b) (v c) (v d)) (hz : v z = cv (v a) (v b) (v c) (v d)) :
    satRows v (quadRows a b c d z) := by
  cases ha : v a <;> cases hb : v b <;> cases hc : v c <;> cases hd : v d <;>
    simp [regular,ha,hb,hc,hd] at h <;>
    simp [satRows,quadRows,lit_pos,lit_neg,hz,ha,hb,hc,hd,cv]

private theorem pentOK (v : Nat → Bool) (a b c d e : Nat)
    (h : (!(v a && v b && v c && v d && v e)) = true) :
    satRows v (pentRows a b c d e) := by
  cases ha : v a <;> cases hb : v b <;> cases hc : v c <;> cases hd : v d <;> cases he : v e <;>
    simp [ha,hb,hc,hd,he] at h <;>
    simp [satRows,pentRows,lit_neg,ha,hb,hc,hd,he]

private theorem satAppend (v : Nat → Bool) {a b} (ha : satRows v a) (hb : satRows v b) :
    satRows v (a ++ b) := by simpa [satRows,List.all_append] using And.intro ha hb

private def valAtP0 (i : Nat) : Col → Bool := (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then (fun f => f 0 1 2) else (fun f => f 0 1 3)) else (if i < 3 then (fun f => f 0 1 4) else (fun f => f 0 1 5))) else (if i < 6 then (if i < 5 then (fun f => f 0 1 6) else (fun f => f 0 1 7)) else (if i < 7 then (fun f => f 0 1 8) else (fun f => f 0 2 3)))) else (if i < 12 then (if i < 10 then (if i < 9 then (fun f => f 0 2 4) else (fun f => f 0 2 5)) else (if i < 11 then (fun f => f 0 2 6) else (fun f => f 0 2 7))) else (if i < 14 then (if i < 13 then (fun f => f 0 2 8) else (fun f => f 0 3 4)) else (if i < 15 then (fun f => f 0 3 5) else (fun f => f 0 3 6)))))
private def valAtP1 (i : Nat) : Col → Bool := (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then (fun f => f 0 3 7) else (fun f => f 0 3 8)) else (if i < 19 then (fun f => f 0 4 5) else (fun f => f 0 4 6))) else (if i < 22 then (if i < 21 then (fun f => f 0 4 7) else (fun f => f 0 4 8)) else (if i < 23 then (fun f => f 0 5 6) else (fun f => f 0 5 7)))) else (if i < 28 then (if i < 26 then (if i < 25 then (fun f => f 0 5 8) else (fun f => f 0 6 7)) else (if i < 27 then (fun f => f 0 6 8) else (fun f => f 0 7 8))) else (if i < 30 then (if i < 29 then (fun f => f 1 2 3) else (fun f => f 1 2 4)) else (if i < 31 then (fun f => f 1 2 5) else (fun f => f 1 2 6)))))
private def valAtP2 (i : Nat) : Col → Bool := (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then (fun f => f 1 2 7) else (fun f => f 1 2 8)) else (if i < 35 then (fun f => f 1 3 4) else (fun f => f 1 3 5))) else (if i < 38 then (if i < 37 then (fun f => f 1 3 6) else (fun f => f 1 3 7)) else (if i < 39 then (fun f => f 1 3 8) else (fun f => f 1 4 5)))) else (if i < 44 then (if i < 42 then (if i < 41 then (fun f => f 1 4 6) else (fun f => f 1 4 7)) else (if i < 43 then (fun f => f 1 4 8) else (fun f => f 1 5 6))) else (if i < 46 then (if i < 45 then (fun f => f 1 5 7) else (fun f => f 1 5 8)) else (if i < 47 then (fun f => f 1 6 7) else (fun f => f 1 6 8)))))
private def valAtP3 (i : Nat) : Col → Bool := (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then (fun f => f 1 7 8) else (fun f => f 2 3 4)) else (if i < 51 then (fun f => f 2 3 5) else (fun f => f 2 3 6))) else (if i < 54 then (if i < 53 then (fun f => f 2 3 7) else (fun f => f 2 3 8)) else (if i < 55 then (fun f => f 2 4 5) else (fun f => f 2 4 6)))) else (if i < 60 then (if i < 58 then (if i < 57 then (fun f => f 2 4 7) else (fun f => f 2 4 8)) else (if i < 59 then (fun f => f 2 5 6) else (fun f => f 2 5 7))) else (if i < 62 then (if i < 61 then (fun f => f 2 5 8) else (fun f => f 2 6 7)) else (if i < 63 then (fun f => f 2 6 8) else (fun f => f 2 7 8)))))
private def valAtP4 (i : Nat) : Col → Bool := (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then (fun f => f 3 4 5) else (fun f => f 3 4 6)) else (if i < 67 then (fun f => f 3 4 7) else (fun f => f 3 4 8))) else (if i < 70 then (if i < 69 then (fun f => f 3 5 6) else (fun f => f 3 5 7)) else (if i < 71 then (fun f => f 3 5 8) else (fun f => f 3 6 7)))) else (if i < 76 then (if i < 74 then (if i < 73 then (fun f => f 3 6 8) else (fun f => f 3 7 8)) else (if i < 75 then (fun f => f 4 5 6) else (fun f => f 4 5 7))) else (if i < 78 then (if i < 77 then (fun f => f 4 5 8) else (fun f => f 4 6 7)) else (if i < 79 then (fun f => f 4 6 8) else (fun f => f 4 7 8)))))
private def valAtP5 (i : Nat) : Col → Bool := (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then (fun f => f 5 6 7) else (fun f => f 5 6 8)) else (if i < 83 then (fun f => f 5 7 8) else (fun f => f 6 7 8))) else (if i < 86 then (if i < 85 then (fun f => cvQ f 0 1 2 3) else (fun f => cvQ f 0 1 2 4)) else (if i < 87 then (fun f => cvQ f 0 1 2 5) else (fun f => cvQ f 0 1 2 6)))) else (if i < 92 then (if i < 90 then (if i < 89 then (fun f => cvQ f 0 1 2 7) else (fun f => cvQ f 0 1 2 8)) else (if i < 91 then (fun f => cvQ f 0 1 3 4) else (fun f => cvQ f 0 1 3 5))) else (if i < 94 then (if i < 93 then (fun f => cvQ f 0 1 3 6) else (fun f => cvQ f 0 1 3 7)) else (if i < 95 then (fun f => cvQ f 0 1 3 8) else (fun f => cvQ f 0 1 4 5)))))
private def valAtP6 (i : Nat) : Col → Bool := (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then (fun f => cvQ f 0 1 4 6) else (fun f => cvQ f 0 1 4 7)) else (if i < 99 then (fun f => cvQ f 0 1 4 8) else (fun f => cvQ f 0 1 5 6))) else (if i < 102 then (if i < 101 then (fun f => cvQ f 0 1 5 7) else (fun f => cvQ f 0 1 5 8)) else (if i < 103 then (fun f => cvQ f 0 1 6 7) else (fun f => cvQ f 0 1 6 8)))) else (if i < 108 then (if i < 106 then (if i < 105 then (fun f => cvQ f 0 1 7 8) else (fun f => cvQ f 0 2 3 4)) else (if i < 107 then (fun f => cvQ f 0 2 3 5) else (fun f => cvQ f 0 2 3 6))) else (if i < 110 then (if i < 109 then (fun f => cvQ f 0 2 3 7) else (fun f => cvQ f 0 2 3 8)) else (if i < 111 then (fun f => cvQ f 0 2 4 5) else (fun f => cvQ f 0 2 4 6)))))
private def valAtP7 (i : Nat) : Col → Bool := (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then (fun f => cvQ f 0 2 4 7) else (fun f => cvQ f 0 2 4 8)) else (if i < 115 then (fun f => cvQ f 0 2 5 6) else (fun f => cvQ f 0 2 5 7))) else (if i < 118 then (if i < 117 then (fun f => cvQ f 0 2 5 8) else (fun f => cvQ f 0 2 6 7)) else (if i < 119 then (fun f => cvQ f 0 2 6 8) else (fun f => cvQ f 0 2 7 8)))) else (if i < 124 then (if i < 122 then (if i < 121 then (fun f => cvQ f 0 3 4 5) else (fun f => cvQ f 0 3 4 6)) else (if i < 123 then (fun f => cvQ f 0 3 4 7) else (fun f => cvQ f 0 3 4 8))) else (if i < 126 then (if i < 125 then (fun f => cvQ f 0 3 5 6) else (fun f => cvQ f 0 3 5 7)) else (if i < 127 then (fun f => cvQ f 0 3 5 8) else (fun f => cvQ f 0 3 6 7)))))
private def valAtP8 (i : Nat) : Col → Bool := (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then (fun f => cvQ f 0 3 6 8) else (fun f => cvQ f 0 3 7 8)) else (if i < 131 then (fun f => cvQ f 0 4 5 6) else (fun f => cvQ f 0 4 5 7))) else (if i < 134 then (if i < 133 then (fun f => cvQ f 0 4 5 8) else (fun f => cvQ f 0 4 6 7)) else (if i < 135 then (fun f => cvQ f 0 4 6 8) else (fun f => cvQ f 0 4 7 8)))) else (if i < 140 then (if i < 138 then (if i < 137 then (fun f => cvQ f 0 5 6 7) else (fun f => cvQ f 0 5 6 8)) else (if i < 139 then (fun f => cvQ f 0 5 7 8) else (fun f => cvQ f 0 6 7 8))) else (if i < 142 then (if i < 141 then (fun f => cvQ f 1 2 3 4) else (fun f => cvQ f 1 2 3 5)) else (if i < 143 then (fun f => cvQ f 1 2 3 6) else (fun f => cvQ f 1 2 3 7)))))
private def valAtP9 (i : Nat) : Col → Bool := (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then (fun f => cvQ f 1 2 3 8) else (fun f => cvQ f 1 2 4 5)) else (if i < 147 then (fun f => cvQ f 1 2 4 6) else (fun f => cvQ f 1 2 4 7))) else (if i < 150 then (if i < 149 then (fun f => cvQ f 1 2 4 8) else (fun f => cvQ f 1 2 5 6)) else (if i < 151 then (fun f => cvQ f 1 2 5 7) else (fun f => cvQ f 1 2 5 8)))) else (if i < 156 then (if i < 154 then (if i < 153 then (fun f => cvQ f 1 2 6 7) else (fun f => cvQ f 1 2 6 8)) else (if i < 155 then (fun f => cvQ f 1 2 7 8) else (fun f => cvQ f 1 3 4 5))) else (if i < 158 then (if i < 157 then (fun f => cvQ f 1 3 4 6) else (fun f => cvQ f 1 3 4 7)) else (if i < 159 then (fun f => cvQ f 1 3 4 8) else (fun f => cvQ f 1 3 5 6)))))
private def valAtP10 (i : Nat) : Col → Bool := (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then (fun f => cvQ f 1 3 5 7) else (fun f => cvQ f 1 3 5 8)) else (if i < 163 then (fun f => cvQ f 1 3 6 7) else (fun f => cvQ f 1 3 6 8))) else (if i < 166 then (if i < 165 then (fun f => cvQ f 1 3 7 8) else (fun f => cvQ f 1 4 5 6)) else (if i < 167 then (fun f => cvQ f 1 4 5 7) else (fun f => cvQ f 1 4 5 8)))) else (if i < 172 then (if i < 170 then (if i < 169 then (fun f => cvQ f 1 4 6 7) else (fun f => cvQ f 1 4 6 8)) else (if i < 171 then (fun f => cvQ f 1 4 7 8) else (fun f => cvQ f 1 5 6 7))) else (if i < 174 then (if i < 173 then (fun f => cvQ f 1 5 6 8) else (fun f => cvQ f 1 5 7 8)) else (if i < 175 then (fun f => cvQ f 1 6 7 8) else (fun f => cvQ f 2 3 4 5)))))
private def valAtP11 (i : Nat) : Col → Bool := (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then (fun f => cvQ f 2 3 4 6) else (fun f => cvQ f 2 3 4 7)) else (if i < 179 then (fun f => cvQ f 2 3 4 8) else (fun f => cvQ f 2 3 5 6))) else (if i < 182 then (if i < 181 then (fun f => cvQ f 2 3 5 7) else (fun f => cvQ f 2 3 5 8)) else (if i < 183 then (fun f => cvQ f 2 3 6 7) else (fun f => cvQ f 2 3 6 8)))) else (if i < 188 then (if i < 186 then (if i < 185 then (fun f => cvQ f 2 3 7 8) else (fun f => cvQ f 2 4 5 6)) else (if i < 187 then (fun f => cvQ f 2 4 5 7) else (fun f => cvQ f 2 4 5 8))) else (if i < 190 then (if i < 189 then (fun f => cvQ f 2 4 6 7) else (fun f => cvQ f 2 4 6 8)) else (if i < 191 then (fun f => cvQ f 2 4 7 8) else (fun f => cvQ f 2 5 6 7)))))
private def valAtP12 (i : Nat) : Col → Bool := (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then (fun f => cvQ f 2 5 6 8) else (fun f => cvQ f 2 5 7 8)) else (if i < 195 then (fun f => cvQ f 2 6 7 8) else (fun f => cvQ f 3 4 5 6))) else (if i < 198 then (if i < 197 then (fun f => cvQ f 3 4 5 7) else (fun f => cvQ f 3 4 5 8)) else (if i < 199 then (fun f => cvQ f 3 4 6 7) else (fun f => cvQ f 3 4 6 8)))) else (if i < 204 then (if i < 202 then (if i < 201 then (fun f => cvQ f 3 4 7 8) else (fun f => cvQ f 3 5 6 7)) else (if i < 203 then (fun f => cvQ f 3 5 6 8) else (fun f => cvQ f 3 5 7 8))) else (if i < 206 then (if i < 205 then (fun f => cvQ f 3 6 7 8) else (fun f => cvQ f 4 5 6 7)) else (if i < 207 then (fun f => cvQ f 4 5 6 8) else (fun f => cvQ f 4 5 7 8)))))
private def valAtP13 (i : Nat) : Col → Bool := (if i < 209 then (fun f => cvQ f 4 6 7 8) else (fun f => cvQ f 5 6 7 8))
private def valAt (i : Nat) : Col → Bool := (if i < 112 then (if i < 48 then (if i < 16 then (valAtP0 i) else (if i < 32 then (valAtP1 i) else (valAtP2 i))) else (if i < 80 then (if i < 64 then (valAtP3 i) else (valAtP4 i)) else (if i < 96 then (valAtP5 i) else (valAtP6 i)))) else (if i < 160 then (if i < 128 then (valAtP7 i) else (if i < 144 then (valAtP8 i) else (valAtP9 i))) else (if i < 192 then (if i < 176 then (valAtP10 i) else (valAtP11 i)) else (if i < 208 then (valAtP12 i) else (valAtP13 i)))))
private def assn (f : Col) (i : Nat) := valAt i f
private def groupP0 (i : Nat) : List (List Nat) := (if i < 6 then (if i < 3 then (if i < 1 then (quadRows 0 1 7 28 84) else (if i < 2 then (quadRows 0 2 8 29 85) else (quadRows 0 3 9 30 86))) else (if i < 4 then (quadRows 0 4 10 31 87) else (if i < 5 then (quadRows 0 5 11 32 88) else (quadRows 0 6 12 33 89)))) else (if i < 9 then (if i < 7 then (quadRows 1 2 13 34 90) else (if i < 8 then (quadRows 1 3 14 35 91) else (quadRows 1 4 15 36 92))) else (if i < 10 then (quadRows 1 5 16 37 93) else (if i < 11 then (quadRows 1 6 17 38 94) else (quadRows 2 3 18 39 95)))))
private def groupP1 (i : Nat) : List (List Nat) := (if i < 18 then (if i < 15 then (if i < 13 then (quadRows 2 4 19 40 96) else (if i < 14 then (quadRows 2 5 20 41 97) else (quadRows 2 6 21 42 98))) else (if i < 16 then (quadRows 3 4 22 43 99) else (if i < 17 then (quadRows 3 5 23 44 100) else (quadRows 3 6 24 45 101)))) else (if i < 21 then (if i < 19 then (quadRows 4 5 25 46 102) else (if i < 20 then (quadRows 4 6 26 47 103) else (quadRows 5 6 27 48 104))) else (if i < 22 then (quadRows 7 8 13 49 105) else (if i < 23 then (quadRows 7 9 14 50 106) else (quadRows 7 10 15 51 107)))))
private def groupP2 (i : Nat) : List (List Nat) := (if i < 30 then (if i < 27 then (if i < 25 then (quadRows 7 11 16 52 108) else (if i < 26 then (quadRows 7 12 17 53 109) else (quadRows 8 9 18 54 110))) else (if i < 28 then (quadRows 8 10 19 55 111) else (if i < 29 then (quadRows 8 11 20 56 112) else (quadRows 8 12 21 57 113)))) else (if i < 33 then (if i < 31 then (quadRows 9 10 22 58 114) else (if i < 32 then (quadRows 9 11 23 59 115) else (quadRows 9 12 24 60 116))) else (if i < 34 then (quadRows 10 11 25 61 117) else (if i < 35 then (quadRows 10 12 26 62 118) else (quadRows 11 12 27 63 119)))))
private def groupP3 (i : Nat) : List (List Nat) := (if i < 42 then (if i < 39 then (if i < 37 then (quadRows 13 14 18 64 120) else (if i < 38 then (quadRows 13 15 19 65 121) else (quadRows 13 16 20 66 122))) else (if i < 40 then (quadRows 13 17 21 67 123) else (if i < 41 then (quadRows 14 15 22 68 124) else (quadRows 14 16 23 69 125)))) else (if i < 45 then (if i < 43 then (quadRows 14 17 24 70 126) else (if i < 44 then (quadRows 15 16 25 71 127) else (quadRows 15 17 26 72 128))) else (if i < 46 then (quadRows 16 17 27 73 129) else (if i < 47 then (quadRows 18 19 22 74 130) else (quadRows 18 20 23 75 131)))))
private def groupP4 (i : Nat) : List (List Nat) := (if i < 54 then (if i < 51 then (if i < 49 then (quadRows 18 21 24 76 132) else (if i < 50 then (quadRows 19 20 25 77 133) else (quadRows 19 21 26 78 134))) else (if i < 52 then (quadRows 20 21 27 79 135) else (if i < 53 then (quadRows 22 23 25 80 136) else (quadRows 22 24 26 81 137)))) else (if i < 57 then (if i < 55 then (quadRows 23 24 27 82 138) else (if i < 56 then (quadRows 25 26 27 83 139) else (quadRows 28 29 34 49 140))) else (if i < 58 then (quadRows 28 30 35 50 141) else (if i < 59 then (quadRows 28 31 36 51 142) else (quadRows 28 32 37 52 143)))))
private def groupP5 (i : Nat) : List (List Nat) := (if i < 66 then (if i < 63 then (if i < 61 then (quadRows 28 33 38 53 144) else (if i < 62 then (quadRows 29 30 39 54 145) else (quadRows 29 31 40 55 146))) else (if i < 64 then (quadRows 29 32 41 56 147) else (if i < 65 then (quadRows 29 33 42 57 148) else (quadRows 30 31 43 58 149)))) else (if i < 69 then (if i < 67 then (quadRows 30 32 44 59 150) else (if i < 68 then (quadRows 30 33 45 60 151) else (quadRows 31 32 46 61 152))) else (if i < 70 then (quadRows 31 33 47 62 153) else (if i < 71 then (quadRows 32 33 48 63 154) else (quadRows 34 35 39 64 155)))))
private def groupP6 (i : Nat) : List (List Nat) := (if i < 78 then (if i < 75 then (if i < 73 then (quadRows 34 36 40 65 156) else (if i < 74 then (quadRows 34 37 41 66 157) else (quadRows 34 38 42 67 158))) else (if i < 76 then (quadRows 35 36 43 68 159) else (if i < 77 then (quadRows 35 37 44 69 160) else (quadRows 35 38 45 70 161)))) else (if i < 81 then (if i < 79 then (quadRows 36 37 46 71 162) else (if i < 80 then (quadRows 36 38 47 72 163) else (quadRows 37 38 48 73 164))) else (if i < 82 then (quadRows 39 40 43 74 165) else (if i < 83 then (quadRows 39 41 44 75 166) else (quadRows 39 42 45 76 167)))))
private def groupP7 (i : Nat) : List (List Nat) := (if i < 90 then (if i < 87 then (if i < 85 then (quadRows 40 41 46 77 168) else (if i < 86 then (quadRows 40 42 47 78 169) else (quadRows 41 42 48 79 170))) else (if i < 88 then (quadRows 43 44 46 80 171) else (if i < 89 then (quadRows 43 45 47 81 172) else (quadRows 44 45 48 82 173)))) else (if i < 93 then (if i < 91 then (quadRows 46 47 48 83 174) else (if i < 92 then (quadRows 49 50 54 64 175) else (quadRows 49 51 55 65 176))) else (if i < 94 then (quadRows 49 52 56 66 177) else (if i < 95 then (quadRows 49 53 57 67 178) else (quadRows 50 51 58 68 179)))))
private def groupP8 (i : Nat) : List (List Nat) := (if i < 102 then (if i < 99 then (if i < 97 then (quadRows 50 52 59 69 180) else (if i < 98 then (quadRows 50 53 60 70 181) else (quadRows 51 52 61 71 182))) else (if i < 100 then (quadRows 51 53 62 72 183) else (if i < 101 then (quadRows 52 53 63 73 184) else (quadRows 54 55 58 74 185)))) else (if i < 105 then (if i < 103 then (quadRows 54 56 59 75 186) else (if i < 104 then (quadRows 54 57 60 76 187) else (quadRows 55 56 61 77 188))) else (if i < 106 then (quadRows 55 57 62 78 189) else (if i < 107 then (quadRows 56 57 63 79 190) else (quadRows 58 59 61 80 191)))))
private def groupP9 (i : Nat) : List (List Nat) := (if i < 114 then (if i < 111 then (if i < 109 then (quadRows 58 60 62 81 192) else (if i < 110 then (quadRows 59 60 63 82 193) else (quadRows 61 62 63 83 194))) else (if i < 112 then (quadRows 64 65 68 74 195) else (if i < 113 then (quadRows 64 66 69 75 196) else (quadRows 64 67 70 76 197)))) else (if i < 117 then (if i < 115 then (quadRows 65 66 71 77 198) else (if i < 116 then (quadRows 65 67 72 78 199) else (quadRows 66 67 73 79 200))) else (if i < 118 then (quadRows 68 69 71 80 201) else (if i < 119 then (quadRows 68 70 72 81 202) else (quadRows 69 70 73 82 203)))))
private def groupP10 (i : Nat) : List (List Nat) := (if i < 126 then (if i < 123 then (if i < 121 then (quadRows 71 72 73 83 204) else (if i < 122 then (quadRows 74 75 77 80 205) else (quadRows 74 76 78 81 206))) else (if i < 124 then (quadRows 75 76 79 82 207) else (if i < 125 then (quadRows 77 78 79 83 208) else (quadRows 80 81 82 83 209)))) else (if i < 129 then (if i < 127 then (pentRows 84 85 90 105 140) else (if i < 128 then (pentRows 84 86 91 106 141) else (pentRows 84 87 92 107 142))) else (if i < 130 then (pentRows 84 88 93 108 143) else (if i < 131 then (pentRows 84 89 94 109 144) else (pentRows 85 86 95 110 145)))))
private def groupP11 (i : Nat) : List (List Nat) := (if i < 138 then (if i < 135 then (if i < 133 then (pentRows 85 87 96 111 146) else (if i < 134 then (pentRows 85 88 97 112 147) else (pentRows 85 89 98 113 148))) else (if i < 136 then (pentRows 86 87 99 114 149) else (if i < 137 then (pentRows 86 88 100 115 150) else (pentRows 86 89 101 116 151)))) else (if i < 141 then (if i < 139 then (pentRows 87 88 102 117 152) else (if i < 140 then (pentRows 87 89 103 118 153) else (pentRows 88 89 104 119 154))) else (if i < 142 then (pentRows 90 91 95 120 155) else (if i < 143 then (pentRows 90 92 96 121 156) else (pentRows 90 93 97 122 157)))))
private def groupP12 (i : Nat) : List (List Nat) := (if i < 150 then (if i < 147 then (if i < 145 then (pentRows 90 94 98 123 158) else (if i < 146 then (pentRows 91 92 99 124 159) else (pentRows 91 93 100 125 160))) else (if i < 148 then (pentRows 91 94 101 126 161) else (if i < 149 then (pentRows 92 93 102 127 162) else (pentRows 92 94 103 128 163)))) else (if i < 153 then (if i < 151 then (pentRows 93 94 104 129 164) else (if i < 152 then (pentRows 95 96 99 130 165) else (pentRows 95 97 100 131 166))) else (if i < 154 then (pentRows 95 98 101 132 167) else (if i < 155 then (pentRows 96 97 102 133 168) else (pentRows 96 98 103 134 169)))))
private def groupP13 (i : Nat) : List (List Nat) := (if i < 162 then (if i < 159 then (if i < 157 then (pentRows 97 98 104 135 170) else (if i < 158 then (pentRows 99 100 102 136 171) else (pentRows 99 101 103 137 172))) else (if i < 160 then (pentRows 100 101 104 138 173) else (if i < 161 then (pentRows 102 103 104 139 174) else (pentRows 105 106 110 120 175)))) else (if i < 165 then (if i < 163 then (pentRows 105 107 111 121 176) else (if i < 164 then (pentRows 105 108 112 122 177) else (pentRows 105 109 113 123 178))) else (if i < 166 then (pentRows 106 107 114 124 179) else (if i < 167 then (pentRows 106 108 115 125 180) else (pentRows 106 109 116 126 181)))))
private def groupP14 (i : Nat) : List (List Nat) := (if i < 174 then (if i < 171 then (if i < 169 then (pentRows 107 108 117 127 182) else (if i < 170 then (pentRows 107 109 118 128 183) else (pentRows 108 109 119 129 184))) else (if i < 172 then (pentRows 110 111 114 130 185) else (if i < 173 then (pentRows 110 112 115 131 186) else (pentRows 110 113 116 132 187)))) else (if i < 177 then (if i < 175 then (pentRows 111 112 117 133 188) else (if i < 176 then (pentRows 111 113 118 134 189) else (pentRows 112 113 119 135 190))) else (if i < 178 then (pentRows 114 115 117 136 191) else (if i < 179 then (pentRows 114 116 118 137 192) else (pentRows 115 116 119 138 193)))))
private def groupP15 (i : Nat) : List (List Nat) := (if i < 186 then (if i < 183 then (if i < 181 then (pentRows 117 118 119 139 194) else (if i < 182 then (pentRows 120 121 124 130 195) else (pentRows 120 122 125 131 196))) else (if i < 184 then (pentRows 120 123 126 132 197) else (if i < 185 then (pentRows 121 122 127 133 198) else (pentRows 121 123 128 134 199)))) else (if i < 189 then (if i < 187 then (pentRows 122 123 129 135 200) else (if i < 188 then (pentRows 124 125 127 136 201) else (pentRows 124 126 128 137 202))) else (if i < 190 then (pentRows 125 126 129 138 203) else (if i < 191 then (pentRows 127 128 129 139 204) else (pentRows 130 131 133 136 205)))))
private def groupP16 (i : Nat) : List (List Nat) := (if i < 198 then (if i < 195 then (if i < 193 then (pentRows 130 132 134 137 206) else (if i < 194 then (pentRows 131 132 135 138 207) else (pentRows 133 134 135 139 208))) else (if i < 196 then (pentRows 136 137 138 139 209) else (if i < 197 then (pentRows 140 141 145 155 175) else (pentRows 140 142 146 156 176)))) else (if i < 201 then (if i < 199 then (pentRows 140 143 147 157 177) else (if i < 200 then (pentRows 140 144 148 158 178) else (pentRows 141 142 149 159 179))) else (if i < 202 then (pentRows 141 143 150 160 180) else (if i < 203 then (pentRows 141 144 151 161 181) else (pentRows 142 143 152 162 182)))))
private def groupP17 (i : Nat) : List (List Nat) := (if i < 210 then (if i < 207 then (if i < 205 then (pentRows 142 144 153 163 183) else (if i < 206 then (pentRows 143 144 154 164 184) else (pentRows 145 146 149 165 185))) else (if i < 208 then (pentRows 145 147 150 166 186) else (if i < 209 then (pentRows 145 148 151 167 187) else (pentRows 146 147 152 168 188)))) else (if i < 213 then (if i < 211 then (pentRows 146 148 153 169 189) else (if i < 212 then (pentRows 147 148 154 170 190) else (pentRows 149 150 152 171 191))) else (if i < 214 then (pentRows 149 151 153 172 192) else (if i < 215 then (pentRows 150 151 154 173 193) else (pentRows 152 153 154 174 194)))))
private def groupP18 (i : Nat) : List (List Nat) := (if i < 222 then (if i < 219 then (if i < 217 then (pentRows 155 156 159 165 195) else (if i < 218 then (pentRows 155 157 160 166 196) else (pentRows 155 158 161 167 197))) else (if i < 220 then (pentRows 156 157 162 168 198) else (if i < 221 then (pentRows 156 158 163 169 199) else (pentRows 157 158 164 170 200)))) else (if i < 225 then (if i < 223 then (pentRows 159 160 162 171 201) else (if i < 224 then (pentRows 159 161 163 172 202) else (pentRows 160 161 164 173 203))) else (if i < 226 then (pentRows 162 163 164 174 204) else (if i < 227 then (pentRows 165 166 168 171 205) else (pentRows 165 167 169 172 206)))))
private def groupP19 (i : Nat) : List (List Nat) := (if i < 234 then (if i < 231 then (if i < 229 then (pentRows 166 167 170 173 207) else (if i < 230 then (pentRows 168 169 170 174 208) else (pentRows 171 172 173 174 209))) else (if i < 232 then (pentRows 175 176 179 185 195) else (if i < 233 then (pentRows 175 177 180 186 196) else (pentRows 175 178 181 187 197)))) else (if i < 237 then (if i < 235 then (pentRows 176 177 182 188 198) else (if i < 236 then (pentRows 176 178 183 189 199) else (pentRows 177 178 184 190 200))) else (if i < 238 then (pentRows 179 180 182 191 201) else (if i < 239 then (pentRows 179 181 183 192 202) else (pentRows 180 181 184 193 203)))))
private def groupP20 (i : Nat) : List (List Nat) := (if i < 246 then (if i < 243 then (if i < 241 then (pentRows 182 183 184 194 204) else (if i < 242 then (pentRows 185 186 188 191 205) else (pentRows 185 187 189 192 206))) else (if i < 244 then (pentRows 186 187 190 193 207) else (if i < 245 then (pentRows 188 189 190 194 208) else (pentRows 191 192 193 194 209)))) else (if i < 249 then (if i < 247 then (pentRows 195 196 198 201 205) else (if i < 248 then (pentRows 195 197 199 202 206) else (pentRows 196 197 200 203 207))) else (if i < 250 then (pentRows 198 199 200 204 208) else (if i < 251 then (pentRows 201 202 203 204 209) else (pentRows 205 206 207 208 209)))))
private def group (i : Nat) : List (List Nat) := (if i < 120 then (if i < 60 then (if i < 24 then (if i < 12 then (groupP0 i) else (groupP1 i)) else (if i < 36 then (groupP2 i) else (if i < 48 then (groupP3 i) else (groupP4 i)))) else (if i < 84 then (if i < 72 then (groupP5 i) else (groupP6 i)) else (if i < 96 then (groupP7 i) else (if i < 108 then (groupP8 i) else (groupP9 i))))) else (if i < 180 then (if i < 144 then (if i < 132 then (groupP10 i) else (groupP11 i)) else (if i < 156 then (groupP12 i) else (if i < 168 then (groupP13 i) else (groupP14 i)))) else (if i < 216 then (if i < 192 then (groupP15 i) else (if i < 204 then (groupP16 i) else (groupP17 i))) else (if i < 228 then (groupP18 i) else (if i < 240 then (groupP19 i) else (groupP20 i))))))
private def input9 (j : Nat) := (group (if j < 1512 then j/12 else 126+(j-1512)))[if j<1512 then j%12 else 0]?
private theorem groupOK0 (f : Col) (good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (_bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP0 i) := by
  unfold groupP0
  split
  · split
    · split
      · exact quadOK (assn f) 0 1 7 28 84 (good 0 1 2 3 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 0 2 8 29 85 (good 0 1 2 4 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 0 3 9 30 86 (good 0 1 2 5 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 0 4 10 31 87 (good 0 1 2 6 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 0 5 11 32 88 (good 0 1 2 7 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 0 6 12 33 89 (good 0 1 2 8 (by decide) (by decide) (by decide)) rfl
  · split
    · split
      · exact quadOK (assn f) 1 2 13 34 90 (good 0 1 3 4 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 1 3 14 35 91 (good 0 1 3 5 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 1 4 15 36 92 (good 0 1 3 6 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 1 5 16 37 93 (good 0 1 3 7 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 1 6 17 38 94 (good 0 1 3 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 2 3 18 39 95 (good 0 1 4 5 (by decide) (by decide) (by decide)) rfl

private theorem groupOK1 (f : Col) (good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (_bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP1 i) := by
  unfold groupP1
  split
  · split
    · split
      · exact quadOK (assn f) 2 4 19 40 96 (good 0 1 4 6 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 2 5 20 41 97 (good 0 1 4 7 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 2 6 21 42 98 (good 0 1 4 8 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 3 4 22 43 99 (good 0 1 5 6 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 3 5 23 44 100 (good 0 1 5 7 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 3 6 24 45 101 (good 0 1 5 8 (by decide) (by decide) (by decide)) rfl
  · split
    · split
      · exact quadOK (assn f) 4 5 25 46 102 (good 0 1 6 7 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 4 6 26 47 103 (good 0 1 6 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 5 6 27 48 104 (good 0 1 7 8 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 7 8 13 49 105 (good 0 2 3 4 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 7 9 14 50 106 (good 0 2 3 5 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 7 10 15 51 107 (good 0 2 3 6 (by decide) (by decide) (by decide)) rfl

private theorem groupOK2 (f : Col) (good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (_bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP2 i) := by
  unfold groupP2
  split
  · split
    · split
      · exact quadOK (assn f) 7 11 16 52 108 (good 0 2 3 7 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 7 12 17 53 109 (good 0 2 3 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 8 9 18 54 110 (good 0 2 4 5 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 8 10 19 55 111 (good 0 2 4 6 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 8 11 20 56 112 (good 0 2 4 7 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 8 12 21 57 113 (good 0 2 4 8 (by decide) (by decide) (by decide)) rfl
  · split
    · split
      · exact quadOK (assn f) 9 10 22 58 114 (good 0 2 5 6 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 9 11 23 59 115 (good 0 2 5 7 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 9 12 24 60 116 (good 0 2 5 8 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 10 11 25 61 117 (good 0 2 6 7 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 10 12 26 62 118 (good 0 2 6 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 11 12 27 63 119 (good 0 2 7 8 (by decide) (by decide) (by decide)) rfl

private theorem groupOK3 (f : Col) (good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (_bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP3 i) := by
  unfold groupP3
  split
  · split
    · split
      · exact quadOK (assn f) 13 14 18 64 120 (good 0 3 4 5 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 13 15 19 65 121 (good 0 3 4 6 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 13 16 20 66 122 (good 0 3 4 7 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 13 17 21 67 123 (good 0 3 4 8 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 14 15 22 68 124 (good 0 3 5 6 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 14 16 23 69 125 (good 0 3 5 7 (by decide) (by decide) (by decide)) rfl
  · split
    · split
      · exact quadOK (assn f) 14 17 24 70 126 (good 0 3 5 8 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 15 16 25 71 127 (good 0 3 6 7 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 15 17 26 72 128 (good 0 3 6 8 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 16 17 27 73 129 (good 0 3 7 8 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 18 19 22 74 130 (good 0 4 5 6 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 18 20 23 75 131 (good 0 4 5 7 (by decide) (by decide) (by decide)) rfl

private theorem groupOK4 (f : Col) (good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (_bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP4 i) := by
  unfold groupP4
  split
  · split
    · split
      · exact quadOK (assn f) 18 21 24 76 132 (good 0 4 5 8 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 19 20 25 77 133 (good 0 4 6 7 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 19 21 26 78 134 (good 0 4 6 8 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 20 21 27 79 135 (good 0 4 7 8 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 22 23 25 80 136 (good 0 5 6 7 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 22 24 26 81 137 (good 0 5 6 8 (by decide) (by decide) (by decide)) rfl
  · split
    · split
      · exact quadOK (assn f) 23 24 27 82 138 (good 0 5 7 8 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 25 26 27 83 139 (good 0 6 7 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 28 29 34 49 140 (good 1 2 3 4 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 28 30 35 50 141 (good 1 2 3 5 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 28 31 36 51 142 (good 1 2 3 6 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 28 32 37 52 143 (good 1 2 3 7 (by decide) (by decide) (by decide)) rfl

private theorem groupOK5 (f : Col) (good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (_bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP5 i) := by
  unfold groupP5
  split
  · split
    · split
      · exact quadOK (assn f) 28 33 38 53 144 (good 1 2 3 8 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 29 30 39 54 145 (good 1 2 4 5 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 29 31 40 55 146 (good 1 2 4 6 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 29 32 41 56 147 (good 1 2 4 7 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 29 33 42 57 148 (good 1 2 4 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 30 31 43 58 149 (good 1 2 5 6 (by decide) (by decide) (by decide)) rfl
  · split
    · split
      · exact quadOK (assn f) 30 32 44 59 150 (good 1 2 5 7 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 30 33 45 60 151 (good 1 2 5 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 31 32 46 61 152 (good 1 2 6 7 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 31 33 47 62 153 (good 1 2 6 8 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 32 33 48 63 154 (good 1 2 7 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 34 35 39 64 155 (good 1 3 4 5 (by decide) (by decide) (by decide)) rfl

private theorem groupOK6 (f : Col) (good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (_bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP6 i) := by
  unfold groupP6
  split
  · split
    · split
      · exact quadOK (assn f) 34 36 40 65 156 (good 1 3 4 6 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 34 37 41 66 157 (good 1 3 4 7 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 34 38 42 67 158 (good 1 3 4 8 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 35 36 43 68 159 (good 1 3 5 6 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 35 37 44 69 160 (good 1 3 5 7 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 35 38 45 70 161 (good 1 3 5 8 (by decide) (by decide) (by decide)) rfl
  · split
    · split
      · exact quadOK (assn f) 36 37 46 71 162 (good 1 3 6 7 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 36 38 47 72 163 (good 1 3 6 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 37 38 48 73 164 (good 1 3 7 8 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 39 40 43 74 165 (good 1 4 5 6 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 39 41 44 75 166 (good 1 4 5 7 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 39 42 45 76 167 (good 1 4 5 8 (by decide) (by decide) (by decide)) rfl

private theorem groupOK7 (f : Col) (good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (_bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP7 i) := by
  unfold groupP7
  split
  · split
    · split
      · exact quadOK (assn f) 40 41 46 77 168 (good 1 4 6 7 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 40 42 47 78 169 (good 1 4 6 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 41 42 48 79 170 (good 1 4 7 8 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 43 44 46 80 171 (good 1 5 6 7 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 43 45 47 81 172 (good 1 5 6 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 44 45 48 82 173 (good 1 5 7 8 (by decide) (by decide) (by decide)) rfl
  · split
    · split
      · exact quadOK (assn f) 46 47 48 83 174 (good 1 6 7 8 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 49 50 54 64 175 (good 2 3 4 5 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 49 51 55 65 176 (good 2 3 4 6 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 49 52 56 66 177 (good 2 3 4 7 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 49 53 57 67 178 (good 2 3 4 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 50 51 58 68 179 (good 2 3 5 6 (by decide) (by decide) (by decide)) rfl

private theorem groupOK8 (f : Col) (good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (_bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP8 i) := by
  unfold groupP8
  split
  · split
    · split
      · exact quadOK (assn f) 50 52 59 69 180 (good 2 3 5 7 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 50 53 60 70 181 (good 2 3 5 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 51 52 61 71 182 (good 2 3 6 7 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 51 53 62 72 183 (good 2 3 6 8 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 52 53 63 73 184 (good 2 3 7 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 54 55 58 74 185 (good 2 4 5 6 (by decide) (by decide) (by decide)) rfl
  · split
    · split
      · exact quadOK (assn f) 54 56 59 75 186 (good 2 4 5 7 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 54 57 60 76 187 (good 2 4 5 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 55 56 61 77 188 (good 2 4 6 7 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 55 57 62 78 189 (good 2 4 6 8 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 56 57 63 79 190 (good 2 4 7 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 58 59 61 80 191 (good 2 5 6 7 (by decide) (by decide) (by decide)) rfl

private theorem groupOK9 (f : Col) (good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (_bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP9 i) := by
  unfold groupP9
  split
  · split
    · split
      · exact quadOK (assn f) 58 60 62 81 192 (good 2 5 6 8 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 59 60 63 82 193 (good 2 5 7 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 61 62 63 83 194 (good 2 6 7 8 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 64 65 68 74 195 (good 3 4 5 6 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 64 66 69 75 196 (good 3 4 5 7 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 64 67 70 76 197 (good 3 4 5 8 (by decide) (by decide) (by decide)) rfl
  · split
    · split
      · exact quadOK (assn f) 65 66 71 77 198 (good 3 4 6 7 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 65 67 72 78 199 (good 3 4 6 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 66 67 73 79 200 (good 3 4 7 8 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 68 69 71 80 201 (good 3 5 6 7 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 68 70 72 81 202 (good 3 5 6 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 69 70 73 82 203 (good 3 5 7 8 (by decide) (by decide) (by decide)) rfl

private theorem groupOK10 (f : Col) (good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP10 i) := by
  unfold groupP10
  split
  · split
    · split
      · exact quadOK (assn f) 71 72 73 83 204 (good 3 6 7 8 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 74 75 77 80 205 (good 4 5 6 7 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 74 76 78 81 206 (good 4 5 6 8 (by decide) (by decide) (by decide)) rfl
    · split
      · exact quadOK (assn f) 75 76 79 82 207 (good 4 5 7 8 (by decide) (by decide) (by decide)) rfl
      · split
        · exact quadOK (assn f) 77 78 79 83 208 (good 4 6 7 8 (by decide) (by decide) (by decide)) rfl
        · exact quadOK (assn f) 80 81 82 83 209 (good 5 6 7 8 (by decide) (by decide) (by decide)) rfl
  · split
    · split
      · exact pentOK (assn f) 84 85 90 105 140 (pent_excluded f bad 0 1 2 3 4 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 84 86 91 106 141 (pent_excluded f bad 0 1 2 3 5 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 84 87 92 107 142 (pent_excluded f bad 0 1 2 3 6 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 84 88 93 108 143 (pent_excluded f bad 0 1 2 3 7 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 84 89 94 109 144 (pent_excluded f bad 0 1 2 3 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 85 86 95 110 145 (pent_excluded f bad 0 1 2 4 5 (by decide) (by decide) (by decide) (by decide))

private theorem groupOK11 (f : Col) (_good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP11 i) := by
  unfold groupP11
  split
  · split
    · split
      · exact pentOK (assn f) 85 87 96 111 146 (pent_excluded f bad 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 85 88 97 112 147 (pent_excluded f bad 0 1 2 4 7 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 85 89 98 113 148 (pent_excluded f bad 0 1 2 4 8 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 86 87 99 114 149 (pent_excluded f bad 0 1 2 5 6 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 86 88 100 115 150 (pent_excluded f bad 0 1 2 5 7 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 86 89 101 116 151 (pent_excluded f bad 0 1 2 5 8 (by decide) (by decide) (by decide) (by decide))
  · split
    · split
      · exact pentOK (assn f) 87 88 102 117 152 (pent_excluded f bad 0 1 2 6 7 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 87 89 103 118 153 (pent_excluded f bad 0 1 2 6 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 88 89 104 119 154 (pent_excluded f bad 0 1 2 7 8 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 90 91 95 120 155 (pent_excluded f bad 0 1 3 4 5 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 90 92 96 121 156 (pent_excluded f bad 0 1 3 4 6 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 90 93 97 122 157 (pent_excluded f bad 0 1 3 4 7 (by decide) (by decide) (by decide) (by decide))

private theorem groupOK12 (f : Col) (_good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP12 i) := by
  unfold groupP12
  split
  · split
    · split
      · exact pentOK (assn f) 90 94 98 123 158 (pent_excluded f bad 0 1 3 4 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 91 92 99 124 159 (pent_excluded f bad 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 91 93 100 125 160 (pent_excluded f bad 0 1 3 5 7 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 91 94 101 126 161 (pent_excluded f bad 0 1 3 5 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 92 93 102 127 162 (pent_excluded f bad 0 1 3 6 7 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 92 94 103 128 163 (pent_excluded f bad 0 1 3 6 8 (by decide) (by decide) (by decide) (by decide))
  · split
    · split
      · exact pentOK (assn f) 93 94 104 129 164 (pent_excluded f bad 0 1 3 7 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 95 96 99 130 165 (pent_excluded f bad 0 1 4 5 6 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 95 97 100 131 166 (pent_excluded f bad 0 1 4 5 7 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 95 98 101 132 167 (pent_excluded f bad 0 1 4 5 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 96 97 102 133 168 (pent_excluded f bad 0 1 4 6 7 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 96 98 103 134 169 (pent_excluded f bad 0 1 4 6 8 (by decide) (by decide) (by decide) (by decide))

private theorem groupOK13 (f : Col) (_good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP13 i) := by
  unfold groupP13
  split
  · split
    · split
      · exact pentOK (assn f) 97 98 104 135 170 (pent_excluded f bad 0 1 4 7 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 99 100 102 136 171 (pent_excluded f bad 0 1 5 6 7 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 99 101 103 137 172 (pent_excluded f bad 0 1 5 6 8 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 100 101 104 138 173 (pent_excluded f bad 0 1 5 7 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 102 103 104 139 174 (pent_excluded f bad 0 1 6 7 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 105 106 110 120 175 (pent_excluded f bad 0 2 3 4 5 (by decide) (by decide) (by decide) (by decide))
  · split
    · split
      · exact pentOK (assn f) 105 107 111 121 176 (pent_excluded f bad 0 2 3 4 6 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 105 108 112 122 177 (pent_excluded f bad 0 2 3 4 7 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 105 109 113 123 178 (pent_excluded f bad 0 2 3 4 8 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 106 107 114 124 179 (pent_excluded f bad 0 2 3 5 6 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 106 108 115 125 180 (pent_excluded f bad 0 2 3 5 7 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 106 109 116 126 181 (pent_excluded f bad 0 2 3 5 8 (by decide) (by decide) (by decide) (by decide))

private theorem groupOK14 (f : Col) (_good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP14 i) := by
  unfold groupP14
  split
  · split
    · split
      · exact pentOK (assn f) 107 108 117 127 182 (pent_excluded f bad 0 2 3 6 7 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 107 109 118 128 183 (pent_excluded f bad 0 2 3 6 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 108 109 119 129 184 (pent_excluded f bad 0 2 3 7 8 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 110 111 114 130 185 (pent_excluded f bad 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 110 112 115 131 186 (pent_excluded f bad 0 2 4 5 7 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 110 113 116 132 187 (pent_excluded f bad 0 2 4 5 8 (by decide) (by decide) (by decide) (by decide))
  · split
    · split
      · exact pentOK (assn f) 111 112 117 133 188 (pent_excluded f bad 0 2 4 6 7 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 111 113 118 134 189 (pent_excluded f bad 0 2 4 6 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 112 113 119 135 190 (pent_excluded f bad 0 2 4 7 8 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 114 115 117 136 191 (pent_excluded f bad 0 2 5 6 7 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 114 116 118 137 192 (pent_excluded f bad 0 2 5 6 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 115 116 119 138 193 (pent_excluded f bad 0 2 5 7 8 (by decide) (by decide) (by decide) (by decide))

private theorem groupOK15 (f : Col) (_good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP15 i) := by
  unfold groupP15
  split
  · split
    · split
      · exact pentOK (assn f) 117 118 119 139 194 (pent_excluded f bad 0 2 6 7 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 120 121 124 130 195 (pent_excluded f bad 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 120 122 125 131 196 (pent_excluded f bad 0 3 4 5 7 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 120 123 126 132 197 (pent_excluded f bad 0 3 4 5 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 121 122 127 133 198 (pent_excluded f bad 0 3 4 6 7 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 121 123 128 134 199 (pent_excluded f bad 0 3 4 6 8 (by decide) (by decide) (by decide) (by decide))
  · split
    · split
      · exact pentOK (assn f) 122 123 129 135 200 (pent_excluded f bad 0 3 4 7 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 124 125 127 136 201 (pent_excluded f bad 0 3 5 6 7 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 124 126 128 137 202 (pent_excluded f bad 0 3 5 6 8 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 125 126 129 138 203 (pent_excluded f bad 0 3 5 7 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 127 128 129 139 204 (pent_excluded f bad 0 3 6 7 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 130 131 133 136 205 (pent_excluded f bad 0 4 5 6 7 (by decide) (by decide) (by decide) (by decide))

private theorem groupOK16 (f : Col) (_good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP16 i) := by
  unfold groupP16
  split
  · split
    · split
      · exact pentOK (assn f) 130 132 134 137 206 (pent_excluded f bad 0 4 5 6 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 131 132 135 138 207 (pent_excluded f bad 0 4 5 7 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 133 134 135 139 208 (pent_excluded f bad 0 4 6 7 8 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 136 137 138 139 209 (pent_excluded f bad 0 5 6 7 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 140 141 145 155 175 (pent_excluded f bad 1 2 3 4 5 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 140 142 146 156 176 (pent_excluded f bad 1 2 3 4 6 (by decide) (by decide) (by decide) (by decide))
  · split
    · split
      · exact pentOK (assn f) 140 143 147 157 177 (pent_excluded f bad 1 2 3 4 7 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 140 144 148 158 178 (pent_excluded f bad 1 2 3 4 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 141 142 149 159 179 (pent_excluded f bad 1 2 3 5 6 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 141 143 150 160 180 (pent_excluded f bad 1 2 3 5 7 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 141 144 151 161 181 (pent_excluded f bad 1 2 3 5 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 142 143 152 162 182 (pent_excluded f bad 1 2 3 6 7 (by decide) (by decide) (by decide) (by decide))

private theorem groupOK17 (f : Col) (_good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP17 i) := by
  unfold groupP17
  split
  · split
    · split
      · exact pentOK (assn f) 142 144 153 163 183 (pent_excluded f bad 1 2 3 6 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 143 144 154 164 184 (pent_excluded f bad 1 2 3 7 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 145 146 149 165 185 (pent_excluded f bad 1 2 4 5 6 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 145 147 150 166 186 (pent_excluded f bad 1 2 4 5 7 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 145 148 151 167 187 (pent_excluded f bad 1 2 4 5 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 146 147 152 168 188 (pent_excluded f bad 1 2 4 6 7 (by decide) (by decide) (by decide) (by decide))
  · split
    · split
      · exact pentOK (assn f) 146 148 153 169 189 (pent_excluded f bad 1 2 4 6 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 147 148 154 170 190 (pent_excluded f bad 1 2 4 7 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 149 150 152 171 191 (pent_excluded f bad 1 2 5 6 7 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 149 151 153 172 192 (pent_excluded f bad 1 2 5 6 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 150 151 154 173 193 (pent_excluded f bad 1 2 5 7 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 152 153 154 174 194 (pent_excluded f bad 1 2 6 7 8 (by decide) (by decide) (by decide) (by decide))

private theorem groupOK18 (f : Col) (_good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP18 i) := by
  unfold groupP18
  split
  · split
    · split
      · exact pentOK (assn f) 155 156 159 165 195 (pent_excluded f bad 1 3 4 5 6 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 155 157 160 166 196 (pent_excluded f bad 1 3 4 5 7 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 155 158 161 167 197 (pent_excluded f bad 1 3 4 5 8 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 156 157 162 168 198 (pent_excluded f bad 1 3 4 6 7 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 156 158 163 169 199 (pent_excluded f bad 1 3 4 6 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 157 158 164 170 200 (pent_excluded f bad 1 3 4 7 8 (by decide) (by decide) (by decide) (by decide))
  · split
    · split
      · exact pentOK (assn f) 159 160 162 171 201 (pent_excluded f bad 1 3 5 6 7 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 159 161 163 172 202 (pent_excluded f bad 1 3 5 6 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 160 161 164 173 203 (pent_excluded f bad 1 3 5 7 8 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 162 163 164 174 204 (pent_excluded f bad 1 3 6 7 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 165 166 168 171 205 (pent_excluded f bad 1 4 5 6 7 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 165 167 169 172 206 (pent_excluded f bad 1 4 5 6 8 (by decide) (by decide) (by decide) (by decide))

private theorem groupOK19 (f : Col) (_good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP19 i) := by
  unfold groupP19
  split
  · split
    · split
      · exact pentOK (assn f) 166 167 170 173 207 (pent_excluded f bad 1 4 5 7 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 168 169 170 174 208 (pent_excluded f bad 1 4 6 7 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 171 172 173 174 209 (pent_excluded f bad 1 5 6 7 8 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 175 176 179 185 195 (pent_excluded f bad 2 3 4 5 6 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 175 177 180 186 196 (pent_excluded f bad 2 3 4 5 7 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 175 178 181 187 197 (pent_excluded f bad 2 3 4 5 8 (by decide) (by decide) (by decide) (by decide))
  · split
    · split
      · exact pentOK (assn f) 176 177 182 188 198 (pent_excluded f bad 2 3 4 6 7 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 176 178 183 189 199 (pent_excluded f bad 2 3 4 6 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 177 178 184 190 200 (pent_excluded f bad 2 3 4 7 8 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 179 180 182 191 201 (pent_excluded f bad 2 3 5 6 7 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 179 181 183 192 202 (pent_excluded f bad 2 3 5 6 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 180 181 184 193 203 (pent_excluded f bad 2 3 5 7 8 (by decide) (by decide) (by decide) (by decide))

private theorem groupOK20 (f : Col) (_good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (bad : ¬witness f) (i : Nat) : satRows (assn f) (groupP20 i) := by
  unfold groupP20
  split
  · split
    · split
      · exact pentOK (assn f) 182 183 184 194 204 (pent_excluded f bad 2 3 6 7 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 185 186 188 191 205 (pent_excluded f bad 2 4 5 6 7 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 185 187 189 192 206 (pent_excluded f bad 2 4 5 6 8 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 186 187 190 193 207 (pent_excluded f bad 2 4 5 7 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 188 189 190 194 208 (pent_excluded f bad 2 4 6 7 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 191 192 193 194 209 (pent_excluded f bad 2 5 6 7 8 (by decide) (by decide) (by decide) (by decide))
  · split
    · split
      · exact pentOK (assn f) 195 196 198 201 205 (pent_excluded f bad 3 4 5 6 7 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 195 197 199 202 206 (pent_excluded f bad 3 4 5 6 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 196 197 200 203 207 (pent_excluded f bad 3 4 5 7 8 (by decide) (by decide) (by decide) (by decide))
    · split
      · exact pentOK (assn f) 198 199 200 204 208 (pent_excluded f bad 3 4 6 7 8 (by decide) (by decide) (by decide) (by decide))
      · split
        · exact pentOK (assn f) 201 202 203 204 209 (pent_excluded f bad 3 5 6 7 8 (by decide) (by decide) (by decide) (by decide))
        · exact pentOK (assn f) 205 206 207 208 209 (pent_excluded f bad 4 5 6 7 8 (by decide) (by decide) (by decide) (by decide))

private theorem groupOK (f : Col) (good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d)) (bad : ¬witness f) (i : Nat) : satRows (assn f) (group i) := by
  unfold group
  split
  · split
    · split
      · split
        · exact groupOK0 f good bad i
        · exact groupOK1 f good bad i
      · split
        · exact groupOK2 f good bad i
        · split
          · exact groupOK3 f good bad i
          · exact groupOK4 f good bad i
    · split
      · split
        · exact groupOK5 f good bad i
        · exact groupOK6 f good bad i
      · split
        · exact groupOK7 f good bad i
        · split
          · exact groupOK8 f good bad i
          · exact groupOK9 f good bad i
  · split
    · split
      · split
        · exact groupOK10 f good bad i
        · exact groupOK11 f good bad i
      · split
        · exact groupOK12 f good bad i
        · split
          · exact groupOK13 f good bad i
          · exact groupOK14 f good bad i
    · split
      · split
        · exact groupOK15 f good bad i
        · split
          · exact groupOK16 f good bad i
          · exact groupOK17 f good bad i
      · split
        · exact groupOK18 f good bad i
        · split
          · exact groupOK19 f good bad i
          · exact groupOK20 f good bad i

private theorem input_sat (f : Col)
    (good : ∀ a b c d, a<b → b<c → c<d → regular (f a b c) (f a b d) (f a c d) (f b c d))
    (bad : ¬witness f) (j : Nat) (d : List Nat) (h : input9 j = some d) :
    ∃ l ∈ d, lit (assn f) l = true := by
  exact List.any_eq_true.mp (List.all_eq_true.mp (groupOK f good bad _) d (List.mem_of_getElem? h))

private def pack0 (i : Nat) : Nat × Nat := (#[
(2607322710532,1417847042),
(2779457209604,1480769282),
(5075780227,1419944450),
(5411587459,1482866690),
(2779726433028,1531107074),
(6739550945924,1418895746),
(4673913347,1416798338),
(5177953155,1533204482),
(7049125186436,1532155778),
(900000706714034718087,774283418218799480965),
(5378098435,1479720578),
(721933128781088646,1728264066),
(6911685444996,1481817986),
(5211441923,1530058370),
(2606650308612,1292002562),
(5376785155,1353876098)
] : Array (Nat × Nat))[i%16]!
private def pack1 (i : Nat) : Nat × Nat := (#[
(5074466947,1294099970),
(2761604873092,1355973506),
(4470092931,1180839938),
(2667031574532,1317171458),
(236507034521102456232030473,7636724998675821761799046),
(4138155779,1394775810),
(4809246979,1520620290),
(5211901699,1570958082),
(3532865283,1268931330),
(1712761288068,1193425282),
(3330749699,1191327490),
(3345236867,1745043330),
(5379609219,1578299010),
(6773172227076,1422042754),
(3364631939,1223837826),
(4606153091,1491257346)
] : Array (Nat × Nat))[i%16]!
private def pack2 (i : Nat) : Nat × Nat := (#[
(6773172683524,1424179586),
(5379412739,1576222978),
(645098482397041542,10404151639427),
(1816241326468,1270038274),
(2674160118020,1059191810),
(5072169987,1036120322),
(5576404483,1137843330),
(4871562883,1004657666),
(2116264402948,857840642),
(34109071837693444877116448010,13675943523331),
(4133232771,866228738),
(5206976899,1067579906),
(5880890010372,1097992706),
(5396124419,12886654271747),
(4469241859,1176714242),
(51764559344866454900290957706,935137006458453049477)
] : Array (Nat × Nat))[i%16]!
private def pack3 (i : Nat) : Nat × Nat := (#[
(385694035921682518151,3736376117272414643742669096651800073),
(4267712899,891397634),
(144300187752069987311752,506457405704191507416420744120584),
(70247813318513031759208329,7518434651140374662313350),
(2255169027,765553154),
(5069412099,595664642),
(1687097475,551617538),
(689958946180,173035394),
(2200921506559489540239982730,12996607739267),
(308222467,249591042),
(1919623427,763456258),
(2218605699,851547394),
(5405546371,664877570),
(336140675,234909570),
(341317507,202400642),
(3131518723,1140989698)
] : Array (Nat × Nat))[i%16]!
private def pack4 (i : Nat) : Nat × Nat := (#[
(2889693827,828475650),
(420252450201484678,33989040305226519504177471494676130434570),
(1712602371,420529794),
(44339933776244405754302247434,935676875901903190533),
(2956802947,841060098),
(2084123523,738287362),
(86594335744984790374167433,5313596243184953400109446),
(274602627,244347522),
(29123037313892121391911616010,879106872892495863301),
(1273874270935255051228724920587,19434778555068420),
(340459907,119552514),
(18537362389519695879,66191106476119176579302644871),
(339804291,56630274),
(4273754056938022913638537,7163843235699222319730950),
(3670403,5243266),
(90618312662581254,1799575682)
] : Array (Nat × Nat))[i%16]!
private def pack5 (i : Nat) : Nat × Nat := (#[
(238813187,28315266),
(4638323715,1209156482),
(8402573484684471051144,479499130361583382296237886888712),
(235021059,93334402),
(5544295427,1377997314),
(23475724682935550714894915352075,1760714242),
(46825209528689881919547848330,13994311182723),
(4973737475,1276272258),
(268503683,46142850),
(3158515459,871473154),
(4195715,53484162),
(3968545411,1218593538),
(48038321781455052290956280330,13916864425219),
(19820547929917171881804513034,13108680696835),
(32254261619044353613588742666,9485102002179),
(5343889667,1470282498)
] : Array (Nat × Nat))[i%16]!
private def pack6 (i : Nat) : Nat × Nat := (#[
(4674898179,1508035842),
(49301089671914494977466450698,14037415012099),
(159608665671250785410440,61320963427448214596423467143),
(3325631747,713118466),
(228796874402191741063,1821598722),
(2322611248260,1001940241574111885573),
(3359448067,722556802),
(3359113219,17690050086838352560572389639876485887611469865117197),
(13871862494409393415,4005925503632769425440209635784022665),
(207095171,206594434),
(4438576387,1441967234),
(62984710875018401423378185,7504518316553511732630662),
(4670894723,1216569474),
(3191750147,869376130),
(2153856771,881960578),
(2958905347,1102187138)
] : Array (Nat × Nat))[i%16]!
private def pack7 (i : Nat) : Nat × Nat := (#[
(22325266589494744487909868554,13152133640195),
(1260234715251205,284365619313875280576396113645810371245818763),
(22301273188654811975992295690,13125885734915),
(90761713197159383140093321,4591069547591033432519942),
(2757577987,1064433794),
(92276726062197167795080,1839426690),
(1516866776708,8288356229426080433433990),
(1375677186564,151013762),
(1580819698436,2206639926246795529832532058606827637296865504652),
(5413228803,1581445378),
(2770632004484,118656041129030788),
(3087538563,231763074),
(3087553283,1846767362),
(101872507347162863572488,59460530142959228347744327047),
(4968420995,584127618),
(744318316929760134,34563048878872691217088217900577777214218)
] : Array (Nat × Nat))[i%16]!
private def pack8 (i : Nat) : Nat × Nat := (#[
(51770917933905430632700263818,13968469039491),
(4469567875,1178814978),
(93244610650144113527961737,7650871356303989122757510),
(45881912728471393112682542986,932214029382514270085),
(25426525840762532331305639178,13701725911555),
(1563221782354514214847126922,871627023922598335621),
(49674928493963648075185417,1020423362516657240069),
(5175457539,1314025602),
(108969889763850976107784,1859352066),
(4225862250712935535364582002319679966619435298825176090962571799,1392116958607869172550230194506104594652339274122044409755919),
(5545603715,19001249886999531864536201819088652488176261878997773),
(4225862250712935534662076010257711015226173754237231196979331223,4397961956722593459993414981299428489),
(4225862250712935543213039711878458654821345026088807210348781591,44118185694375209341732563836206860078151212644509129303974867463151207021951636),
(3091079299,1761712514),
(4894756841708864404520969,7197114800884938607433862),
(16120385172702543423511656615747294062886600593897379208981,28184323825596195418800178485538102510425348402358650952789375505189159835624264188234447511)
] : Array (Nat × Nat))[i%16]!
private def pack9 (i : Nat) : Nat × Nat := (#[
(31485127290434655124046204327631433716575391784955818772,33732288975349970777937514907556623008266),
(3364369283,1200765826),
(65969524000563838026704662777322891394639414927041555,529316375792645798789),
(3096388739,992073474),
(120106228982676144119438954458043661021720346243602,1871936514),
(27325442758830229076092339594,6311943833563224301609064111260052006450021473095935470101634130494919765523),
(61494389239130185789152742824315547690347006911722003,1868790658),
(2355436675,727800066),
(25433563389220170446915122954,47514142028036484),
(120105961373733764023629439398316729724517899050770,1186396364898464831934752038425891889272465997716105442895247),
(234581955808073757858651303288839591830901502737,49203137955869444),
(8087927549496965477681541386,12988245430275),
(55959973607755846786136151407867641034771070924690,18907576753897763007980155963008859706270300600542605),
(4402394883,1168255490),
(3193393850381734843391100742133982316430,3217563496852788487652170132186335644715400664037105905587579394989226196085286970189948977027282471924399286976546045109244655537035546379167412111051295285091183184196171690157),
(213470358306354638357307995464994458300201488,126251398295945604)
] : Array (Nat × Nat))[i%16]!
private def pack10 (i : Nat) : Nat × Nat := (#[
(726550501855673734,34690896208276839460872942077846348853130),
(5409946883,1352828674),
(2771570212740,15446095135619),
(5413223043,14252589155203),
(1590478143889395918024354570203046413,3306692499072178706243590),
(2625708675,903982338),
(1590478110531955663375441526593621261,121471194667951492),
(1216417155,463526658),
(120106227719678434452248180310524848761624609561618,4650273614013730545128409885916175241),
(263093458544395159546024027789641149838610670353,1876133634),
(851092563478838090264769535127748486709647,1041724830546354366341),
(49674759019710892569600521,7579896332968440980681094),
(4771429763,1238518914),
(327754618356556116743,1005973843969782668293),
(415484988260144033090095565272377417349007,58493866725856894510468049543),
(223108808960596532325767315695339799686588932881,4276101260378820684616302121046879018170773812000457697860094539207761589591131547059117787125016782089112466968256776420578720)
] : Array (Nat × Nat))[i%16]!
private def pack11 (i : Nat) : Nat × Nat := (#[
(11144708177569792641487012234,880286602199640846085),
(4894756842412687675949321,7244172449243116489158790),
(223108808960596532334367745017356027639995114513,95518777043259830114923888101346568942959509019599313074023265593233),
(435759392501165102215562001987023491484365456,1257072100135900629237416838858853819886954540207415931037583),
(47323020484166453626348169,7565734449532496616064390),
(2689147395,909226498),
(174913519195916031467400,1907592450),
(687577699460229,1049222542138418521989),
(2621907459,897690498),
(180017931567308678023,1045705582313257275141),
(1250799976586245,1044019616282360121605),
(17682385793993759209948918154,12988697314179),
(16120435947784358631195964475251242956706264928764274751253,34456456152356049490686361285249532656010),
(3431085955,1158818690),
(61778840548234921711841545,114006850026049924),
(1662290163080502114311822442215254794894,589398968144548357972558334276173537549042419824872118109988467648837402565867819500591828699276711879415344250036852741535)
] : Array (Nat × Nat))[i%16]!
private def pack12 (i : Nat) : Nat × Nat := (#[
(1917071747,715351170),
(189494813898725146887,127308810685642756),
(11543228391360233607,1020912766473367201925),
(851304995753186512184922266772206347230607,20812948259690743167811576643473802262331728420106381),
(435759392510575146254158071101477629963417360,8377915726902947470239622),
(189494813897654279431,15239339931011),
(809382090645253,8406282856669699621744774),
(458170495534227838485692966342625642691184400,7628773857838016124741926457252777050752884800540743839304036281807753044385616517786003177182425837889878565810461),
(6342716483423013331418615065484684,116105151963163958344146672713593366905118688333590963598),
(2688163715,783382018),
(2771571917956,1845674498),
(435759392510575146254158289914223822476164368,169452218786743571544606123004444146796197434309543606798),
(67250338404922857791931273,1166242946),
(851092569571166874961639696448447960068623,97004018083678121225323505293678077245299692608450942302123936943889),
(7163200866434179578011228924420620,1013524575403159111722595895877606463744181302666385343817263496265243973226377083993791715696935251417141308956),
(205980035,94383618)
] : Array (Nat × Nat))[i%16]!
private def pack13 (i : Nat) : Nat × Nat := (#[
(46478543891203515761259721354,2633583719407076487710554438887739494114134290572),
(7163200866434179578011226707866380,8826672322453670103114653685977019997263700592906890805273390608),
(3899077123,1869757442),
(837129037504501362289610048535172591225815056,286961893801878317368961403435910913268492802106351316525964891003836697175228767856070260183056775826338677184781135098112425064635426),
(415687141188976902,11795809145731),
(13990626692254256988303177163787,53560216828265925295800244656836441830659570644644591071842260562277850956394004),
(352092780347270278,99234027282857092),
(53370005387322452500546185,795091227291580806778652948444879531293642539776278577345059886146481682),
(104238291772114165040136,1208357027579754168083186365377912855043807311725469510102543),
(203590413617410478599,24568795554070223221373846419645999322721803),
(301997827,42996610),
(47249979140723957600813065,71808499054264282933371201415),
(1283657091,476111106),
(120106647121648621760959642090337202873287156052754,2629299348604739340330083409493679336656662142220),
(1013385859,293637890),
(4775627139,1515376770)
] : Array (Nat × Nat))[i%16]!
private def pack14 (i : Nat) : Nat × Nat := (#[
(1582973211396,2299463308703759347104923403307100958860830168460),
(234583292692677552552999210160897725969228373777,38329130951588010736135556394520013937930),
(61494602945975209003967090590930260846420919134322835,35360962013102198102449162016894053205346181721675226254),
(435759395620419060971308540684065270949356048,684195639703906002178931053275981838520463629700977313015871450992844306),
(180244366228957954055,434782097793555228549),
(198500718907144347527,3948858703037764971185431871623290505),
(105633869550453451200224076942575286361924723618578,70722879299202850003453448199),
(82344200098612300307706761,7636701364418785645394822),
(401470881837723315748134366172579240501182864,131449527174433668),
(37290243,8389378),
(1276458883,343975682),
(180522993145909950343,6323465975555),
(435759395334687104176614935324130863140970128,806707327193657637712555213823089915862768105499482325117615839351255826),
(435759395334687104176614935324130863140976400,807171442146218228764403038614943304489167017568624902265094819264309522),
(2416509187,105918850),
(851092569571130978459586993523564982322959,429701925600535770412331680618085477512207096750957551386511357193422729930757873173)
] : Array (Nat × Nat))[i%16]!
private def pack15 (i : Nat) : Nat × Nat := (#[
(3106402557843093780999808629617548,1889762178),
(496429885478743025729998554891,1880097922),
(42173853372195386082041873930,14054632637699),
(212178180076056555527,2104780529155),
(4733081603,534839554),
(1241984787494277,270577375368405365670959995155886381264308491),
(4737807619,1229080834),
(509937923,285247234),
(1739898959236,1976806786),
(1107784422201794017136649841132867435143384140603713216120471456324633,180664942314352178562500160426519279618024029900817659662),
(7849943350765763453542071081320388654492366522752995366352790,39177967668005181686200826176191819062922),
(3413635092968871931395071739491661581,128930779754627460),
(175041745623673716748808,15823855066755),
(101682679812916123783,5712990257155),
(645470211,408995074),
(510331907,323000578)
] : Array (Nat × Nat))[i%16]!
private def pack16 (i : Nat) : Nat × Nat := (#[
(341837443,256932226),
(25470953318607817169500917514,931055903871995144581),
(5178281859,1561520770),
(722865348432645,73314150443786477152638203911),
(190460940467808060393864,8878885538685974457009286),
(428610067207408383378370612766198047689552839953,12137085481669239576535237735793745928060203713575583902560606480),
(1635017651395448239816262013223497022194703,246161986683721484137239616838573160962615634066414789856321533095542178020836194536254407366936),
(5413225603,12113737379843),
(6237097364026825865998313954252231693,2198256413757496810233639918815966138399815031052),
(1285166211,621881218),
(1747781728898566607780747555532830015630,21782280645840499813507862489531216303579385226835853),
(3246660497936748422468174265535302925,29190578171904747102528520074893609210943949319134451578973948477910477731124927343367534487),
(3246660474766605839589228496432738829,1918082050),
(12388118131934118775291325002507,4385278823877951237204930526368098185),
(6342716483498571203625951936249868,407101426955333098245),
(6341133785032711762633152862373644,71396478681906884598418341192112450706837432743346733980442810120124746034337273085769066724880301199539951538294470558)
] : Array (Nat × Nat))[i%16]!
private def pack17 (i : Nat) : Nat × Nat := (#[
(3106402624938331518960849549407116,125905164346555268),
(435759392510575179690628392403881160897606160,1022197926575975131141),
(203590413617410474631,337016356896644181620876269527893036284269108584865847157980807165460336574067944132939211184105715923006137636428268655327772455188386),
(2619671043,143671938),
(676228808275545350,16434549989251),
(352037890463891974,32689808003324998602145768550985714755082),
(2668492702084,2333792353795820503011866083118419167280279797260),
(385793115009261973895,534047454379615649747793910906248),
(48510667903127906015850761,7475935076479642203558278),
(699529350968390022,74168204218114682059541921415),
(184792844574019165191,134973230660300804),
(104400643,4195586),
(171573251,17827714),
(53459222660,2163719872322679499964227612830868282345393442828),
(190460971631711593645320,8052376302798159324886662),
(198500711947485322759,3948749380746281731648504752235371401)
] : Array (Nat × Nat))[i%16]!
private def pack18 (i : Nat) : Nat × Nat := (#[
(46520555492869576279159159562,13977107202819),
(13990626692253761330215642660875,49392132477455252688907980081367553291554908883088327795582723344966787781586452),
(3667558843614170010296148889043877261,3431035497689478528213628479719934981216903889085380529121535377830354262526138501000726),
(201399939,33558274),
(202190083,217081986),
(3665377539,1304587650),
(81731476346399664982281353,113937709905724804),
(1211190275,605102722),
(46671360824029972999394380810,14063260328707),
(180942249010205295458696,5507393128888619552088710),
(5140986115,2024959234),
(13990626692253761330784959340299,256960149411759214953317494893443469577206588514772858844810159888921782750437082123096697048602713919255688940498618394156537414694931764814164298859791039051831310559925530717034081839),
(27325442758308127599189373706,113677588967055322598741692974997341542392767383103631144425569351295419374512613363214801343638411707379227),
(699529350967932678,16485245500931),
(53370005387320561717166729,2444332116767375574601373656715216355197900701759342346834782416688550329493646022524182),
(4805049603,1243762434)
] : Array (Nat × Nat))[i%16]!
private def pack19 (i : Nat) : Nat × Nat := (#[
(45904912380472971222366107530,85626678178889895970939012103362868791697468467735253994341037981201),
(1471288804455301,155753879792830107271672494982311715099434061007702670862),
(92649522057314630057279625,16596910424195),
(47323598372506984588984329,112738048193826564),
(180956097768192636829832,2038606338),
(91155001505612730280919049,114853336766952964),
(325579794821623263623,1155779842),
(690293211903767174,16734424812291),
(4335022595,1151477250),
(1242470460109189,2044972674),
(3328935590236771305245189004473611405,137305913831810308),
(27325442758308127599180856714,12774275971151385006472332268939359086544528654301147949255428916391596532464269896959508537577151070014508733348028896276367219672435830279590669575240999),
(2633259626884,14295697107459),
(311731040494382036231,2030290818),
(104238291772110203668360,142728497049939035987523244463178935816720377914746755495557482621871410233526464116604091137272912071259265325706393494866724085048484878791523930524575852901618781526382768082433692154055622901042),
(6342716483419287103049974031270028,15790192690563)
] : Array (Nat × Nat))[i%16]!
private def pack20 (i : Nat) : Nat × Nat := (#[
(1662705059098673147259234635488360543758,697565879577673038987374090912487312996466304795418452713711587255622674),
(851304990258520651396728133854546465993999,43685305353677146990424862215),
(435868157830806212039769865623737249806758672,620272415097926038543578146395528),
(223164496809372780564362164436013937054079202961,773428056287507064120619305930428586572515754650411408951159997478220690),
(3295556483,1161003394),
(851304990258541368189199975616380580017679,69217832766463546242039403911),
(5142693379,1426238210),
(851304990258541368189199975616571968270607,41774746752188384824874700650857339525770),
(47242897050720436876222985,7423743138691),
(3245835377118464209612069755857221261,652228408765071659856565862095424809339065473456871908094105981190940946),
(851304990258541368189199975616378331938831,15966954888663357217241747636033990197730134437639184187454914382895953011835353527667616181500296534682),
(4707664003,2059577602),
(3331932291,2064896258),
(1960202423878963384616955466876374090126,16924234995331),
(203590413617402741511,9481211496255502945871013207021073593520323345697488804780910989795524835473527261795317653574677662492451131342109),
(3247470818552095990749699950812214797,36646182616579903477909093272419619169802)
] : Array (Nat × Nat))[i%16]!
private def pack21 (i : Nat) : Nat × Nat := (#[
(442542663542846726,1975767426),
(851304990258541368189204587302590400053391,189094568208212867010935861020573273327056775551034552462),
(4301403779,1150427778),
(1303819203916037,281744615146585532696481828294525662343109515),
(22545571866942598,578366476175628934154118396651784),
(341788381391539287559,131529595265653636),
(1215105155,337682178),
(3247470805512791008123562162929616653,147505643798826576901342751420851297039048781981685770909805589130484981151879655113890447918162982124919110782504257531670291556353962342275474981),
(2771571913604,4928052630790645363707376626762464777),
(676958783574851590,22766689000757121371045287325986969606910033294245389),
(234883331,1801457154),
(21769282130982748679517833,1143833454381535321605),
(92284810506538979171592,3684439150250078706460166),
(397637526596489734,31221899945456150509160634293464177319725800226930438552368312361262470930221039488937862881493001730771110239449107648803153172270929453930123145076909382132761480702421848738197038),
(177460682912252015164808,135544436529718404),
(640797445508,2239453909868054613518131949888807432279508113548)
] : Array (Nat × Nat))[i%16]!
private def pack22 (i : Nat) : Nat × Nat := (#[
(13990626692253869592528391773579,3741973266139435907967607606027596917139141487028675938173656983710413127861592184286742),
(53370005387322438449246985,141497022327748297362816155633057907218427091949964443955595126229740531747974515377550603881529154581282075),
(3296867203,1163012482),
(104238291772114137596168,17113237674243),
(23117816191911686,821271866634119940110559367),
(1007629187,295936514),
(46520555492808799708950117130,13977116640003),
(725469421612898566,16245346988419),
(3994228483,400604418),
(545156303054768518,33285579997663402267508361161094311613194),
(13621595287169042049267599626,13065325163523),
(5043212803,1551033474),
(112357586386845363568975398159953974258605160410331667,644320957750613479356345234194946763489642554696824954446978743898343340528211300329183930885226384116334527959446058165663),
(59358600023951268894028809,114006970350143748),
(4657536736893278489610226570,896993975572002559877),
(510200579,310416130)
] : Array (Nat × Nat))[i%16]!
private def pack23 (i : Nat) : Nat × Nat := (#[
(219448410911807350720655074531160105973838203926418,43410747562069428032978023534129782318614488507888624487846492172573371038892272886502850026824732728073716393154026657215176500641),
(11808793355349898562304410762,13039567916163),
(108972159060245401306120,8614583500390573218689158),
(810480934864645,1912722818),
(1251547139,614540034),
(180243770518637786631,2082692738),
(167980861890955398,33157195246530545724877950267916674123786),
(479881506749119508706843170900886463180244112,349675606503172601681429026341823270892050315),
(3193394672588365164428717679101428899086,17570051835457735917369890076582070289814972658737176264234093763967724945376171474632546154256678511258),
(104238291772114137582088,31670185178926139389238007463441738229254804392917153080807796196460737203525692361582830743),
(53370005387320974702936073,12792562469806858902950117371825200529075386649083922989420080656),
(11836321890257935751,1921077634),
(203590413617410424967,17603374080495384761002414827744289222617723201334286466954087259393110140638731381507335275711595536794),
(1249905923,454089346),
(92284810505783670743560,63348759481935364),
(44947997284681823554184,77837161341814455062097020935)
] : Array (Nat × Nat))[i%16]!
private def pack24 (i : Nat) : Nat × Nat := (#[
(640796133508,9501606606084562955257862),
(1563827011053868876957417866,12987990550915),
(3193394672588365164428717679083543141646,585884825885310656677400428851748912187187479867210741168849589733596389158778490370612996933115175471845388399226109745695),
(90778422839621133351125257,1143263057762168580613),
(6237097364026825866002758527915786381,1143251306916422007171492305122325472753259192193949310124673680976974322644287215872147135051911416224384416540),
(203590413617410422535,29222016424780536784706123765414460378887941939171023724918968201461589547677228765913805079),
(168820739,17023234),
(397637526596504710,21615334879552413717648750082152179298321577292320854663330116181821239976916084717792173061522955339532724808357979295732503758810576628998564),
(1322185123189637,5021426172726726863252633072162757129),
(12386232127449364025894230769675,59271558040414145929310871107524082392326199124227745713995152),
(11460736262618287735785589002,13288907775235),
(6243883273406640469396649159999424909,77334419087554819430869415687),
(13640865759066102886448430725643,2097251842),
(45047273331309269880072,496858471394872938179078),
(85389385369434328455,9835745165923982044794433159),
(429072329889201339433861860876981709696387068305,3983172158449761390996004500359624064953892697599888856705906653424355887763)
] : Array (Nat × Nat))[i%16]!
private def pack25 (i : Nat) : Nat × Nat := (#[
(838031894314846366081761447025354901752918928,732745798217560323353116776492935177),
(177461836071681521042696,14020496274307),
(1636781043583684308753440326221396292486159,2629188890247300211168297564930831422608331954700),
(5208225795,1315075074),
(3196837975749383415534063137151164633742,1176650663452717511036484482558625064622467638702747372577917810159505351105537022932689539095452487625189096604),
(397637526298317318,34328569854096177407717769544128077622666),
(3193400258634406748276307377743827384206,9644111859691589279656454),
(512963715,5202817771541184014966552080521882249),
(11808793329711860685468862474,141230250293031940),
(4426125670353565246101459290761781470934172101686733930337733143,490276366329256367792329067617928),
(3832172552824007809979612638901988793069462796488049520572566,59847953166467618432523435911),
(16884329492010365471273266958409000481633821529429158137365,17592641266435),
(22325306447201897220407761930,13624366159363),
(1451858232547205,274415420465127141462706448881586341694104331),
(4665972483,526448898),
(6243883273406678582513689567278468749,5324909036342996617610018219894043401)
] : Array (Nat × Nat))[i%16]!
private def pack26 (i : Nat) : Nat × Nat := (#[
(7729489310899232797801069652440064920585838164952235568004874647,4050368458871779307760691994157949740164679180590164334744023999369012501011),
(184792668653095497991,2013517058),
(22493874540016072457652105,7305659494215980831244806),
(43531957415905345243254537,7149688815222666602719750),
(476450691,294685314),
(10627909778693935238792,2158232706),
(166061238923157189383,144895222865963524),
(49901572701286046299450718986,13942681404163),
(5544282499,140670488849636612),
(61742913960703054735724348722871541603122504056050496148,13087154714039093979446459932044443711450688617971915954502818832),
(190405541451261560636680,119992789595489028),
(5545594499,3108499599182805466309382),
(52068914339497136228877321,123146204760746500),
(114242827043265976808615246069396159931663385245330,28482292940778524382291090439),
(435801799950818052759105877400188591881326096,5221509627734606344865681090190495497),
(114457181350374435803199083806965833070100738869650,36265595259848631769377856806410896264970)
] : Array (Nat × Nat))[i%16]!
private def pack27 (i : Nat) : Nat × Nat := (#[
(330290516187838825479,9940357089283),
(726339102726374662,17782361211395),
(837129253051004397664001435292320788463762832,487148297913782098085325124450006749870399433613894659653426519282390749266722347541),
(5578047363,1389532290),
(25428678702616909439894887690,13718930946563),
(2624396675,778137858),
(108986057527207120682248,1256331425359256164463533155578926301685962376955916027381263),
(2285378947,708923778),
(1635018072365242964187502803305314039578767,59726961977775363852778207164433660546373891334014085864520487768730652649932820),
(177460156332915823034376,339244382351456242598918941798713122437126667),
(12181833925584278733935233284243596,44199562185155599821672581378668755081738),
(776635794133765,734271535052483469043671116706360268493635642271650913959910197004824082),
(352037355505582086,14622025538307),
(743421438907714950,80257673301762948245963141285640),
(1310343427,470867586),
(346602896777537602823,51887054490639678624706506759)
] : Array (Nat × Nat))[i%16]!
private def pack28 (i : Nat) : Nat × Nat := (#[
(1635020928627810728931875772065401896190095,7110665650577353456328068826084434541481583427740206165654664592),
(23792644385798990701287562230411,461755524635505862406473992555176346329530301834546950925147575374564337337751493141),
(346602896520141490055,75327384852286117590127008263),
(5909880374897570351112,9553735947266186207812870),
(667555295234831878,2075287426),
(3193394672588364559965653412169940353294,13427778497328085991519210042341686615940925139980997953971286416),
(4974461315,1402116994),
(6237098969899300375159340863791054861,9880396206911594070989318),
(46478552516787063096151838090,8794248454638123007138822),
(5209540355,1445113602),
(1315833859,345023106),
(3246976579925542148753140616705750797,5810084229583755824582866318310881941770),
(6237098969899151915232271923176096141,2139355172708013855844613023151517541489653426112015156165644371932537701636086861845583266347932185),
(6667233148841378488263746926222604,61939654848792546415912130439),
(24189505538100081713365269770,5657806686076331662738228094694790194743679177480356537416795220535483254291),
(435759395620439148630952046162624161358690064,3895017482459103725369981323568052895969852859841643223144849212990069906963)
] : Array (Nat × Nat))[i%16]!
private def pack29 (i : Nat) : Nat × Nat := (#[
(23792638259990027879156627885451,41751650379233033833377637549632379836092448516187528851751010677677912186339446173380132453528),
(23819555640274868136280709155211,30416979118543129082716123545511798153226),
(726533765906634630,33625862455863075815914437979662648045450),
(5405218563,660683778),
(5472327683,673268226),
(2771506370180,148214650668019588),
(23618003050696956443822217,7352937350577491060762118),
(13021914853554815820760307745035,9865173602700521894056454),
(23618049167557484987485577,7400230199986194827239942),
(34419160849479425682301202826,13891093538691),
(27911071305354174609762186736937153400353680,270230159436945608739154341395326483175634059),
(101547061450815155080712,145382626302123652),
(54513811143269872284691770970580377744271,9417548954609479991917446),
(6341133785032714117039465312827276,2741970026581389682726425135738906190027629760986687817485804763178936292941484259736115720583360454036721997785068673393396767450196993955),
(458167898833712353470082987539558649659539856,81633005122914870058210785671),
(46469996601543023201477788810,39751798202166558570514592337926087812812364648457989793243735445459627815451796)
] : Array (Nat × Nat))[i%16]!
private def pack30 (i : Nat) : Nat × Nat := (#[
(1308951555,159402882),
(90761712112388717190386313,18195701546115),
(2622892163,1023534978),
(5043735171,1531107586),
(1311001091,1849759106),
(2963550339,1125258882),
(1320756945900037,2226388354),
(1516866785796,2227431554),
(1516866785412,672570628280391125156801942922888),
(5441465731,1112674690),
(27290486636563866754508992650,13882468996867),
(53301731677219448865309705,280173021720287282549087748481530425406343435),
(4603722243,1937915650),
(36561631246037647653704905226,914893044872732885381),
(1188667506581915013107040882969666787416221260037460005054684007825561,46813019831166827667736227190835374807081068643412621064484568111927431418463252),
(33827259656639219627230650569990739658949043804569159444,1383365021729494251165445084266719714843151512274822813213805365491541165514327442129171248973073210162059843077402202289530352794021768343532737774630)
] : Array (Nat × Nat))[i%16]!
private def pack31 (i : Nat) : Nat × Nat := (#[
(5175920515,1439918082),
(492251414922210224245940043470392012593627536,505885946732716270602798782129752840624336324478793913106144998794365806326561646357),
(844461782467845,267620427223864934098293037508014165633130891),
(71959939,116406402),
(37585832196,2241080322),
(46522667497370083734197511434,18367485523459),
(27325442737559975116906840330,19114470354748455931692811442674778406728066003658187523813939944645989408211631696419477526849593933802501677902425903572156885877968171440164),
(2692949123,916688258),
(2755929475,922859394),
(5041570435,1414701442),
(397637523478036486,34094407600926496886073591480227916279178),
(1649271652100,1280552942971244315047186012511909666826),
(53370005346796826400208649,14517654317105741455973703483097863584360226513885661756504787780224885103936736626686345266484790072090310597788723211805389756195318929616344899577068910523021827435053241480117699955499738417),
(703773650386949,6478757085443),
(2691636611,790722306),
(5006899715,1281515522)
] : Array (Nat × Nat))[i%16]!
private def pack32 (i : Nat) : Nat × Nat := (#[
(9015250445184342949620997376121996,62559824537467653738613412615),
(34423713225783737204439200522,13891121850627),
(4268378371,1265784962),
(53268432593254001670374665,18306107018243),
(609582089093813569333811162025419377018280742919382147642300409314685466,5781738358672479672409942449769068077996600368779565134814875868992695909011),
(110958495601275586743573624966282883726,1149611304705219247621),
(17325364992627868293933949959664636147318266634397240342165,957736866426437079119345603577182576861024706826476491146014922994900359639485407588931644771588052559869419292),
(5040257923,1288856706),
(203590411848750216711,4135904081143434644530407267064999305),
(128835252895765265184952584315012201567117296615570,45858609916371974520072742174735585260042),
(203590413412860969351,10125276073946392072299526),
(104238291692962551562888,47325136363685191500185425491957503280218886263269376658029957265828883164505488539670888511011563180358039834183825076195253634142329823920413643640077601711298572414507),
(1313866243,152062594),
(203590413462817483527,18573704832003),
(776635785937413,267960709777811241070680932437000167631220107),
(27281926548179581702076966282,924127181034182789509)
] : Array (Nat × Nat))[i%16]!
private def pack33 (i : Nat) : Nat × Nat := (#[
(104238291694492661723144,21251933785928876352240754170843986259338),
(170535555,182475010),
(397637526297522310,34328762110405886235271233700195496751754),
(13990626681623700029883700421259,1678547466727907131625264854693184154613424934604607072776079),
(776635791974917,2248380162),
(203590413462721609735,7879402715145256040946286996161183730133059161565683214),
(20757118153671515271,3930792783293869213720703048398935817),
(53370005346796823857018505,55819718810174080256895852595341524523298341698841378045767512717748786341909671637503894840354939391545495485434066375926323260104534402227804114560484754273240125547819),
(203590410936274126855,10191855059503641063024518),
(53370004684478646454976649,70881876848395873061203617159),
(774163224600069,265177710066175236542503356510758390114510731),
(90864584955801612488359817,2325244023199149617761385616696952587455839876748),
(104238291692910006763528,5629504780322500447787676857112622150049276767324740927232528181843937474195),
(53370005346796823720834953,2484596774489338315889458759429139650606606671666484487694334573073),
(104238290672051235660296,127034268624108036),
(110824476251308180089215218470431956110,62637526347505356337628544647)
] : Array (Nat × Nat))[i%16]!
private def pack34 (i : Nat) : Nat × Nat := (#[
(3697492355,1164149122),
(251413420531568984304023180747335469086269905937,5714558901209336909302278682505040228443060028874882781894057952225593137171),
(104238291692962546333448,212781395211597306892229026654181128073905419087854949494863868420624639475198489093279977865795526939141705633949452098234678419231827366556952485),
(203590413462817473287,5603031573275994699544851249371506569),
(7163200860991641245130907943839756,207965734837658121485711605607380236620660095394475422350),
(8856269246133997718870204923243188077362340678511189200936982,64270949691420929708094358573084352244399173649562241849647590362080781961214204727164673867867870954778592692940321438),
(2956730499,834768258),
(18110002709551203389413415366793763490224212705829072814485,2294564226),
(53370005346796827242542729,34840547094015472544513851259711335055569902944609386244678167201080826311635486700812384791),
(676227038753594886,2294560514),
(177269283753142787185928,18821317674755),
(343137255620741,264480024872915071015573727783892963882705675),
(203590413462817486727,3094852982292582880792755795900854200833437414258789878454631263955901036167744150848662),
(53370005346769940784094857,5629504780322500085422576333591581993562623865650680617885524375375072999059),
(351597516220481670,1056081393718872212869),
(3390835075,287344130)
] : Array (Nat × Nat))[i%16]!
private def pack35 (i : Nat) : Nat × Nat := (#[
(5277682778569281313387120522,13288904624515),
(6196293603767798455356006829919515533,62560093823023488278006612743),
(3396678403,1202863618),
(7075748394283922147655206546291084,2307148674),
(23636984243668131123937220566923,154892034938906244),
(2354529283,949076610),
(1877749311662768666157412077910173817870,154891290009977816512123269018246652132561880270135119246),
(397637526294565382,526821217494885592810731608648129002802471386269857520018187748267468694975677240622170387377257988602999792068808755871627333027177413788251996723133753999861453193385092908),
(961428532838610142046086503787444758200335,62598614026996265112115097479),
(90094908727705160327,1181744189400437013782654103805025289),
(2622966275,1024583298),
(492251410228431859176414044339216736561274256,21422918246553337901844619483794588212964342085337101),
(1951479555,785478786),
(1447772851417609306949304989579,378461522380376235338058762226085198366473867),
(5006767875,1279418626),
(21665926160851230262529499658,2319733122)
] : Array (Nat × Nat))[i%16]!
private def pack36 (i : Nat) : Nat × Nat := (#[
(13990626512877438021501730757899,10450988565690670376046598),
(961428535602405974953933680350030709794063,175475886973653194523520210601319284349063312523142645262),
(2957387139,960612738),
(53370004837873060474002569,212180074072800004509003602004682880859284306910845844622),
(13990626548145608588600213511563,286472072330045441824058712590712473513119755),
(12092334239635156756484917386,897575500915404744581),
(5110059395,1543692034),
(51767000281462282048012240906,14054645221507),
(3463071875,1252152834),
(3457108099,18181524336342502149192195257493441736359290803053965),
(12182490342627721130186024681948556,86896917800513234416246062739654727467537783943051942147892034355473),
(618305642878419078,364848131915550398842265098539528),
(5109530627,1423091842),
(23617840311787415540009097,2326832642),
(159107908815890352135,272897154),
(53370004828565609380855817,1284507273282721135749)
] : Array (Nat × Nat))[i%16]!
private def pack37 (i : Nat) : Nat × Nat := (#[
(27909561349162766786436340747113247609402000,32986836039834994762406939645159298819466),
(75696530333461811704328,9940357100675),
(961428535445388810845859037404544659764111,7884633638948893100702810423426684270077193559716417878582367487290418306579),
(53370004837873060480687625,78423132291783896104054093579653594804015066497141803708355302088950225569472511984698419381419916268911771),
(2352815107,1824610306),
(2621257347,772017538),
(2838006947305761810242943626,876800114772178733573),
(22545367648242950,1921001730),
(492251410228431859176414178078111097644253328,1644573705206656471387723825187011024667428414860),
(881201539,493939842),
(104238291693339299293704,10130731213390845295484294),
(2627218051,1047655554),
(53290312697375729352122505,112103981615109380),
(203590413462819711879,9514889103084110561970843319453784975485870000530750428681509020241850677070715931651057408546718870276832943689373),
(44033917399429,2074317570),
(12406638178681448021016661729931,691250989225866877619259547216776)
] : Array (Nat × Nat))[i%16]!
private def pack38 (i : Nat) : Nat × Nat := (#[
(177270099969870161594888,929323143606775849989),
(104238291692963693862536,130944983798989848042125330930493442456112569644078500515583102533896398899377189015116730007431394530438215010266470340520888040574998760404559653),
(1310396163,474014082),
(13990626548219395557097371016331,533157301053362865464254878526578135411300202856833476213480212479601038778086702229),
(203590413462819714567,3095257828519547455546815968016038699045918813238121695665855717699432745243823910573742367749807752557230855109888479626547960072455343779),
(397637526294569734,59326729301689866051879427188268237670323172752955571780033527846094593902756347297550278673441503104032496274793167812260975872238948610862274366447065255592),
(12181830789318126664149607341107980,26039859069036125859740661058875876449519365396893069),
(53370004837874054083982985,960701231925242020913858764954257948174263499048473976046210368535772306),
(77547395078876075864966281,113796147749080068),
(22990530855671171555700847626,13667844317699),
(40937987537633734531278255242,13916873838723),
(113508085990783109447432,3401403871323404571369862),
(4905779075,1263809538),
(432998985255367686,19388366612739),
(3667558823498202936703936071500045837,3933974774527698291522239754889764295575364733699276745521453035717441890067),
(7163200827144927610749875139648524,145138051716072108077673411306704528792627569282309005597980212083739636581690594738443685996312)
] : Array (Nat × Nat))[i%16]!
private def pack39 (i : Nat) : Nat × Nat := (#[
(397637526294560902,25218246428371397478271536847676672681596872080217364462955779184098838185137729641450318085132377454299135053361980699037110904481),
(776635793544069,14411980850857029944073577568243483243594793151680834253018652816),
(203590413465132793863,26214551348011291711280319781670914973853994980719757),
(104072290603978492027016,52162498865153540),
(27325442635949453186928155786,1731021156015593353504936015636668588615355651091732359146895),
(104238291694147994468360,7782941619826708176123883626653169257758535578016035800904556989602846612645841116659260746237633245379783844523933),
(2722382083,907129474),
(1356181629321477,2378407170),
(203590413465132801671,119488739416922497220542791388816056201031498109578675826329096842257),
(24189505694369225464046363146,8775446588998805034864390),
(397637526299087494,19269595214562492229386312402482848934167924179335888692156174755854621284176390867001050809288218378613811052925698091555214513347172646383012),
(65421564005822495216710793,5313595084211178498572678),
(397637526299091590,36066070079089872846571924218778741644433340858915432780605240729056900220020298385392431127),
(397637526299082886,209881775337733526894315036677031295122549416409314914574),
(776635793552901,2452401845436657516465613529887338408922737565836),
(1513849487364,2281921282)
] : Array (Nat × Nat))[i%16]!
private def pack40 (i : Nat) : Nat × Nat := (#[
(1275406467,157306114),
(104238291693185891511176,14051899755752026675276594902023544012248835228984719630819158928),
(206963843,191913090),
(45811638376737542,2390976258),
(1284838019,587273986),
(776635793550213,2124733269859224018849267123831667492765670989639759319499152233252548538899),
(1516866784260,154755006120662820805224723837241957874888591724826300189060999316449850859116701915256338526713451954579227),
(22658755126821254,2336237826),
(13007231066745665326122343996007564,4247747632915399194106858878431143817),
(13990626603633324064793411338251,39316161257907941624837769972064634258147741835575134251667599578843762094906636795924049042697705404898496677119996316960599272993),
(674499715,431017474),
(180974589495623921652104,62986202476815041620749857415),
(203590412328845588359,5820275591548158983042006450021862588437576781878883251375995129420312629357320876130879570450495810104814089372477311114898195210050296299213965507903780870384002858),
(27334606337908864731349778442,19071523307256116190704769466323248962958538540531981),
(180017930143124233863,120683608222712964),
(55799681214564715283167753,7546812086493920369002758)
] : Array (Nat × Nat))[i%16]!
private def pack41 (i : Nat) : Nat × Nat := (#[
(51166116232615026405283020682,14011569704707),
(2320890605379051915003908864453265561129336894065021093044638122392,154026747585294745946964673066681496183068769421466027662),
(51782414627535466938913474570,14054617960707),
(98417987370840462897760649,1486126082),
(608407547121016046014921908522663554185122050907145126285152748039373722,20097959416077907285046248184901760360264527873975789713346845629411289454479820991799985263791550255642),
(775642108265221,2392024962),
(203590412328845594887,1009735648100265055153735369075735262056228047068724720205504342711435410251243967940538669269145624423329912199444850157129897815917817086036655101052187708616105),
(414773412393788422,1046291473121602186373),
(47417825303202748052169440394,938566920740835331333),
(5477055491,1365412866),
(1987256579,813794050),
(27327265563952361835809946250,44002262583589693270870305952035128819789758191538797224904850200366068821844244),
(53301719815415880400248329,2404486146),
(3192464899,1001512450),
(147574868654729075719,3933164897729782033670095677944979465),
(4069274115,1221804546)
] : Array (Nat × Nat))[i%16]!
private def pack42 (i : Nat) : Nat × Nat := (#[
(41421622356690878354492624602219446097222044421842875028,61203886469281440102278636423),
(15335802729368402993534996683113072409323094189455278997781,384914793486126395085428472673906900480340455317707712386374535169757984949966964117),
(2890278019,948028290),
(47446595064182194899401392906,14028787331843),
(1919107971,1823686658),
(96816387993430412952421385,113165001849865220),
(24294359174527282887500990597259,2425538946),
(50541445162395583868572223114,1495565826),
(95388561516338113092895625,1750369922),
(104238291112368942629128,11356409426078129747459003406822031347798336499877276136797615453830637423379488336645069912169370819533738716261021641746421783988387182506752056006296570035879237030395104993481497233844888587206821885492),
(397637524088111494,3172716743193981942288581929859995503689423637171622648202451406501284414814355136476694),
(397637524079776518,89718442816740936740762822407),
(2581417963780,2309481224647705802152208276497021491334630028812),
(2894668675,954320130),
(491467702437684653895755061461461746210381200,1329480714457453902469),
(776635790662917,2297524098)
] : Array (Nat × Nat))[i%16]!
private def pack43 (i : Nat) : Nat × Nat := (#[
(2633530291844,88557287944542838002996761095),
(29952739705797662095040672568207644261634638537924870420,162636764334471812),
(203590412328851624327,307816094282695917185374728538491352912825828160010758619075500791298890455056461770819098879315748214808367666273311391619447608403298703019239825003960112703209142438691734225608255279),
(203590412328851617287,1013257235701318436520877212673047502805743805053742808631317068059801449994541790567921803570785706280057869796813426820637273888519573505661697308385885943983657),
(397637524079788294,66954288445707360565393004167442266826738846455032742527558723143618041059535230215350062363566233948980213064154757662),
(491469254975993669479248977848886577817663120,1762478880124859283695258581589043367722980780524625173504721950735088432111458067073333108809128089),
(776635789218309,8246574130246679259640730405340845917256708841202683214479801833447526143357063166841710578482997851156045073008706209586612922043762412663633634274664460032600665642),
(203590412329614918023,3918808091968154153368027171913342774099899373226986974323230791357607896705743880201238),
(311602272477429339651631497661456186427650491216110396592514125718402310939,18315973180035),
(397637524088043014,50681664716096996136673385422083389420625035852531306771136248835228873296703611943038146919091405953836888966343074242325937581674933313804881667490775317400365240321631276371712087365631376213931478129022813483056721464),
(397637524088045830,14174855621977361102419949046274821332762045328611732840765512964295240283242761409699533088364325929734914362044126425508031592159872088001612199142657575),
(776635789234437,480761046100147320807516927558626210557057370250951130482307683976919925955160516684779346747269164808354043959291276570823660994391204100749258373531604501171753),
(1516866775812,205734635089579543645782684183603227181252958623575744873060082910283907036520050749908294333976),
(2633522041220,2252309595386362800578240208936011220372227878156),
(104238290682119310227336,5849859316119050356992384712428469385),
(46470002303433154779743855370,2342802690)
] : Array (Nat × Nat))[i%16]!
private def pack44 (i : Nat) : Nat × Nat := (#[
(3396617347,1201940738),
(5444748931,1488111234),
(99933914353693871708522889,19732579521411),
(53370004829684582179162377,1026474963451794828833977192186357794765309114778785778545909629866830937749763611213892686819282470491675291036),
(381186099871889966087,164956398195785988),
(53370004829682747590770825,494182290815575150128721948008740383185773995253792018827726191943200771954114596605113392247219078010146966525366132576543),
(92287116190411670496136,507729312120048707473279180623880),
(51166164149001014236122397706,19706669074563),
(5443435651,1364363650),
(101137528479077898160226185,2464454274),
(381186099527620180487,165447948612878596),
(104238290681653851455880,85388869322641493944620506209009630081055820038987917771143193077106406341900159584554131189169223967318635951145302290376083869304827663700017259770361968168),
(203590411487605178631,96721794152334033504807350160835523400514643920199494618617053075526995438664648996721546564369057286297475623874627365644129465038370),
(397637522436728838,1731892023194501342780499527437956589468763602146017354687182799710509139724540692399511497450966930450334992359559589012886102552224470906850438026867736352435458250591659096030979127801392),
(27008090046408982370200265738,13624375624451),
(1552916342993092797465964426,888338617358858977797)
] : Array (Nat × Nat))[i%16]!
private def pack45 (i : Nat) : Nat × Nat := (#[
(2728210179,1080164610),
(776635786022533,1849413730667517112220165173006490083732575481123285267412495),
(32149168062297365582530697,108020653293339012),
(50231355692028847651669100554,14028819843203),
(27325442472451598030494449802,4669629636524954203120232838066292611523355189912297492402427288038937335800052878813921019518034343944304721502116562399244577121556585099579352340425825615480336461101762067629),
(27325442472789507895898283658,36734565758354740524879824100844821977935818246447660545455417277955499694814931899193093527),
(41000223786205318,1513962262355405827406204609697749770762),
(104238290680744927763464,6084664008085297413254),
(27325442472577329931828937098,375416569300257298771804709867453696962017103952077973209750449414206293043371555989),
(51780291377240075532542100234,942610451271210152581),
(5243028355,1450357890),
(96294737075449047802530185,2483330946),
(203590411488545685767,1390993526908468140511043892737612368315177740967962985799538252264577170727435529541626176806426398392672593564),
(1374445241582469,282443491971794369093267963420269361773167371),
(92659108759652791255512713,7688765001465225460068998),
(1877790108295190225882712651981471161742,275812535260960164676599183983677314313764107)
] : Array (Nat × Nat))[i%16]!
private def pack46 (i : Nat) : Nat × Nat := (#[
(27325442472577698820027334666,301002117665398233706609293596745614884397028377248530222326819557457019564806218133),
(4032669807578083298314807008317643690744445892354177804061685524120,226044343474818914672322295709344121349561738197148620942),
(4474651255770907119442449417249654546708493283174298585486693783,1358221899599629820805),
(7163200791498351813236737284589964,8551882990336556725131740865996252150693585275832839161435478926179611490350409425367897995138029627408727400537809836226798252616031567955163293923804668803261105578),
(53370004829252597523104265,249540145220265709784388243974588902330900747),
(104238290682133979537288,8551882990336555468941782396485804992966795290249719560480626031472772164473676088879049206767688318118379896041206857449357943763751691736074560314606744841498173738),
(397637522433327238,1753888014193080033852389178621718540254368741806519982781967),
(203590411488542928775,11111287213188646641752041883463954765076910546085841320320006857805527160005806543375416471),
(25110111263320469957500551562,13598784105859),
(203590411488543513863,4857021178699149892977987956060389258904049615734953236671270780558509048201025962910139882726054754109485736221517696925077069962258584555953455929571193171108543773621454994777145657507573169),
(397637522438561542,1950402552018016135112414168957041801),
(2489403651,1011998850),
(71977219,2501127426),
(203590411487808454791,2548541415559347244549230681009069049090732033803400198433578044499340991582388345071333726266599065),
(676993931606444294,234206171060854161846911124342840191798752907),
(385770738145093239047,166715307550009348)
] : Array (Nat × Nat))[i%16]!
private def pack47 (i : Nat) : Nat × Nat := (#[
(428610972443242778584848666933699220459410899473,68389602088905710752472302617297700784800586244149992168396758981826877961306595611761322444988050537810843),
(53370004829094969471612681,126703598527485233838948074368357644776947927040517768559206946615824589331685875824756362067543233268360840096872344586748041819654201905744767546871275051601936642679677125246163479983),
(1635020606044008799778715380381449171714703,1383359966174429601023020922130505400677938822918631773817363761136295887608746757334237490738074153734978505628),
(1635020600194788790213356874734190310535439,20613669845080816760606732589909947105925119488245609275821370976383001268057594789576844781412594990234),
(203590411488542924167,116224901390399305187293030841366102986613897092117900224605946998249610659331154911095367087669610078476521216279120326539466305669488374257644730356094754596132673344082979565900905647),
(353466444404967292423,89318313231108100),
(2120105603,878813442),
(397637522438560390,3420102786580631741430768273807959768508346443788),
(12097174664984215931653528074,13555555451523),
(1320756938349189,2513738114),
(1516866769540,229806589708736663609145064997163049578724075745795412238),
(182851450377875437191,4138496093883714539258535150578956169),
(187480905191137687431,4143692211335885704782300587862825737),
(239527495615185030,1810144770),
(326815379162117,23378781477142688115425422505286475801815819),
(122574814261842608775,1358728905583214500613)
] : Array (Nat × Nat))[i%16]!
private def pack48 (i : Nat) : Nat × Nat := (#[
(134417795,83896194),
(26930644743664107028645225354,61789042870184849285),
(39725324396102065553207093485416463476415876828302995,27593337900946291346352506813361355389985638100000653),
(105913438451118694237673738511584592488898691473,92989365023995813328901650762115953885325887351487782964020641019913255476086601492991890634791134394485465044897336222),
(1273805236860799765617123850,12988056687747),
(1543341992729144372937732080286502157,3112360244401181870378204520855707820908199776051678478848607022141920043915462287077910),
(16428883398949145201700193162,905657774737827477253),
(5276648195,1455600898),
(26177878417856556662225289,2530522626),
(62661478811686466699656,20736579285379),
(3867554051,1183987330),
(18270093334827119331746842507,2330754),
(25729081282799380519704806026,13607386624899),
(27587202633341993014679913866,13633194182019),
(22655002038693877614101219210,13650399220099),
(25738771615814866877558378378,13719470999939)
] : Array (Nat × Nat))[i%16]!
private def pack49 (i : Nat) : Nat × Nat := (#[
(27635833254455649167322730634,13848508764035),
(170939720910039166440200,14054897930243),
(16460373997274985043548263306,13280742613379),
(27571469875588239597736120458,13254935056259),
(254390384071838899116376640257665377215260801937,767933673490756856317369090574088),
(4070849283,1374851202),
(254391493646305943018070675338851117430426587921,20849518492931),
(314865178976747016590557246556656332286745501732864868969023377820360322715,79638854271076546180402526582280),
(105421213267503432281608,7613403696358219312140038),
(8949006626629250785350988539511879785170493088719193389729174,4308500076193109064342646587933256868013101014411850367951264656),
(2986804483,207643650),
(82540384693045672611237104633971616407495012060661332250161732365829327456509085,1907589932266921243127549500983190202187416504222588611117071),
(369548604964038133511,518524345198631679764028467661192),
(5377640323,1477654530),
(16459032758255638935840955274,2158615470339),
(56327237724350288329790345,702857730)
] : Array (Nat × Nat))[i%16]!
private def pack50 (i : Nat) : Nat × Nat := (#[
(161211688853604829318822469988225813295888695430979164551097133527010405188508,2603017563340056152603204113286670843321949501397721581481929673848171302592595430300060357753023001),
(53975661192962814308470921,71726556863840004),
(2754225783812,816439714959466992517),
(161211688853604829317082731216383616781429734939845410599252448412046856632732,171579752887636484),
(46196205681653300785517245066,2363631234),
(1388558656642126942336043198919180,20762154198659),
(176224548503252189395592,641772676686121554437),
(316397016359582773895,2456077826),
(832196896694061719898853717566533321081827728,2564081026),
(344188571295414368903,116681808346782468),
(1462628772366085,283317230261415456161741171439989424165900939),
(721474863756162182,90715242446927876),
(5376327043,1351826050),
(404578167849178519173484567919875872145679,5870746910890775402670641157774865596686860378432650336134269286136360819846712352922310485027866911146737833588524993054528072810085486796392425721136354174018277674),
(5277499779,1457829506),
(715184502684037,20634354677763)
] : Array (Nat × Nat))[i%16]!
private def pack51 (i : Nat) : Nat × Nat := (#[
(5275334915,1327659522),
(9346563022402420743,479181753035339459071196400936072),
(42442501580279189540314100362,13624355733379),
(43055234754915119584218761,718588930),
(1543343230625833584493578216247085069,53224107158639302094062247394472021765295309928111056501023483485554250697962873381403585788970586196782416247146881883530439463329),
(2754225781252,2328064718975204145979592817859586783003820640652),
(3014331122860978867504617633167116,1436896234962357896441898968144086948905215857375656345855475644440142103669035327726313969944080520647257912604),
(1682352315662931910372165104328936931598,8682587606187532300157628070321542537431052863728544320322901152145455835923),
(171442299863975154626952,7655647362347244695273478),
(239034571889511814,33516269278115460),
(1952588419,712069250),
(27616173839816948632359607434,170228169057603972),
(34141600735468551966495500117177355996847759319009789716,1033767590145436209158),
(5700272544520445851143334420749682573,77001885057570692),
(3709179091796977778040109165561381133,1935073691756037669539364513056023244968204029083897246516879),
(12263728520180506526395782142101260,16503064023555)
] : Array (Nat × Nat))[i%16]!
private def pack52 (i : Nat) : Nat × Nat := (#[
(15530806144835223669300169093473628835530850633630292705301,782552779753434755920677803564936),
(5887387317422330605988683121547,3150295410392329263973836434618209404372016524245344088119433374257701603424608598661320926090049448597523259545605468200834535260856937185236504279670617845768310853078126555181),
(43869334324176952901896,1919265904309523504972920777332080677608565167882055830491407),
(5887382479588106085790310269195,28178979001155262781069101543081987733189707102975245),
(5887365474337849350594956244747,418786869671486578741533455547069741223005498361046753190294719165975375296172023234855469145987449283295909492702359002701128190424354),
(19538417244005584660335631498,13658762600835),
(1030426254565369388991484141856973066151241650544360278770076487841691290,38139318590497997499459160394404040331275),
(2654615043,768700546),
(111508627690919041118760160310374416380637291762155795,237164897732295256862417257716101081859311464690848342030),
(217790288458826252185078438106200031993432210472978,608855596997660260731354470405640),
(11498803354340489464821646730,5730139131409605854141902412710951043037739598391156590931296657520076678262550682267343611211279582321012576210684313519240044800394267862278518985910800515586094378),
(308086019,233001346),
(910841172868,94277999898581084133099100295),
(326815379161733,267787229477434447358683449852305619395326475),
(5241715075,1324513410),
(4405019139,1828892674)
] : Array (Nat × Nat))[i%16]!
private def pack53 (i : Nat) : Nat × Nat := (#[
(23634358786816701728378249,110490774507149956),
(5579556611,1513333378),
(348904333116870315271,63335383706826828818185144711),
(176089695795744134,787862916718247540347051047131016),
(10429788485920620911790881648153626241644918137438288028437,167202089820448260),
(5338888491065157025415038434391922769872219276935748613582742,1102486365214169143925299472268213724261760777836685),
(3285844347517596239025517706539249421,62404671142280068496924636551),
(1543337534904700492411664857552336653,45975136534696936769640078477333756427522806679184299605798064370755221685083068725670239549691751796491545372),
(50266265397376464165870985,7532616743775615778387974),
(43864453713762243136648,14187137322895802295534009775903746210402095892676739634091348611946499345477337013011499628023591864030741908465770919435882107952048512893920448785021652927713534432624947919299130318980962737),
(685499083206705158,34435250986579100006217098521421944089226),
(59233450045967452475135235659741914196468979352142099,507729312129467499647129822145032),
(1444561667,492068738),
(104154830100777870215,11367019173956512299114374),
(3062637315,970051714),
(80762675078277,267271703747691190519806239455479510151256203)
] : Array (Nat × Nat))[i%16]!
private def pack54 (i : Nat) : Nat × Nat := (#[
(3197117443,995220610),
(52750159749006153828738057,48785778553349636),
(3014339829478648554744885468149516,256114623821053560667390321537521353047431105871757425156573704098445466608262847605248788509347014278087132859425034998892806839523746),
(42470290272060707751069561482,13624365170563),
(974008835,282100866),
(21744770522616030798677258083467,2626773378),
(5107366275,1299344514),
(41709871367280553738332747146,13908334229635),
(4324004544293900190526368783873548,6493146487407191700698057164105815709962),
(24539771795558063407811475082,13675955118979),
(279529639614954789836789843586371872708814753678639842899263795222233292443,563542189010028623101045382979729469992634015588263872089522797915538),
(2654674435,776040834),
(1181353731,315660418),
(70780803,1049474),
(26918722120415697223295682653801317265227992566240065827477,1449975720619273414021),
(7944684187814018773378610684483198220013768109553525041470870,4880051659826084633783790606080416536252012602365391057937635939674771644297156639189782)
] : Array (Nat × Nat))[i%16]!
private def pack55 (i : Nat) : Nat × Nat := (#[
(203427401869368966,86501225547505953551772912135),
(28788815688268503448787828106,878530341763294534661),
(1712655107,423676290),
(23929746848436533881996035825547,1276763235355031269449202312723071889745798171705174091159695),
(11498876325175057003434230026,46941472507075895419952748759406196393071842554545816957836861091426420673333270158792620223080180037501408684541523902868472642738801816433643431174497539501314426581547),
(30306565047508311360849802720959588550635331347105395092,11886837466897045542689030),
(59192509858414670626659770939374196387959631537315219,434887825996710704097412232503937449598249739),
(11498876325175057003434216842,699482448503078045069687838795028398774931484369609132270578605212551884124683800576444690986079504359705971893938678223096138503337352561898910447769030469414185),
(1765596195185298382697445571792573051790,16102235830922166633483406657145969417506486442090765),
(30328972597313416719735383869180986934796767197998947732,3816405293659173856190419732869566117868124722027765606786663319228910299413902607909167223360006815304403771783801993890537376),
(344188580143014162823,1166301314),
(105246219043681205039752,21176019811971),
(196343235950699850254088,518206388433308945229871435658888),
(109963685591636374931336,503620124174854672693940481778056),
(383482882716210644743,2653215618),
(42470299854291469571027251978,9399644212227)
] : Array (Nat × Nat))[i%16]!
private def pack56 (i : Nat) : Nat × Nat := (#[
(419742019583155334,412924016605024995973),
(4782579752308775059464,8467203104630319857592710),
(442085686623761918451719044622827385456165008,61591210275128666273234605703),
(462840448978161219565303692102146420270694672,802520863483196472007301942005768),
(85672761159691881095,74483704412112671921253043485883268442043634223733756420109441036790862301339615389850115273141228853725505159790746063782381236804255842977240831927449217188667027746859),
(32012330116137484222984,1393306624117410136581),
(239403419857388166,2522116866),
(1304025360709125,2191744642),
(4976102915,1539497346),
(467584811860613,152510888145099524),
(1303681763062661,9468772580227),
(23459927944428265534214153712011,1463683196268814054149),
(1757923657476,2608121858),
(5075190275,1415750658),
(356569819321680006,34094436162045683501485108586984990961674),
(1393559418756,2572471042)
] : Array (Nat × Nat))[i%16]!
private def pack57 (i : Nat) : Nat × Nat := (#[
(91322910565107566554594185,7357647039153795412217222),
(49011184203061528431496,10567354219267),
(3288776104475768566688992532867056141,2822112666820503605136977009338814674312384175756),
(374511410356093574,32753732961980293395986919685812751826314),
(44030121836422120671368,16546318611856842501666454588808),
(1543343260955363213526842997030919565,3094862006254707711877766395813640677181051699543146629038122490846944240412060688888598),
(205261381020857860999,7400406457747402148318337159),
(6664589683885517349011337,7206476004395410763500422),
(681004264341782278,546408363718413729313430195857160),
(2189369603,889300738),
(96774643597189,12075132030358890151419142),
(1330086453788421,21974397208579),
(47858410637005693882146313,112104230653056644),
(105840762227841969460104,839188738),
(356569818955063302,99154840148955706530208208519),
(23943356921072418587945461697675,136224901786454259461)
] : Array (Nat × Nat))[i%16]!
private def pack58 (i : Nat) : Nat × Nat := (#[
(32132183313852933135748745,10478241312883100488881771583862819230517401133848440249054919824),
(37946883,71311618),
(17553244036,22053045731331),
(41352546456379270,11895668267242906938824838),
(2088050307,1784777218),
(45886450371738683952941977866,14028848159747),
(196349986776670517017224,516935100633324447176789614326408),
(205269982876734135943,3951459288244133273862984182369623305),
(11498803354340487364041592970,952100699899024237501379288328349222493024257903795550564541619692594085285862244834211252325660408520820821261502350485028131308407824049023901872263746062257679360332799330902672167817546180327692467),
(5076439043,1525864578),
(46829715902302749756404879114,2335224306530592732334729787968890016217988019084),
(98125442986485584183176,11433298408032759780048774),
(3802087171,1344438018),
(136338466940976844679,2703558786),
(14288696823972154843738262274607467534857455797642349716,3681320638062248741743521334819263188957003057036),
(14242402383586090514038141176383384078019518518924097044,5388617566894386019870560411455972511379818402392804769648525135261912557107232907081267841014207962047189678892295564211621995871676343134247872780769851476216593194)
] : Array (Nat × Nat))[i%16]!
private def pack59 (i : Nat) : Nat × Nat := (#[
(790191749600439886151049093134883698830,377803276055731684070881136785667799398850486814015869316142496248881995103264355093),
(93847919456595878018502409,7721871734836247196286598),
(42176592303326595672259642890,943190289783400350981),
(4641277571,1502792578),
(86630967623666316194597257,2710899714),
(3709986924191035162374925334336322445,12212984650073336251156230),
(190389491035761881272840,22215153365891),
(27635833263697071918984549002,13865713802115),
(7288232487018048210509745711263025940634575659732184747157,12439068227757286115345260088908604534045914377750227804693454381759450538341927999769870135552877298513359192519965),
(1543343260938359152638767757877326221,36032189264743805370912122847079098284276325457172327661722760662673197074900670913049180692112774424034648706440769800256062590137921409973102062633572676949749591122497264401018294207745858174478054553623260080292192312),
(4974457091,44145471656870055743291921927),
(1979973763,20973826),
(5887387317422329531245299369355,821536172160404382913677995872392),
(2991006979,964807554),
(1248594179,334535810),
(328055006828805,40115271203239556)
] : Array (Nat × Nat))[i%16]!
private def pack60 (i : Nat) : Nat × Nat := (#[
(4323330788169241811198835954699276,3172725992521174310085567677684426631294353716139722901582480927009939904897459613394198),
(790191749600439886151048680133011453454,36484785036244484139671118246631450616152400619436306057501349305351123938709881341489287704033695054368002462123186474168022774561),
(5073876995,1292003074),
(3014342306520232719997593282887692,449864099785440060960827547773666809410241291),
(167328541552558214,32475921935310870334432128726096158933770),
(11498803354340487365713475338,12284369591334283466044678),
(731472495064965,5946897183590541362940038),
(2718433923,2221175554),
(43864453713762235129224,6758599702712039399421499526696203529),
(45895825399052204760967958794,11856805813379),
(674052611,378582914),
(24498452255580535863311022602,917794556106056557189),
(85672761159691865479,42259785171516606934968545257302967939099767216969555154705172981862123984866281298374594240331718022647200415976326212942938409906948970958260952428547959635642555705190561020506158),
(696425432294021,62227858046908804),
(60258683667468058887,88753352989042082749382535),
(3655396977820143788936,485830768687344922582453292433800)
] : Array (Nat × Nat))[i%16]!
private def pack61 (i : Nat) : Nat × Nat := (#[
(18916734324071642373843395338,914322280046154501509),
(101191555,109065090),
(402043831321305990,32582283426191338667204725074358684684682),
(72161614577719025484808,1506918036348033186309),
(97487462075900213786775433,7428648564686927607058694),
(4598861571,511767298),
(168933596922569637592456,2746555650),
(726303008989712006,184370431966524548),
(41245991002003508133120395530,14037422362243),
(6967184262425686151,3987991714610341625626117044062665481),
(2522892675,1017242370),
(49655233703528838,2751799170),
(681181062374050054,470716727231341445711012354578568),
(26582190990725,9156254552629252),
(579102730663476590463596646216197888345231,61475890069032820151331119751),
(369897603,260078338)
] : Array (Nat × Nat))[i%16]!
private def pack62 (i : Nat) : Nat × Nat := (#[
(189088867716,22585689842051),
(1983836365564956429713312011917273380494,503610491445518592060810511852040),
(431325173234460923290821900474263850030927137937,3755293959554193946864610721143592112510735588748),
(358005905275739065991,4245161942487286282299410854700105225),
(4606477827,1492337282),
(45874337501619875397888594186,13985772657667),
(423364612670126564815422721243687657842394220817,156714355624561203127558345274707551879045753815142970510),
(17516080686324941630847086948969444362448538705653255046549,1695024882872540612309516046380973063727047780957360573951567571806837743836248433824524414407164697),
(11498803354340487913630938634,4066859578909518847754946264255543817529718247401718738357504055024218127460458635964405836828106070317416137444353820225302560),
(22458600301446265456310409,277566010453559185338511660774232165072562315),
(45901283281043533773813664010,459282261457307579195133223956916719468109451),
(862132928564403196739205081337732442293647,46406909937160713617546117153716918430714567365671784519936168482367927179501204),
(43864453713762237219336,4238966563075217558618129756858519274874460329308360658443970693556665927464410383280116671553086982303364056472981703498002464),
(715149205635717,2731867266),
(80562695460477000796942729,7650918039632512357200774),
(1946421379,19924610)
] : Array (Nat × Nat))[i%16]!
private def pack63 (i : Nat) : Nat × Nat := (#[
(420093897255498630,740619010),
(302647702136769758215,1196667138),
(27641594472549235730703792778,608278549729730791301),
(205945927787203863431,4174906831359300386322553137823691913),
(790191751197349423616163402906315211918,32475916511984463830710118027903624029194),
(1898975911018568935504054968941922950286,1457917953116497849093),
(820151888972677,362587423875),
(66814274466652892671915083342531352748795078526902163,12523749525701473886022790),
(7244029362745742318972901967928460,1457917953116497728901),
(40003212870653910079778407306,14028819835523),
(1787826435,554765186),
(43864453713762233484680,106600638114431301424079454356737851658193938775924277970675757683438131264495226467981173408809579592835109311347039455942471985672486716017579195073102344927609471756060418065344522613532952182626604698367285),
(22458454659091031398490889,7211303809226758331560326),
(6155245020848732489033716149106845069,2783260034),
(85672761159691862279,57604885985730213338549303371976222389084154053243380964710023009500292743351676434972178116173665515428554786647983209883437954337),
(16451776871842939032666130442,84571491716697774830320517752830884499492268821519677990249374707217)
] : Array (Nat × Nat))[i%16]!
private def pack64 (i : Nat) : Nat × Nat := (#[
(2891927811,1108617090),
(97514885502892165092037001,115135524893959428),
(341765626381907278215,101942505187884287229930280711),
(16451671776188767840951731338,203519853806074481157),
(8423342977674797861077570959883,16442059961341695737072640458540307524234),
(53987489204197752279735945,22746988912003),
(131293121872191526945248997178673863203853364446459525983544257220530085019,59774353696007080443401338787276379886126103661264935304745139185144138199389356823612795059821845961194821777642182686),
(256431878656624076064939447614597389070026102434491261686609877383847834,1528778011238966974469),
(182527693337955550215,4159304264869328623991098321783597833),
(53860045016898659850264201,12571924804220829391193734),
(167328148231028742,32263837111905139410871421511504012564106),
(2834070928228194386569235392439169129614,17713415554460777106372434324593583436702211784267789),
(169207926931598353183624,515346359335337966610502760191112),
(49041920206919939810993161,111399701536075268),
(80424512527457514336392,731199874),
(85672761159691871623,195355315977520616409556296446051130402992297870538465562230334054499532538551812275493364852759828020781171341723558181370875220869478314855291698234768752417639496786027633889478150428763892298290)
] : Array (Nat × Nat))[i%16]!
private def pack65 (i : Nat) : Nat × Nat := (#[
(167329611640023174,153546883284344900229354664483995545035266616558521282574),
(2656062083,1027729666),
(40249416643248154927619968906,13125895074051),
(1720585987,542180482),
(3330635653554993650342209503681005325,188681625080551044),
(1780369411,559230978),
(47931607321992537703921289,112108018823653508),
(105913429141237124474245337966173075633356617233,98467590301175868792240411143),
(1543343260938426697743073219572743053,181965772128045294443302098786209872521506135038213886606575131529744178397666687765),
(4323330810497634976385916860123148,21864197186307),
(46760957102698822613272056458,13565066037635),
(371863420305759359495,2713907970),
(406107950833902217606272811100232185355407,2870847806319149646769896465712904328498784058119189963368611465745603816693806793579254090816616857),
(2120621059,733044354),
(5887387317422551184165161600395,58298161852781877410221769861792997542376639980868177265346278260866538769843991637004420382831428276610998240805813254999172791073),
(122571111416780310535,56999563747209374973123804985585885788426)
] : Array (Nat × Nat))[i%16]!
private def pack66 (i : Nat) : Nat × Nat := (#[
(1251415043,597761538),
(167329611636802822,32709990465651909559250027818584473158410),
(3288776125124271192141201892899371149,8856528529662455191723414983111094440008295234585075092872656359408644974739),
(43864453713759654190984,99655991275744150862738925287464849745332215235107222694863946347449564990742597649189587372839215727908182927787497886),
(43864453715685644777608,6740451995704513187760219779718506633),
(22458600301444942950702473,2496441577094355479268497869274568808484833355282406702238439430443325338190993749928949022727180814273504981507885454290801636532848769827),
(43864453713759654200584,128607602013700144396274447680226280104152186671115215158396033362416052901911617556602479792741228853617014093991384550909022129092665813748759333),
(790191749629794396248881633775083796622,179632246747081959089951464825769773846760626959264709547943711493973483541290402365934567346957055998365851),
(790191749629794396248881633775089032590,181273192130309948877065339703822601924033240383246670836769767694904612917388527497518503395827054902843803),
(85672761159686824583,3231478502250122462179611437139196585007790551962949945247714688240437255602467893850932074834361566666488922667976396687551494228510206565057575018491200122203615397446508954541),
(2655272963,894545026),
(138677635,76854018),
(48442757376357290794360713,111400190993510916),
(703758451474693,4548482474476974769332984546954852617),
(1330431761992837,11719424596099),
(341999821670186765319,4226994287012236532718086497365024265)
] : Array (Nat × Nat))[i%16]!
private def pack67 (i : Nat) : Nat × Nat := (#[
(404578175810503940697068942575040619952271,3077357581662379743444851102063514285237240748240490399119191677891435497705361135373974),
(2598498814212,190573455899687300),
(27594729590020949913179202826,13770623661827),
(11498803354461408425031114122,56327017239112857064208654288201400858979913190035610131277089081472103765446525062478985934184689915072125520008808382696766392353),
(2427741661654946425012233,106820062912260740),
(44954054402793693254042600202,934531694529897347077),
(23231543933394228811787744394,13014064523139),
(116931611702583190657876051061202481234426134338706,210957516746410743845220253699096479178709872882364254183325617984567526558109097871568442567320),
(22458600301682438330138889,5823905035438780607353415962177683642805056225579854618944054962827297315122277924971887141381674191863340916701868380972389005387662062966133430329074199455472109610),
(43864453713864777205768,55284407063085813331077286782204866302634123),
(22458600301682438330129801,481126259470437179373330313192178380200503152638345766946986256531683982680260233997532589029699742319887451851326720699914655347592994),
(703758107424517,7046049545520784214534207392890239241),
(34158105459905696880591772171677245569334834012891906068,6582074288110672046215061755902793609),
(1780895235,630271618),
(27802399959943377345991478552422582137461823661474067,16925575796952896257790416355303017230078886819995112843703956624),
(167329611640013318,6962800946819059837701865773190961872446379543435504093759336769970378977385459304874443484826379342762943203388225778728909600)
] : Array (Nat × Nat))[i%16]!
private def pack68 (i : Nat) : Nat × Nat := (#[
(326815647728261,267961709292233594986744026335284198502646539),
(3288776101340473880871335792248048269,29313005950004407790824145495916394695170523017637901),
(655257169220305480923448822283,12019191128143611279249542),
(862132916872195711205970811661667558245647,4323755401276115554335379850342105116417512072064045368259172783100195112043964963895758024629412161858175329165691517896178464),
(11498803354412546729278257290,159225469310633407633571129076389081898603671635383257321969070559460361029786518008612706626512061188952859429290146614493800450920393670565122853),
(11498803354467020316676344458,14306106565428156965859594307720230107442969141857204008527556034543539824064917883251900940329731437594),
(1279799158633409142428617226,98461215158130392739361394823),
(22458600301587005330621577,19436702796708179642769913214624725635990427226424579802928249021881236798679571014116383166505312700808555432917793068173566813503022960038692),
(22426814161823658217853193,100861300919188857900004186759),
(1541158934031980547134637534048047629,1660769050427807182032519950869095087082938039072185982155804570012931833712924799409325304901180057),
(2997170179,1130502402),
(1745356419,242250754),
(43864453714037119786376,74571466070990906840744373839478415295159005689297323267655238667688849306714998984727568554963389463181562001826777934987957640595618593757183005140684625476320981267371),
(22458600301692158978116233,16302693485116834373780965239517702654844790186226154700252992272),
(11498803354678259107259024522,2085101150145915320319319810692957607957362512082221185289652684218976672585100836340377598355675995340157444694528183296670633707939674664327140660902),
(85672761160228749575,76870101423113028924662984971673088789080298627021754393228121390485618662813862300540919516207052661946989456895394311258205610062336011730201531926162697263827203201451)
] : Array (Nat × Nat))[i%16]!
private def pack69 (i : Nat) : Nat × Nat := (#[
(348854740796269284487,21373302031235),
(1574531,66068482),
(1886003587,758213250),
(2084509499027213401454156176100395316814666322192713728688083382680,1431226981855408668600757004231391312639549279578992183707957032209523698841062549178369726177733229504727987509801278668278173199055459577892),
(85672761160228740487,1096668981590539596129443301553106471889831920247551356923907742204900930827648592010267477786780925552438058449816399001987577808513838732258280716629849731832233),
(167329611641071750,235150167448044805676094613626612209191961117595547277710),
(27816772371964373147770077527662812413609566089321619,236120313659179563247121968555189736489191261666380419086),
(547110382476293,39017090),
(167329611641068934,1207909380769804248654715250880727010749688793085521769819907914607338979256332064006725065003072475738268993166935214840374065669430691652235223892255759192642345),
(22025580211234707923500999818,914347612836795106949),
(45882523094564836142096271498,941463581272431571589),
(326815647736453,1249532935393986391106917000138319236283473799725820418814299578354771736547300023270355694666254718517571768079101151433702444306182798131149772085919434352080334818885335582762012451215758596391219794612686641564685231582271598575087866685),
(3214873375470816293604767709139614839694,4237435938624200736861052286195151881),
(85672761160629963399,7995962004978065790820909723773393042720485728769489246993597519560618363989448061897539167348135364467966638806225546805582479484980734315545497029255303825733676631578209990305735516939420624777988366516),
(167329611641855366,6981143274454403066846186407935941478144867989329409888975434521618929139760095292105117599585061058743726110006258090279002272),
(348784732269958940423,7707851070561810853868550)
] : Array (Nat × Nat))[i%16]!
private def pack70 (i : Nat) : Nat × Nat := (#[
(819294241376133,990180098),
(819122448309381,2892062978),
(167329611641866886,818318057233321249877631133041499466311952650126989844018675704500318597596632036042242728803215426449518651436652053222175),
(3288762970510522177072724644298572813,1496102785656113360389),
(1953636739,808551042),
(651842655092493289460670550283,1192682663465982594099046762901578438769504730730601069750927),
(1747800451,2208383746),
(4327043,2876252290),
(70665648388,2169477126637471145111792667506760483235309103756),
(2345885819500829152868544293033004763032462078487059358891472258200,631551626055476650198020298023637702460713347909065664650885119749614373538731603093),
(66792483834078577617980397593497795633113201217904531,5173670920646464718422188522545297165300050704876386587054699057969725314851338758477846),
(85672761160629813255,7172440284515293969396136540928339293696913465238739197376977881443668075319817086607334725580596589239944671387491118962607207318686179021332227306152860269763813826175550628998105059061198236278909083978354774074423),
(167329611641855110,481265239443631974368820382797749720540024444191282626642704006842928816426305762298377092973737715011916678054444444988933643849523362),
(18244096652476422,21777283885699),
(306756633567052550,33711527581115660005119892130875148685322),
(298045024178304140295,54791385438399867574525549703)
] : Array (Nat × Nat))[i%16]!
private def pack71 (i : Nat) : Nat × Nat := (#[
(43090486464412071202118251146,13942670902659),
(115713060067010456472072208567402948516958303761298,18498326250264333480858935880536860874832296207922317),
(41199362178599699309998857,22987824983555),
(326815647737989,366795720294318825306980236467864498181331265417867364013958653087371040171083192372525525334482865617462001130641808603762029383678041789060963284169251174520168188692770262562829066415),
(667502311581957766,190640070419867140),
(234257552529694470,8075267559821315500497030),
(326815647735173,323491360836747210643962333274948377007505920124753826743407183069930769698581340429469056456113611193039392012338847469114855249142272055971321260888519422158180982820524844),
(9530321564116926727,120134188555127172),
(326815647727621,32301799392680212232019519419855956771950588673261516119357348119093110318744935851509994647616770434471494017713931167283618316754260826498908561351021575666228428942052544615538631129751050570873412023449887711793702124418815585467),
(59245130652648708775138282866355971114733456797352211,1269655232149482169492831602995609149235983073266541278844559),
(115713145805954804729757097541560290303995329780882,85205062463360173567596372098988533914264892611465003419291700174097),
(234521707714334214,33202069699058762438404935997536830792202),
(326815647741701,4656863417459444930816554123071406375142724704651216642878007268787859157086642675807991430045093918486295096615032699460726955469361512327537315385011751),
(5369262747063502213683568221721936141,4200936770642260773236657200557104521),
(170393340164408263274132085634446221,9905966451386842294578189100504073721007001910924034769264326928),
(2694590339,1074921090)
] : Array (Nat × Nat))[i%16]!
private def pack72 (i : Nat) : Nat × Nat := (#[
(638311811972,506657774126624421729062100427398709197148641299128429280230422957583020062969852874792055830073770207516576602710794466828398514681233463746801497556248294733369012909711532959183957274460707649808763578805994294),
(149879814483056919943,2516968282627),
(258331217991343936647,2517336370051),
(476580739,305173122),
(1251299715,2452903426),
(3490597123,18193543147525446119935434095978405116552724855747725),
(1549106764422530586333586827185438733,168154622595262358117227142951746850021491067828728555574544162822360956765467422582190645343097996371653915),
(4371857539,1403166210),
(12186894296221608288559914838926732,2933224962),
(22458599986696512300141193,268005483713616836659191522280454105752886773251059241230),
(61778067596154506688677641,7339235460094594486975622),
(2581350860676,1203800231867559718789),
(2455886240592848331740186420144112141,487834927648748140624726973128591938068758923),
(1428647398788,2771601538),
(782972850623365,3542611374259293407223758021236155152344779374604),
(1755845645060,693661459831736994053)
] : Array (Nat × Nat))[i%16]!
private def pack73 (i : Nat) : Nat × Nat := (#[
(22458599986696512309837833,525222286846371457630743674009829564808075414824996176029525272308307211678428739897466108695437098049888086513992822120095),
(3632345475,1155780354),
(130165343137079550168328,8633274616825158928946438),
(50266434932869545341300873,7627216274273636703228550),
(50266303664471035674380041,189964528046445516719773526608026826907571467),
(1321274487755269,283838883846174758671974246040342786716526091),
(11498803255530836547373501834,5459650207083756215215133991414701995404181884305476391833762975767424496403),
(2580612534788,2947803266),
(356393520242445446,19123780009816992343896736430500491669002),
(4430893187,481355394),
(34672720569629605447949683594,13306120154243),
(34721715122388426315384573706,935098727107441899909),
(34053748184293978270594173578,13297517635203),
(13321912200133962556054281,7395606404984440756425606),
(1688607619,697387650),
(23728184373038194410120,2957345154)
] : Array (Nat × Nat))[i%16]!
private def pack74 (i : Nat) : Nat × Nat := (#[
(2096683569924,13322556869483965563753478),
(5887387234912570522945974845963,1236372697308689983575786688690615451225224418788852321945255683699739788369658613846663281556376598427996214117346151901148284542792424683606072199443875127196457),
(4370810627,1438821762),
(1543343248296003414009029542160584845,13535368453685930983959489976040832494119850553912608491275646376544556865311843218441544563782014553210535932078877),
(6423378169694435964002625322108812,1728414850),
(11498803193188614302628857098,13347035804424570431437574),
(22458599986696512309821961,150924872952565758170947111214597536386289027024967244779317752886146476658465351146958771276525337098994780230871833333265256230873414120296805414634509400872),
(43864453099016625605128,269158318278871465585492508174116679093674224170558649102),
(85672759959016846855,1494959714169504682245),
(90826181420199468816093705,7717197787044960003110406),
(105453169719158324396936,59770307947638553209283631111),
(11498770620371739570845975306,13030958056195),
(11498803142455582431261100170,3024643560888262585304522564727194053443553426519259057933618582768175401585589707616073416568017049),
(40249494190410489113173233546,13297693788931),
(3014342281744450323956823052735244,1683228192482103374589710945625774605038383955678419652239968400144713154120426361596867094977540889),
(1428658015620,890265628912231340243767962847368)
] : Array (Nat × Nat))[i%16]!
private def pack75 (i : Nat) : Nat × Nat := (#[
(85672496553697609863,109596445402333930014295527559),
(5887387234912570821674799477643,83668571306724536487005004622321526946532407450718584686970274468091394671273504663372814310910514365213929092353336182465358383908841463691673644710716764584),
(11498803193188614886083592714,81055437889947748128560421841032874106355316377572402288883357508661304541672212),
(22458599986696513449382025,5778185253281525970967812184278719751040157206852185816391407912858625082387),
(43864453099016627830792,2779089626776361012619651803780983544671692485388),
(45895850274572332980540231306,943772450550082362501),
(3194726981464753207171151804395317580302,155275688129093268793175841868786455895545818326981883150),
(130502434719482854728278151517258658837275066904722,941049647439705621188062467841051461977783975948),
(18296569949102243289847766154,13590005372291),
(3683587,17726119496801269672933017636458520311559133852817933),
(2238158605572,10130561198597291462375400625271086825634710263249693353966805648),
(130502434719482854728278055228120824586978160233874,23505044606467),
(207144024310441978248053642894937256378848016,14501988259101840875067039137587427122012626185497625920067065104),
(50300423223741858318929161,15169690128623385127187694676874548729098),
(3014342281744450143522811594158988,371587671408869957772884224235557870415200501703980040293836985935733184543342073352578037780632),
(6746629031116712809023419757048588,272605543405590038555449466088460292200274305784234738702)
] : Array (Nat × Nat))[i%16]!
private def pack76 (i : Nat) : Nat × Nat := (#[
(85672759959016851207,45377323004546452228267795918135748807152703947032830981001578451108583514307655436871160087),
(783902439854725,278776650324438211319905968136621154625491339),
(645433258794043526,23099820280963),
(3709102258192082184982484322351137293,10050442667082618281313467578470354037407222832703860954767284893556754598547),
(1899060356194346078711031973043784008974,116191064288436458493393783394579857460076280432298521681794749451193432719902263530078167224545894291720859),
(969807078575621,282444831335188796814038219017246306846627083),
(3709102258192082184982484322351140621,33242500166532116799211724793119090787473873175942541),
(14149085945315607733809997362059,40729815937633042083738143405622740356371387356237305286549886071903535985032578978332037399),
(18296569530428006168037765514,24448110677763),
(93472634317940431539336,6234082585196751750859885894156150921),
(3429582851,1249006722),
(3296998531,1173500034),
(254288110910282415495,955317355351803009157),
(3497932163,1261591042),
(2997158787,60231689886374350329162172509065142687754),
(969807044431365,282442024169219052087914677190841384881498123)
] : Array (Nat × Nat))[i%16]!
private def pack77 (i : Nat) : Nat × Nat := (#[
(346544350378292236807,1638981795754094573957),
(31627125175804667153158965002,13297508187651),
(140976180115033502343,3927999838608173268669667863766997641),
(401481296177874310,34244649325378033643509854375161205446666),
(167329609294954758,53026760081109446806607845436574463385325782214890999571952840119786477813254525882566737324125485232951759423380716082888208017056199827799804220012022135194281992592645145644097622319),
(5039603715,2435067778),
(5040263683,92133536849737348),
(2789491203,919713922),
(2990949635,957467266),
(110306691,2757974018),
(40561278459391878,32646179747700991864724603074422658577674),
(4870188803,1000556162),
(154728998020,24740789330051),
(43864453099015889635976,25968675341318193220841531901360519959818987875734589737483911661948358465385890217859033015537958478229695184365457262248557957955790239505451306467383448528222265663500907219098926),
(204211331,2390776834),
(785692571544453,281569603451075543067860035649480730925559691)
] : Array (Nat × Nat))[i%16]!
private def pack78 (i : Nat) : Nat × Nat := (#[
(24498452314496701582328408842,13762028497539),
(177338468786554539298824,62947578228087212205912841863),
(85672759959015409415,1280350741544690348236485232564622558258423742141056227107014408561359514967458143511927464411197913093305230246068108193303888046766835044448922333990),
(404580703958183752798290565438190253984399,25496530884041965951478405141063139138077177437876940256114824657191863308483681867893415319),
(1683853284350257642199648226052000859150,10672260457061039351605578640071087090530238547995936932690553515256763443264496169082939072387189099463478572207056960105158683253490189792689289047678503),
(402238140146459526,2778009986),
(27641594515315479640113752970,13813560774531),
(50266352145557634009353609,112953680993770116),
(3288775945996596957421187941507814157,2369717857884467305136788583622222213326736885009814454346159763657829989072689984400967223519715536179913820867711271238310412428564028067),
(167329609294951942,1268001876498868991466537600724069424483990946421813204500972086306992975566310724534561231803232258170091090877402301463877756344184187674899726579374483218723625),
(5513891971,1583574914),
(116062807345882509492744,198238339974142340),
(3195596691198494544654071210350219510798,2329554514760770988112960333986388736445436401548),
(1444349928031493,283140453478109250205040119949012103897333131),
(5604191875,14562541916803),
(27630189431544933783837945354,13813605863043)
] : Array (Nat × Nat))[i%16]!
private def pack79 (i : Nat) : Nat × Nat := (#[
(2919760771,197156098),
(3701213187,196000343269840900),
(105400837462028911584136,7529749920743305496792806487596677385),
(47822451010859960090174217,7471176394444973780822150),
(5887387269032133584615242614539,13650337971770875498583796439882425838758477804129928066033938827567305110701130370061416506971417009617345520620061),
(402237345507388294,3043294722),
(131726323354119647879,1813311618),
(24498432227204445316443611786,203091609727966852),
(266574463918744070,2739226754),
(226002962110829543330804037014840021110202056081,153182335515389028886337266062774934396058649887557821150847029264401),
(23802571483982828464613757699339,1279081326714595725458411249526952370235309356722429942303887),
(226002962110829543330804064156804358975172791697,34013311171008063962158377729408970268165939751337997),
(441412035372713951817976634794609416230863376,703182395796925294341921526392379990924770398092277265670295638025486354),
(1895098109188,1798616105917522494011755406517872003382829610636),
(1683853284350257689735323466465970045966,56786853591175469813727940307823113662346),
(6423390519524603438262275690418316,688929766744869091369690803173919279779239439993418606842242755061566437111783092117)
] : Array (Nat × Nat))[i%16]!
private def pack80 (i : Nat) : Nat × Nat := (#[
(85672759959019082503,47803493842828314258313582193620250434502164497510368487980749546849621860700436),
(167329609294959110,479414037936488661973918477702553192957134520826780124825121880071984491839975331017117535405640409070420698635109254074217506191539098331252672990836883160658729),
(969821334161157,1224067025437637410877695760042538047998509607193492793333775),
(1534549509508,558216192529552183685),
(5278944515,1563669506),
(47857779015615606270805385,13719105486361697537288326),
(3692055811,18240020058119854337274892431034809199704810624129037),
(326815643154181,494489201085027565395344477378078592514239728671523791920733920036061246171164013333),
(2581420326916,7350125988809596053125932005926889609),
(13177010526490880090396698418571,518205576035153054097615681280904),
(820150144147333,499080572419),
(24492362044544365817595764234,13589995941635),
(3014342264298799612149827691695500,184418624426145278012570182978211659657623714726553966623701432256782259370004585805111034895244573432723099),
(43864453099566385090696,2377007542869922718162609738010448942866913225097296708794218794124139057249865215005420926907408843282359799989729094940951770554448573219),
(5377643267,2558739330),
(722045936125164934,13705979389251425370585734)
] : Array (Nat × Nat))[i%16]!
private def pack81 (i : Nat) : Nat × Nat := (#[
(785606662106757,24931031190659),
(25754533146637100743274870922,13702263832451),
(112364948003064508026858167908653437091658374042419219,701027495356740758530740203683286337927943606888890010968590178583787922),
(1908947746948,2719238274),
(404793380603248485056039025028070473466767,25698957276352851725455315444430607376992207310693442257231355926306625128543220265085145632856433850394),
(5887387234958723904272154500491,922433106578570129393471564334302392803306449840783848856025345109903407939256345825375623162062369002954792732),
(167882134877684613331464,514398908870031088729575604272648),
(790612080854782220154377786520353178510,2924003542988514643634693127907483870220045915670558262414841419623214472326263083320423002251212425774457991957046302),
(85672759960090595847,46321651632659756890193252042670791932352133894913332197100202043317489967522892349067256120450783278434295927879049601591144822762975257851973480462897988394480134615851),
(85989927092452686365152009,7721871734202851716735622),
(6423369784030151458621186800164236,686765315053779652956385811570724241071768571751961981263045601367786514),
(1597769457540,14724012292099),
(50239111790117736207949833,13702705281795),
(41885827,1797587970),
(1683598460926726970331816990741765049742,34460567503071548454385233848248491137406336683306765),
(441345234939305026334981849396519252342231824,697949444146414077383998167693490482979258440229240023066064377470892092772864725397)
] : Array (Nat × Nat))[i%16]!
private def pack82 (i : Nat) : Nat × Nat := (#[
(47848454412122503752457737,52517495117016836),
(159549059219532549511,172755903318287492),
(24503290250876653628303888522,4151621299702430636416965657424016639614679408731299806793702781082228143270422934177309694405401789455292829502452989616817184),
(586631687150782854,20522814709763),
(1544164197828335085320339978183652877,681143124728528033895052306325125408662174503038197705645843076478081387679531208853),
(356498763049421446,795798269266942228224480981907464),
(676791228076146694,445020687890236109212169149823368),
(85672759960090582407,278788299852541620135994807591867149571810362502827563681235206242115297251201409885171369404220317749464787296132832544431216211115810),
(25135449853969744936306941706,13675995952387),
(365768090799001222,11348823848700299028993798),
(3091152259,862144514),
(1534544912516,6225071745946864556808710),
(79184134487685,2479140354),
(51754911023153422207256051210,14011551880451),
(11498803193278992337772104330,300843376064383368112294960230517621730676942310309548661950205882254655066350678553224476269259272410957737705330839677784701450639010),
(167329609297051910,13736562599104213864159944533753955929079205645075944752927689401365826726745798897188250592925645649562)
] : Array (Nat × Nat))[i%16]!
private def pack83 (i : Nat) : Nat × Nat := (#[
(1534411090820,204570993327652868),
(34418897512857970662279952906,13891129205379),
(27611429203439174723809005706,2092752549685183045988702876449630347842272351204904538478095),
(93271811606517430842249993,943769284145767990149),
(3288775945997228460876812254353294221,947713812654523113969081027888416925004893178711480613718002131350716443574859711464327602099153138777763918399504177756831),
(1390234281853445,273894044172080560544101825775282981987180427),
(12191987194946577676000810855711756,34713067334308676854183123527130348263306),
(2715301331460,3115497858),
(557025085701509,278951385320245070748073041177750463666410123),
(34438851873564057941698231562,13917012250755),
(6751392666616357965628556020959500,4244927398661491893890356767326166883803577068556),
(5512578307,1498745986),
(2871156358532,1761988354),
(22458599986976764027220361,35467914244482845013057853543329476397726393536665336200895047666761231983478143658557990632524481815163532476424839157707850480239375971371684),
(5887387234960426124657897704843,13739073942643028650104326),
(356498763049413382,33860144256760262392688545177294282802570)
] : Array (Nat × Nat))[i%16]!
private def pack84 (i : Nat) : Nat × Nat := (#[
(22458599986976764027228297,151213840009008116522218911158361026357813628969583031637988596192188901430237255149925445652446273281954464160344883267779847562144547699847181989),
(712432686623506950,24888044846467),
(50338369107908574828642953,112949455121291140),
(1322234747568645,7729679287970356734315518935724039689),
(27581112867421168912156935434,794530624413945260390571631288072),
(3288775945997214460062330728824701837,2321688721262458194700648421815740891744837411000171014682735363226746162040511192748979940780431690931899456281131510120334063157691733696416748672934),
(4637080451,1213422466),
(53869361069182315234008201,2999497852581423994989181179117447433),
(1986141187,710151810),
(1899062963413312309776418797338295354638,7752644028256848259986397905292617865),
(1087941459332,3122764802),
(43933808681193314715400,490274084126568846619613107200776),
(27817166342436181802245708564880047797914422210929555,359041597136453347827354735202154442511127066819192444932401845928218200157328686997),
(356305216991273734,5167943676640901599713030),
(18878592953782169589219002762,13065679539459),
(3759150211,357607554)
] : Array (Nat × Nat))[i%16]!
private def pack85 (i : Nat) : Nat × Nat := (#[
(544347523,365998210),
(2714963558148,2229467530378005594364005176024180991875272268428),
(43864453099563992240648,127727932987934757184731726239638825405001618286686011430299121463271958084534968307471843098658058686470783339398156869713438973759764719472021669),
(53928572662967139877269897,24115058841091),
(3734255107,1808949122),
(43864453099563992240264,83130373401679280346264695331950375202591415442617850799368261059209739475374157914600747511856115594602144834152332542699550529909616935165540735962824694824),
(22458599986880007000306057,8494423567528972679877470296568788779540010412800325917194844030056406007639535958010557768826371192291520726870843747109025001825478422882468),
(43864453099563992233480,604592269951693739303414677568018656708139444022105731626684539796265339963732874591961427693121392913390600617412787005629581670399416853488569354694282367173054389971967020),
(93404094458119254908040,497685914405999726341),
(4942873091,1465038978),
(50301795204105660365226633,63342779326911282142251103489724721015818),
(13186313801985074229526697758475,25833054265347),
(731092195686533,180095772495281668),
(94491381150117748552061193,115206211458253060),
(275275297428028038,34009085171071424160589246460312698361098),
(115713516928096355928671574386732786326442771886482,1726331465581650517748136008288207905046608887154001862886747205966407292239243366817486987343857865815996323868)
] : Array (Nat × Nat))[i%16]!
private def pack86 (i : Nat) : Nat × Nat := (#[
(219631314959344017260437952198969744161496682219794,206909983696473604),
(428967412029968783711792875388612781565423207441,34713067334310070674817641951524106278794),
(7315473912969551911244236709110443772698032002947814459157,794530618326692802365857542005000),
(46488754438232829895178270858,13899686635651),
(5308956547,1339194498),
(547239939,3164986242),
(177340661824359656469000,14248326882445538196857606),
(3733559947449122769909484387531195732803872049720256151310102,4866659518195465659797073164449870923307286752752752796115864494477595236115),
(8105979940025554601902293514,13306286976515),
(428967412027344970075783015240403880058593489809,5767697615041570186415723932392190098572787848945357304479734281187834059411),
(1249426595645189,13222785275471237561451782),
(85672759960085922311,64576526786512848628266913193067141813979303509285759417783725505709363559682583073709935109604500359033708367278802057758498728531294295114449397207968929251222937625404006395516554017867698741113015844058805),
(167329609297042822,19202026410946897181432265385246044666057650293195908822580185744),
(5887387270404110183721574080395,155089526758579438554818193826356708486979661314152277258464739514001),
(4500761219,932298370),
(1253696784905611612457337098,13142725764099)
] : Array (Nat × Nat))[i%16]!
private def pack87 (i : Nat) : Nat × Nat := (#[
(1418182599576197,272320897768737036294463068235256423214449547),
(3927116291,383825922),
(2015450040708,3178621698),
(441410570440539314438991270462930107634549648,5890580053496971911387241722508262654068716319417976617531083125620298235383504858046742),
(49092843691810948990706313,167624139413349508),
(35635545121285,20939490430392327069881228965589176986951947),
(5887387234986483521094316851723,15127737282574637664304541991409122295690980944736008416832819656528352856558965781041373871223245873414646842920215268920163415713),
(43864453099567521681544,269193412094794353305624056971533517514303774767621876982246062031111842935053525394096217034451440007536690100821525080447929791395490),
(5043929091,3068407682),
(590932544856738438,2333253378),
(1683853289113850854679598428600396104718,1478617484316785145779389120835488487579548769375780601508296599289652806471062730625333463038792842642998022300),
(6418471885018564150589288591003020,62299478109841718586902405242628897822346),
(3288775955300489950546090680860148621,8843408566856958421609802956212278728848462039622867505046451359510504332741771628847029085005619238064931611337642378443437282410144074255829088143398597127023481002),
(44026208701739862313363129354,14020245626499),
(401904334618959494,25581664404739),
(4138147715,3137718274)
] : Array (Nat × Nat))[i%16]!
private def pack88 (i : Nat) : Nat × Nat := (#[
(3014342282446904414636132054353164,16085999342530596097398817335219158697889935270130753450047139138930583494287654690150107182188664842446715567947082275096663881799544632453847255044420391),
(11498852725087589148956888458,1354575996508284699101142949912046428010000486297736172612239),
(182162312949755323044616,3113596162),
(385612742154414655879,1228806938773559257768656551894064576403813643088857068158351),
(1471061364775813,272849951249108624612687069792366912110381835),
(5606939395,698437378),
(2873166728068,26211088648963),
(4128574211,2642462978),
(5611653763,3201693186),
(53986479244907938494612361,9776895104435756980530924708360114947098967515529088348443768592),
(205473120194566038407,4120312591771626066399248903458480265),
(43864069807474460590344,621262422787),
(62325935818178027183875209,106539198540225412),
(972148470018532036761088881210270311452559,154026489644534506825452613748450204381156536520147993742),
(102638723,106968322),
(25736385310578470447084023306,925285380134492306565)
] : Array (Nat × Nat))[i%16]!
private def pack89 (i : Nat) : Nat × Nat := (#[
(4769459843,982636162),
(49129495406829743280528521,3211131522),
(191751012634792829959,215546903743698820),
(43864453099567521661448,406237384260270174059952636099622618634633596838025470035834358662808196099838519572876098528467048349428013234319706946966013744793916549463547022503320756235467263821662429652230458031),
(54301530004636991558678208132372529035121165222418,18899262946560030563050768534876362625013387134763308301863409296),
(205960028403064192391,758260880044517964421),
(501150857740042886,942868409350186867245499844537352),
(85672759960092815751,14748583424310695323994967870522654842953555165728262444880640085340659139789597024376681127956825255190098581222173),
(68631441269646074249736,828844968173549231208202404844936),
(49129442032568810154316553,13962585196804990318322606309876965152403015389591633418612166672),
(47137716876170564790163817354,14037422353027),
(365303429295719174,378456630097247874670499673961993025901350923),
(1322235923481861,7975820589548320582652344768067399433),
(207254041811569684630551699436317171686908816,14140439472598701750534022),
(186760048856422117034248,514078746481032997700208742772488),
(27628258466511184765694983050,13633068351747)
] : Array (Nat × Nat))[i%16]!
private def pack90 (i : Nat) : Nat × Nat := (#[
(676501539542743814,34648394650296803598666471800963824085130),
(27640954518101404217429011978,13727580688003),
(3014342301086161195512367153414156,8084236574915495978406489096361235530840832948882605859167369051274985072175522328319305509372214805479091419987471779897897760),
(1257586629764,12350752475463586290029958),
(640920296168764038,34520469554966345766272768684112249798538),
(47821341949269837615145737,7471178126724203305817734),
(1883714051,1824609922),
(68772074491984493195144,3234203010),
(356296763452699142,1778458425540164767749),
(3014342301086161194686632721842700,3268459016368935740203339711159907051047773461150808253496782380309630099616833402603321862009497625),
(85672759960092816263,5995807162864867545512558265405941484180673215519513432551083025594566780437641480751766),
(2788833283,793869442),
(167329609297056262,1080615510600298440738038693749321815918691033836892173202191),
(85672759960088564487,7882507569642195600990380913861200137),
(6423369201956034347374909838348428,1677127354392437175301),
(4430909187,3117801346)
] : Array (Nat × Nat))[i%16]!
private def pack91 (i : Nat) : Nat × Nat := (#[
(785723374452101,26149112724099),
(47760625402562091884721688842,12802159991939),
(801497910557317,3158528770),
(327894793738086529543,3083086082),
(43864453099565342785544,35870953899617287892723161956159246953012786091493648014693563302241276915482766490917720964434702229319014975770332433697979415125096706468132),
(24503290251016169061100048522,14602763270192993032859526),
(790191094226677933239319346651988314766,731309736520305740710395797588838850728952409768812641889887564390948114),
(85672759960088560135,945469701179503066295372080334958444581531349989789904687236651095149832490131923092625444151814302959229728125254480824735),
(4622300810608922704928849277701738637,208795584966082820),
(167329609297047942,123913925246184036317443761488328254073912724670873305161252002494066775758872725394609336831483541294682836013618618066361212912142626),
(95955941468831335666440,26381677500291),
(86497171292760653247368,502653989232038971326445762233992),
(1251299572396805,8349821942538540175071110),
(1683853284350573717613161813190988222606,265445377938057249215185728884954186255032790211594866702),
(676500662867603974,25944735980931),
(6422110829254435140827565019187852,96989167484704813545911702919)
] : Array (Nat × Nat))[i%16]!
private def pack92 (i : Nat) : Nat × Nat := (#[
(27802574274055376690741020397708470165636796771532819,684183581459724975799739737753611308359259128018288270432250403180826642),
(19301991556,14563045322243),
(37684227,44261122),
(195183413787696697778056,7692863849257853761333329856975559945),
(167329609297052934,8843408561402381625400267970245953805071096919641466684747177057502844000882407436057696388861741965201400356619570472966331874468561389789669244829066114138610430762),
(326815643158277,3972341213808400925950825512737689918569980472445032410771451176491318587135385342883756572392649806880156890363228128492762784),
(971490834857884215093657051966540632507663,845256033543292588594428249361032),
(254669600557412037054318217983973028349526888593,14012034576241353566675078),
(93472634318834922364296,6985595113370295641380217258282528642609827472008993935218694900841504226790047968183120083111241104835825816956829),
(1053447371396,3246720258),
(1050969193348,839226242),
(167329609294234118,167342936800317251030183987550228603489985205727475030710915351207358389213183765775121002855519441785325644217056051261259785992890737354864125330542397059880),
(90838568435743246492783113,677696816121601488811706100386013103029028109888982271785898337149129234),
(85672759958648275207,1775294424217690573268646867228742308038206278557410727759802341337581312008732737674567692915962028678821216025916841526199892758970594083),
(785622372785797,12595159055763344852157958),
(43864452897582425120648,103368656109522509360248789511)
] : Array (Nat × Nat))[i%16]!
private def pack93 (i : Nat) : Nat × Nat := (#[
(187274055118988649095,3297960848341967751443718),
(43864453098827917165064,65682161509821353428818181169414314164083654182767319606598409193294251698430254045820396498350369888229777570207303663050278942369),
(43864452897582220051080,17736813848605474385152805396400634953926002654631565),
(44290330462924373190513861770,20788373867139),
(25147475219850014734979502986,13125887740163),
(167329609294234886,19164801435429781052124075081907474403679974646282223032459688543503365081003024309391061315527725507113188946271404341884418175276224997139004600937268827127999507249800240539398338856188022422950200365582755244543815699776580973371),
(167329609294233862,1255550883331160545388606208679953705611176114128437443078411877754065304693502048392852591657355057419066187140789093971541007157504966832508443652902),
(34418875078129433933887322634,11522213685507),
(226002210236463108978123808863951846550074901521,158747403415541609046130753017929010695380941620239562786959),
(167329609294237830,109307972917594405372107481611912581665505786318851692990865296650403321264752726043752056870905263094868765638977238686),
(326815643152773,28835732417542332450379302466830364351178853391277159927533236448017222672735860802026765838973449183430711923472847409076975834529),
(23812764505439300527970285670923,148464014735329519194477066886954009828934016447694274062),
(862292867433221,270054469611440288998849642079824590743305739),
(3430762499,1247123458),
(131272233383564021732232,13558102129917962988291334),
(497827302685395407853740600710325602472314128,205994818670945876369032361170818676761289026118445639038428493579161616485668604024412966341400)
] : Array (Nat × Nat))[i%16]!
private def pack94 (i : Nat) : Nat × Nat := (#[
(167329609291616390,2021125807421073464850504949119290785626762865484121682355578690474014574272248847893165700391697248935079988699645769876379040),
(2458838971268,25429099661955),
(3431543427,2307013890),
(11498875209282095172150512266,18641882051329362755780982662280435549526203706848317184507328528),
(326815643147653,157173522175713548270930883167084715208157247441330590539159458640632150503038754282700231658617521407588857580232192418372217375649301551192044325),
(4805041283,3295892866),
(1685577007108,190371257725014020),
(4127268739,3088435202),
(5551385656104838,839190146),
(7236896950933895517308916997824140,998354579710705940661513994249864),
(1685577024260,194382285251072004),
(85672759958784001287,14080072388736608913477578294859459766536291649715668103193156148440749116028681931906894288212704873197436377656839182982560501700959614876257226943096150422278662416056952748974317719626585521),
(1529049718404,221663281876812932),
(167329609294499974,55767183035465354808646874093471948997313032205212784371523342996679653075728209279628971190810175496624883188178990750),
(93454011731222917302920,13969326803317335022425734),
(326815643153285,19365005916781822817212588839929253631988882750650481588607282089001088647158488823168295856936967865873240442465731179373905195091589113193764)
] : Array (Nat × Nat))[i%16]!
private def pack95 (i : Nat) : Nat × Nat := (#[
(5169894147,18474237159479471289975757449981956229424301458306957),
(1899060450307445241366426580264702771214,4199406810513290333620607167543325671058829886325966559008323719858132245375266490339537024407285859463390828804187304424218400),
(1899060450307445215347425336173317408014,19806405825551684020829696225323037242558583721533197),
(783836199596677,11641094731497263204624646),
(1543343239276920847132820876443471245,644672840445775227559700380304766418048753753885060820301351491045841068750436458140841751427708722347507367670178887450114152409653738483804330209114134780302088932368413484),
(330461854873650678023,103026666181821802066630361735),
(3014342264212736029556290774303628,46852786403509445244250732381872498681185274804524134814757747337450958851600150406659128310410693055940845912223681790493143631255240309622567416640260770814203664888619),
(29466548284581303435029437111836341867261737758289675308437,2919272646510764638213591791392200526285236332684),
(5887387234790500057727130418571,5712136014413573279431160532371794712742457997208236731342082606765402445196462436403775060042887160687425831608551182946006688961201343476797154567001836836127863594),
(5410077955,1886553090),
(11498803192950195425248301578,67362861383893293503667668095256590951690),
(22458599986230850439938057,3041310122167855663932851915864962916972387845156928395068663997707893498362078604237150885184735511967509197660157075342322754447001484359957385475461930237794195398622413419309),
(257243458459536902,536860590812902900606590359001736),
(43864453098107129765512,22931671008699568437144687250382786577976214190294517053683751573831959801180106323161539809230175171354),
(326814601576453,2802041090),
(2990291715,835816578)
] : Array (Nat × Nat))[i%16]!
private def pack96 (i : Nat) : Nat × Nat := (#[
(85672759957240487815,14985894722966355218670854),
(219542892908505389068085992978421891232077636193682,356356524232239699648326943044993684901980299),
(365768934655267718,860113544458899601089088458039304),
(66817249502803089565773596450193879615167741235510675,120708581504175877917334779143),
(219542892908505389068085992978294975486209591037330,1319515266),
(54330447832868565657854026843394300897936447635474,2493881177827843163228763111917273851724668491823737223827471),
(207254210788225424415031535504889803760869008,138014972266462506355333201017212310352653038491664380459192684957713),
(501394858124677,7051157836343620027784384040643307401),
(1919493379,752968962),
(19093206148,3336976002),
(44318175998438117689059128330,13942699213059),
(167329609291485318,37092872106774792756226780760207851073319738409009135036723459748598122514659674991770498104829804362974237367018112050420469082785),
(46490015907256796125964094090,97996467639678036832395933703),
(46490015907256796125960551818,4237751441484899581047357590248784783880987294092),
(90800812318860929933527689,3341038210),
(23812764481763166880566004503051,46639119614349005854559967658501851316306221766170967780000355441202008911215764)
] : Array (Nat × Nat))[i%16]!
private def pack97 (i : Nat) : Nat × Nat := (#[
(43864453099874739561608,3075151907823994911098017167160563185316100249279603765946558534422029848595882718577966212763230233),
(460573276826516102,1442936934503603905541),
(177345183570706063571464,515666559810328499241511954889096),
(85672759957233934215,326105655588667845757319296208635807749372689027025535802583386830170165876575153372120833422104),
(346377311661535279623,3347368194),
(169209826472698704236424,60971092594236179229224160775),
(31569295050514968362883026698,13005459829891),
(2462326919300,1012557235881373537117425094573576),
(4800319491,547423746),
(4809232259,3353755266),
(167329609291472774,20945707317871764246921906695640768187785817710025605421474507648987813421254368866695496994419961354390536022980824762691837009992161804936062381043628199),
(2582358807300,940970767454263818866417880742280),
(644913774878801286,34584285328340807748079081295693152992778),
(50266183868284493662596617,7532611554863507920259206),
(2088382083,860985474),
(95762354277381586992264,3360047490)
] : Array (Nat × Nat))[i%16]!
private def pack98 (i : Nat) : Nat × Nat := (#[
(326815643147397,1881859863956534780073705320508756970190343396817601596415747098824019904583189518731358560945830224220987468444),
(1358457022596,1065193060945939066434096885501203037412198299276),
(1359897768836,66040466211506547684598838559130407746442),
(3431859971,212819075317074180),
(43864452888457765933192,21857720953742204809980637009524734132019649665341724939929787919463480553176045317391155037523542373146),
(2992001027,1100090242),
(326815641585413,3005708610876847596727779017244881908979581869564537668916097068119005356937940434449605970029331353),
(182837641507997888903,63933413472488173621801008908967738665098),
(85672759545122928135,5490624317925641215964875169073706125065274326106286802660358221264126118721019514811158),
(676844434031530502,3009669250),
(85672759545122930055,4173565458609444372769271306565649499587777776106288486235382847584216598158041444843872818379293174121054653408579586763314066653748491043),
(43864452906309329244936,9972231081597749138980626194402962480443825876627439251137852926896745366419),
(167329608486568198,873774332315029171002683615898888583488401129041851722737197006584318933124604629219454883735149720636718612723636327772959),
(177430734317803433309704,139903604546090628),
(2281833091,80749954),
(863033011273989,3376787202)
] : Array (Nat × Nat))[i%16]!
private def pack99 (i : Nat) : Nat × Nat := (#[
(3288775966759205970046059702772840077,455775780505042926668518150857994460055575947),
(19564392491367816319744412298,13039560599171),
(326815641575301,2614421122421317131809124770828876058773352941039072110657253879234413535228194552721249935744107799589889326071173428403945916011407280510058850081457703),
(85672759544988717703,280083236756918826544513561282957862611795495961049779873482609758680109380830233767767222724854029380468984432655776865697524862748761577142764453),
(167329608486306054,20667495868926003209251451315321804672390663331847343044798280464),
(326815641574789,420066963809531487723964804924495705694792262331071776144546267985716052545127700628376389043096),
(85672759546699993735,882222404194778641933475117904829202317874585620483803097577768980204946),
(167329608489648390,2522887679347332290425269223176757170407638226535427396226447),
(704754547052037,278084111844924245053078275384328382182421515),
(326815641581317,68736550017277208478177932805095687567757506339348709405367906402132647402520508147351572394873347463768968864049016519440041603873),
(2372736930232766272102626791323140237,2803083138),
(638311799940,20807786392520214873251776867256495600920028264782227200459002285226709370587717266937577785876064491172062315387114270148087465741209689654946391095866151),
(43864452906051432763912,18065284307288509725258343181997351012575292397523538936735164460012421057604762207726381487011414638287823672433931908849074800739958299796132),
(85672759582131704583,1223471552162224179768838312751439884094791569897606282385222844059894674),
(167329608558850950,2460970115289345650340256999776991798574757184610340193097052522070103303216406312429752578181841817),
(326815641716485,14830537870064336348235308191995496124554)
] : Array (Nat × Nat))[i%16]!
private def pack100 (i : Nat) : Nat × Nat := (#[
(1899058179468362376660159185000155455374,816285317533120038528922441550801775865414972770736870381327),
(43864304286714170920456,1190298770578686019912071378239776430150979543713693276891279),
(326815641711493,44648649261866133061697022683844422441530057193806766976697339305706694501635959546632182070586539355876870352264137002241840530337),
(184720612121930780167,1247664778688844251331014885274133837023034915805905807301775),
(638311800196,24053069426500083088696618949911989251477113945218168569913632982264836536897991153822097917798263443610),
(94581654931263318472456,912615697701429044229),
(252712941262667782,25350696583427),
(7244352123905012777695967711403660,1150701608928713000325),
(93396127079681188708488,13832447325284488234225926),
(326815647159045,1422522244140977440861880015874344896130735159513760827325950921974086734748620692879465687033801363427130119257045915775147366561752061698397932151138459489849594376121876745910003069356291052550593461098513901646647),
(638311810820,2369760267578590680544579203861691630002667794700530574892384502131713646031779580325261957698312996185752518984953566136890384610319811491),
(167329610269340550,480429797217177518401039334195259385816099299821528421817944891483701102495916393134255911383540766386106959400363764846723645016785826),
(167329610269340038,232670451470740902074462975604483490965704488016859346340314980593689113514977372667657692512084535963644699),
(326815645057285,6397561110942353493713086905066079113),
(638311806724,762463591600473817980823860147551703747768557313228714429136900550875228966764304405),
(1376345915396,9905637055731701140278554635111884081710538950309285157458506384)
] : Array (Nat × Nat))[i%16]!
private def pack101 (i : Nat) : Nat × Nat := (#[
(182414311699938812551,3403787778),
(24503290248322373440187223562,7725119894734921860618771755365633473650404609749393855341387598665871832989300671941281726310628259278206819078557),
(638311809284,24545142211980851484696747437981485774000049358483270376441371939331631133601333813956886509928057906015668233436082136897240792640414797945380),
(2694578691,18018248573357771667624002034749067082458166124180109),
(1365646360382853,2610143490),
(555202401067283334,33050670148824060983891041316688363776650),
(1246702723,13830197325911048287004644032510175728785634959016724448543869191731893182501780170147829439976170289000427063791122012456630576348694169995851817250859245463906106540629899173560883562488886065),
(2656586627,1038304642),
(2963352451,1103236354),
(2728077571,1065483010),
(1360167783812,2300905541220274254309305973956709627964834602636),
(136112793381498978823,2523198850),
(2718256771,119296868057683588),
(85672689212988660871,18303629357225191448929834746300520952635792526515327768788803612395786658717538735203555518498112483445775439023649636961632140017601856433700),
(346472266276151705607,4242634880744780769027615490203378441),
(1885873539,747725442)
] : Array (Nat × Nat))[i%16]!
private def pack102 (i : Nat) : Nat × Nat := (#[
(85672689212988667655,165424811710943909498373373768590428539841289075365104433774173008964424358067658424336867794740657875476891),
(167329471119118470,115336030214116502006876495367),
(22458581441048823346973321,27941464658198964201197711869935424123178714069808594851065978444528664189546487902766298677327506255975244718582191021304965430344683467726372),
(43864416877048483099528,2245704321187699229235643438078803567207396512660576669164431),
(85672689212985318535,3056694327273318843073363378711489021053838293122136151517795293003535989069260781746549448421826073),
(11498793861666959918126221962,125653030973362246598288205941965256597824565705079252659593243155985),
(167329471119111942,90951927994241044507628045269823278195799293051767270344855476647910338777215818378199278221660161609615402720573152798),
(85672689212981856903,110139541945979430448139603074597163496410761930290189285391831119297441953767779662904565502673520073328756172470511134),
(167329471119105158,150706665874797628327622174573478994257506659541131341267535970854417),
(167329471119116934,15724686988505278930320584899927900725830579588067251442250628430938836862360618136403561664130977750489567976646429),
(139628675996285793817096,515033662851841342653580258198664),
(95983287625247473346952,3897644314445925156222982),
(1987127555,803306754),
(355366347136151009415,3441846402),
(90851617268974720060116873,12699168855555),
(156147524040453360537352,514076309957115077980603918987912)
] : Array (Nat × Nat))[i%16]!
private def pack103 (i : Nat) : Nat × Nat := (#[
(2929929475,1113723906),
(112468571782801853710538672092313402431681689786777619,4690479394522911687282187187773153536776176100876),
(326815373279493,6024379075097984141964794463802607054121684177787441909121413653376148416066139459018500771155735554404264813362429958620077600),
(47848500443757825445274249,3050419202),
(40005966561315370433051969034,14028850244227),
(18327382960487336116605362314,13607208320643),
(914796161550597,18427910842627),
(34725604719779706776516116362,13934209947907),
(4210435,2249419266),
(32270051932801873381037393418,936833318008391942661),
(512569987,1977855490),
(624642973576581,1506306868342631182085),
(2391616771,975295234),
(120364418692,3458625666),
(154955623793988377267848,15537387688729230829592198),
(167329474536014470,17970893980177991773203162839153669054449035962113549)
] : Array (Nat × Nat))[i%16]!
private def pack104 (i : Nat) : Nat × Nat := (#[
(388506594901697670,32561259690729013941945406660068354792074),
(272559066147342532487,1899530381291933696645),
(19571367715364906091824623114,916046596887392933253),
(73812096620166754728747145,3211162626),
(15527672265811347543117086987585897195685671312342642602517,316594628365579138823634582187027663170823750042547015054),
(85672689212317583111,14526578388777763702338618378832131588022750335931426989773101863538623109086321000321170845273268201752242882900487115867728187434302118459475228076964728282174403987055121288034061948738231857),
(49045516669631904224715913,2436214402),
(182527543807059567239,28416405517315),
(5174612739,1988473218),
(167329471117807750,3687967942970482740160280271399399164810194255824495005255218720252423231016815890423318),
(203427402540589958,2620627586),
(27271620635308119163971323146,33753618961368836037677536860759467842186),
(36939771029753116789982729,12336964728963),
(25147573465849023586402509834,13762021142787),
(1356493353664389,284017744365470003429211882411850178217957899),
(53332286132941857715340553,111683032238543876)
] : Array (Nat × Nat))[i%16]!
private def pack105 (i : Nat) : Nat × Nat := (#[
(85672689212316338823,89139449801840653818037841449532503275460318946658668576862578353084502580976405969029987369531093435170311194901555882546489355461767429290905367736795949387312355498041970566795624872261465384588521995918901),
(676896437595026950,13634170827873262738044550),
(302647702996604702343,3460488322),
(3195597819091545761658216485261970133518,24895207694979),
(219457319733393689696064001620812757869258430828818,519907754092333729814284427097063474315050891),
(2919715203,18052775268467947453033850914041635260649083167419149),
(3193524313004363265527106118301029781774,2606884622999281107622281693396335550697340873638182527597455),
(167329091751314182,2975876610),
(2957460867,966904578),
(95983611884762829636232,14092127907822338424550406),
(864735301878277,3153449858),
(4467270915,927054082),
(355690606652916318855,3491135362),
(442074802113397965757865030400418677221097744,53001230052759104571535690387184306105205126282009185451576537068575641706905387875192699799),
(226342298684511573958405104550073813367494222481,5628500937073269573472192791253291439774115937277129089070784141239949495352684029836182),
(46515993716989976457465315978,214146203239241220)
] : Array (Nat × Nat))[i%16]!
private def pack106 (i : Nat) : Nat × Nat := (#[
(167329091751313542,32263393170207220501051709600274263211658),
(3196548907054098276270839601858863186958,11630808323548571022498904395069114124965585963409453317552299342898886099731),
(3288683876075754215341286502208381837,21289099960811399027510147479602568697570668932207922425512553104),
(167329471117805318,2350309526491576770608761578075598406019897696978658744760207),
(326815373276933,786154850616263588235245190034962277994110655820981073875415118706728212690014465045),
(85672689213390532999,8307106940901235591237798792600562746672186685107385168430770275409260980184280813010816473262694699138683985863638732099543010249098263376486642884885350532512012714),
(155017886286950708563080,11150295383899252569841414),
(46494273154112040464528392074,939158581760322036997),
(167329471119903366,260129395266430715771095527628143318480001440222304351438569513950264192729331648245468902510281419795524190125366609273115335749921874829096865417033385938876692870173457780731283446564302490706238152117809908243634924717369),
(1050898944388,3446019970),
(346571310163155898247,28210894356611),
(3014362367527439245559704125976972,26301413783743444863349911179007133572549922353281791014213752673724798424928267947901180692315852135962),
(1927442353924,3490047234),
(3014362367527439245559704125981708,3067622524848107728001183623735692253246043782862549731730715578827817001520426992300129821179403801),
(167329471119904518,237378772505908745510445064353188377225550529651097953434638655110155717817067365868320732976794664534695451),
(326815373281029,19162369029140605865179161730508901232184726746457478990772798514879256000863589483820299397607706386870421879966437266096348196415454827676964)
] : Array (Nat × Nat))[i%16]!
private def pack107 (i : Nat) : Nat × Nat := (#[
(326815373281925,41284797067222278427230583103414522514058),
(638311275908,86703257719115306462533456715311667119490222861880977998473867981735109759229460),
(3027871391210224519,11323339838595),
(24502604274280856923157053706,154833044117431045233796278947759198566039998925059502511265616255561449923471938165139484336361017986917313473999069497968792083245411416590854821),
(27268614927729706717529318794,13632970804355),
(595814361019533702,3153486338),
(326815379173765,98893788802466305616580376857019697645724121111004349192169237391121444486579039174214720246230596433637503054978487524531875726193224718115364065717059563039590299622955),
(71001326084,2182280557032038556899719633339900825250864384140),
(3288112351912923786712233446346280589,20288307854935343131062697779508528301697892818209291179169992720),
(85672690759573642887,26504642426234648029283618346794202654926591763434527910083785509176644363182736374560874541008934854445620295199029736665034640722945800118398829661459364206120776976493441976798126),
(960431617196220512949296749753116066002063,19012921965146145053418862456919161992245237710749453),
(47856595967090733167749513,112103921687092868),
(2761828995,1087505794),
(69060415236,2200857769066263641255489043741408923768596745868),
(441401230452242601619004692690101536570357904,19059812730703816649164844460797363930496182871447181),
(40628530315830790049918699530,14046055282307)
] : Array (Nat × Nat))[i%16]!
private def pack108 (i : Nat) : Nat × Nat := (#[
(167329474139792262,1774156434820823047570933551957788903782781080051912747551526716316145522216796182619789734145486750174654963391531563233097181224619818296770763496935200221138375191405639296144038551487795669551968877974424675791731961163582394),
(167329474139798406,2679109811947100191753093108098229286638094871278638267972484853048686277648993462751933531870411156454088406226590048757397534366074489087403680500646),
(261245646393590278,9763793251712268030473284667344512966386219956111162091266976400),
(6239624764036960872362668116914157709,3736561508271238460190662561553030537),
(981860165901301275760145237323610060449142091491423039503209995928,798026636332510775528138182968858523905387327894615694696822147405103697427276628117),
(262072068965155334,33689917367087346210151406179419204931594),
(139593091,166744194),
(862111778227036324593296769009735082391695,15925757501555985689663110),
(326815379179269,716576077402335999413010757073666060380745921087974730711830094973674010294233930895979130046871205135245750980573582175283930448750301009440863046982828880885040595344578839764648257033005443471281075),
(638311287428,411489580257667490177822664523699351710079583571749467296136772131232095195517066320150080687000),
(5175923459,16137311868662998903654291519064947588247045355612941),
(22458645742836944967912585,17807499724465618763149697713710483793009135476524173),
(19227556996,2173840237418525031296408496713182472634198377612),
(22458581180130419236490889,702318256033376514675040073669486070667953228652405059441467125168245650),
(51163691990131548543296814090,14011557120259),
(37567619,22053904404611)
] : Array (Nat × Nat))[i%16]!
private def pack109 (i : Nat) : Nat × Nat := (#[
(753555263045778822,1071216254033621998699160586645384),
(790191085533763750206047485823711511694,13903037182009437977841676617688802493115064552802674067694519207665530672789690744614837918962379283994),
(85672689900181272711,26406998383865573665067044850917079557194261184055861181724486079763252219357696839860974462572158625749021986603931968152681114979307426451945821805719773812074310510547035073437230),
(1543341963933132324621186495749424269,2193345299567886127210344577760578597334111138030570240797071),
(256440771008089575047,4226994284962068353610370218178273929),
(167329472461291526,84957665513011065289723514904857080056538505605168716331882435477497491060174406311926779266746736946156100499733730561279069663718182935540320680995998555688),
(12193866075953654601972360102820492,1975736005985804041884644084585160779912196179089128641959951),
(262080780501516294,81865798096304256016697710044296),
(652699473299717,2501142914),
(1877790370216405171720662275516310301582,803997547757122842451894888998932620787599359770512657155981012738897216438419232789),
(5175905539,18357111479733338014324686251158916922319723171162893),
(1543341963933291669699413578964553869,4201900949548096273921967861441463775055251429377588231085236830326262717948835814771167142422338867607249234299798171725225504),
(326815375900933,40324398042432458652359053205114270803860221974249490985730025184678522342656269262453404835794486609452093606281418760039469200435003228851108),
(326815375884293,8578945944783987376804649234010012713684396953476876360862010424704674956755623087728109243670606239712179463537103658633566112),
(2010083958404,1451541571095313581317),
(2290372355,18790435387140450672649925521356745851582689027923597)
] : Array (Nat × Nat))[i%16]!
private def pack110 (i : Nat) : Nat × Nat := (#[
(167329472458473990,713563921143775535921024949919443444166318803457395082463938424479103258876237651044662526565569584994157905966839591716696272250505841482152527377662114111327145),
(177444510618816892257288,28631727609347),
(17393539670338277988029113226,402481217762437977861),
(33971666938608225943626889,26268311878147),
(5306974723,3526792706),
(25135405466034118299273073546,13039683281667),
(67119670505167735105082761,2389091714),
(49029972406886623639175817,29240159654147),
(33971526471385864622113161,3566208130),
(43864417228155085784200,1343176254259809056880063224237298511716910075326379686562288297077068237736568967560009200034962017258121408247819840022187937100842216251750916408014403351776169),
(85672689898740401927,140265706546667769999068732983245084950433652409684902461077296768125030235490993579796054925024113867630423745317304452288649472237546181099166489968459031336),
(1775137015684,2320913671911938841363737697852521501193094285964),
(326815375895429,10596775013420822277714488575010079973438850061548701879927289522570134802052195278133006763326045588378),
(883249541582295841762571734465885162111503,2379223196771123013439867367623066001598883967613047889147023),
(85672689901222364039,4548673627381443927923114967094868089828848973496715913494685275316181338415712227174539305690402998128706327033808404659738528),
(167329472463324934,1782088941974279646721803404072464518369653374635094774701061324535689034403521538760522424969700437749101142300)
] : Array (Nat × Nat))[i%16]!
private def pack111 (i : Nat) : Nat × Nat := (#[
(3936422275,213375196390982532),
(66350921367974619063432,11428536233246306349579398),
(237957725423750038663,107320610118178384003879633799),
(66346408741750809494664,121050357093871236),
(95930293300588691587336,14781062438440598216447622),
(326815375904901,167815960778601104423766952017382668314118431080197626205497143737815634760017116463958411651729330326055723013540069889053462992355082904385530149),
(2290352387,3520481794),
(3936553347,18287231988549941576234499304225792860105795090808717),
(442074802120608678661342479613803931674034704,700590396472184726630112224177941499134441812831050274603755090922087058),
(11498766411194999360807830154,13030952814467),
(326815375902469,970062999998349248074367537558149051943551416847502954840672492458625229915171667700103055524598812219348889295585000798994333815858744600003869841365403400824245051788866367430384073495012360890768947),
(638311281028,244359232908209643857130344397819390185027172035125206910241907063474016456191393552230116392986019607517083),
(1917334403,740513154),
(326815379964421,6097233335330783138271676676985560717889630988767182939150935351444803255736512777294496120934108207186833194735366893644692723918850502462720645954141462590908685866),
(196280536853642385180424,15997669343107),
(53324123579828089979346057,2497022207773815775708286203303591466095098493061353118598031)
] : Array (Nat × Nat))[i%16]!
private def pack112 (i : Nat) : Nat × Nat := (#[
(129208898075775205767,1934842882),
(326815379962501,334653131045387107764597866113468992639652950167010122813315155256024040689088982097519872858758618542349839317147908763794390926009649032025518501),
(198578415861965075335,3592818818),
(167329474542449414,35398471391236030571342005567024672031494302541525415570760635736593664986988576739202320228975221697720305922063494907616016151713),
(187467350361073327879,27531522887939),
(167329474542456582,182171581306500521251354729667114362633538698159028225987645597753985609986010915044765360076556878915311337214629438155947918859512568411902598693),
(326815379965701,5881608451723040459723731732901228239742285093452038999605505872522191007137231149835031632532231854058003499168292102624216508552183966593847398336315668766722001834),
(776824195857797,1786103810),
(13969318044225999636799527715083,703182238213990506715647884673431893676874654476700508525572300063749394),
(53288719346771215560081417,85837675563231263026812485913160999894572024014185620046592614970641),
(7152290838643711814041355008955148,36028109568682755277018300678442481441674),
(3661972909433899719250319414604473229,3085236866533941134881223926064612542014933997571945240595461866146466095204435359049110),
(6423210694876107996434971766640396,456653242006554815252537404724059936709304331),
(6423210694876107996436205971381388,207046741284012407004749712607816138294774482810323796623172083274541771806186645268625182977560),
(726101918826705798,653202897198328348107435649753224),
(638311288964,97298834586723990710420721639065901954885637833923916088406584626590289108616009035624169769880)
] : Array (Nat × Nat))[i%16]!
private def pack113 (i : Nat) : Nat × Nat := (#[
(138330103189049384055432,4303520025975245579289862),
(27906144337091225413128074406593589297043859108155155,1744536356562998108683689940065850954492759334523728966273167),
(4976692355,1540683522),
(167329473062444678,15349260091833578208735254964576940789302159729957799147185511660686641890659017352373164045517625075800380575997469),
(37303171,3231101186),
(134046292700184858375,2960258085264041993112178427742729481183811773068),
(676897090430783750,3506879490),
(1030967381283205,282966016912552797023648458238158649010965515),
(9777763458949,123031830788020673352071502307441929),
(187467350980836590087,5937994447663018393489670),
(167329473060674694,81895499751488981691989267392385760686283985679868516021490840081613953430993781870738345982538183031802277514170790636237967026245789794868889541830670453672),
(115710684155679164539110607690285490313962376470418,39438291145975857178894017152705167597290372254157837),
(167329245931372806,26261234993283),
(43864417386484224360968,36217689253873626228793125545552091123834004568658806013637483378372919112193858427924418134051969692675685044435261613264517619341485569318142249894),
(863185516168965,17128599472643),
(3019098731541359933859483661305996,32986867125282505401080037860243401886730)
] : Array (Nat × Nat))[i%16]!
private def pack114 (i : Nat) : Nat × Nat := (#[
(863185516103429,17128595278339),
(1545778550549058040633854676320460685,1216999444456509688660690376282104887294366169369827533539855),
(1545942562100531232424374681217206413,3629164034),
(3019419066602600063328856799252364,2213709093587366590802142861287312919017486044172),
(85672690207977000711,1099071879048970276435191519553864813020246749644324962318970417089306598383108376290267752555408696710098286387478963587999),
(1636636737158138187510349405095904831751183,1971737166302799965829),
(167329473062455046,4294598888464366872767250376476602578074335490484655756114790057712989284251517449486851666374069911387567024164169781061520288),
(326815377075077,11225530288969371484820868251980026322658560178979372902569631248),
(3019419066602600063032056237983884,1995261552764943114245),
(17622445262152840287864119169931,134047442318324000154613892871),
(207916977533043743116257433527976022445543184,9011953256626994416330086938974645769),
(863427347891836381111112740772020751057935,16152470866356549221330566),
(326815377082117,158442733189479374526597032527531341112440956540810269069848327588218974686455653137730526690896837448459197767907657466481349554655354919500286885),
(638311283332,3392708351300307076838216609682604194054910530321067089319522656999100288303889993063958),
(12193893918083147611801177499841164,578987500075902520455151119201681928764049675),
(326815373394693,24173981126369169408754001916796814684672289636336361716117273495311766533475524810551757719)
] : Array (Nat × Nat))[i%16]!
private def pack115 (i : Nat) : Nat × Nat := (#[
(3196548828624041978789049387804988484494,1989608984981699742213),
(1636633000250616862097070131617958800536207,11902310989828383810214288150837779140875173791871328066850119622251253123347),
(4607643267,18404152140445908650771502860852523187573092692214413),
(1953497091,17760647479249170011680583543456845949020299937056909),
(167329471052783238,15249157612744809844889422761850192285977882512473675342628040920702914271462684278995731562661342312927531963407901),
(3896257411,823232130),
(95884537344651116682760,3652567810),
(638311275652,6158881513836993438036826598391492902268722564623574601173893022591558406107859681446806),
(1246701699,29163027452470879623126660452817415738978616157230469316793954506993323904587026282101999022854334995994),
(356559805074185350,328466567723116085764857905178837045081375922920740848526),
(326816578536069,390721925514549621333287395165819789825359748714253),
(1379959850756,37856516169190946590824943797292054854802660125140170114070382281730463861426128119785261414710017814444315),
(695924028416645,27954231175299),
(1874888108904660236669365860042595909902,1717455890309524048856661968749087332720750965740286058440089411443075783089111538826697383093702041),
(638313648260,1812040378222380600821208406995320078176292394220831206031578469789734180629185369114366507479782001896095928092),
(47929843612810330105584777,1489233618175311758420284890286628560136741468762153689748273576660908434)
] : Array (Nat × Nat))[i%16]!
private def pack116 (i : Nat) : Nat × Nat := (#[
(1321961952002053,3099858434),
(1911367618180,53823333940139549279060806407),
(326816586674565,16340743846341066939957615988188435321392023741807207575264994697281373687447336996367323634354593806416947791158813),
(638316446212,44580717701621712213742939011220050192721460927684817342453904466583823289048596),
(638313645828,9178996279035042127878797136512039386000940197032093042840824590115657303240597611835409318182490754642300509538713455193120288),
(1246706307,1656493555624361070397146868118268052370856974224796799890198592848865275329813003597570852882140953),
(753465272704637318,33604625946498468193624027994121690103434),
(5203499267,627124482),
(1364138759885701,3671512578),
(47933313575040902575893129,7267825218741839179413254),
(2660837891,1052898562),
(638315987588,135516424054674339121070528519),
(256838307009540486,175809171518874756),
(167329057321864326,10900972826012966370763789359054117401155613836598797),
(6509736856318160934424959978635276,7532608668962746532261638),
(502566035456133,2074322818)
] : Array (Nat × Nat))[i%16]!
private def pack117 (i : Nat) : Nat × Nat := (#[
(48501450732618156322194569,16566642765512749743239558),
(2694457731,1062336898),
(94729395962144836566792,2276591278516415421107767564401546554014735430028),
(12564520953535938582138681377035,176279512836512540846120224768885269776236137450657911865554262538893495278294680597),
(2688893315,912535170),
(167330848288875142,6485412799167683848445717074867057514165151122957727230625579377099968794387),
(24793375873531842133848497546,581951950112682039965392861149448),
(167330848288886150,9250433903184438739739158009867060731890776043293357690503682854558213141766328497489169877505180595622959528726301),
(1377486635524,2197999082593980908168682414589376600685161143180),
(2649399184900,10835384916483),
(1584641613572,1946392066),
(60079741187711651100528761869771668045642140850782227,1115633784065666956103719391080968),
(85983921114659884423,39494992194084484),
(861940064904922449621359866916657962818959,74888145310966582054976239519677536460554),
(326818063064197,1353816813299420028662574474165172047544505527313340268008214732520623511674710969386409753343003534420274339383715617990600780507375943942107427976358),
(53370076409293241513228425,7523172008984317828224262)
] : Array (Nat × Nat))[i%16]!
private def pack118 (i : Nat) : Nat × Nat := (#[
(31921418277274271489458769802,13005452488963),
(4775612163,18427366324342336381234189123378375510128072859034253),
(253108109294771974,1117435396959525933611991237351944),
(640420000123403526,34584303546381679689600181964528541737610),
(104263943353118995841032,16974820552208404813980277753577376744661899),
(43864777894630510697864,7101072850500867098389635321608),
(90844432235197244762699657,1150704273379889984773),
(94577042942562327733384,15315036934999078481421318),
(4775617539,1952840450),
(43864777895522517603080,2938139614353219819183073855855269172781081123100075013262887515539028002472923885587636599326691097),
(1360877133188,1328334545293026973701),
(85673394327192417159,3345224320521818188344290670298911836387059980924723744317095512604242361749944809229858262318292518473684900481003207148494176520220448675),
(2441425203972,3210996866),
(4768412419,30391919788419),
(326818063076741,23739830826860985697678547499193076181669240890647053),
(43864691570650464984456,8156072879821528012766641319526032469197951780915271174260598960897808237587)
] : Array (Nat × Nat))[i%16]!
private def pack119 (i : Nat) : Nat × Nat := (#[
(397735807264956038,238016137166956548),
(101798970154633944178184,193590308746068996),
(961386338880213571188617312647123259303055,113896909228038941847567176495022935721382320460540790766492637989664262453215709039842184032170836271266203),
(3725854851,348169474),
(167328837140416646,668073577798904311660894022455048),
(326818063065733,568508427454693849162661102908605689991646581764038881974054717682054819252134828132993395763773374690884754462898657873695),
(638316529412,5275382670702487957710505719149309740282431303236649251073463887157452283020185999925497397694762173820183533271306084203025824),
(33827262567874093941330062796503168577940967058713674260,84677112439323361227867641082054389013363676246314428081253606624017),
(326816644794629,4885474608222245392634907567419869674440558134796),
(704928758910469,279834014228391025979246681215152097573580811),
(167330846986682630,69443405038683996803764758623314979976356442605794866747558333679049703644566655301789171814263537732048448327135973150),
(326818060520837,1593858221367868944972578124172757251930127996586901762656818415886819424711088428679494266484383630632316505803944673572818365916100137536654631423782),
(2854548032772,1839445122),
(638316524420,16785314683857233378733574),
(53294597291096697174697097,7594096288780585072492294),
(11498888366669713451669272074,1411161342951855618406369418449055664978420288894426975387039911738712854675)
] : Array (Nat × Nat))[i%16]!
private def pack120 (i : Nat) : Nat × Nat := (#[
(5578033667,3430343201795),
(53287555381991684031389577,306114561211446288237313396763422691466),
(356559614561960582,4161940662010822444156162117863898889),
(31602007074525789328882270474,263776045076598619390171016072918444046284299),
(22517583407602066155045257,7211108388957828272892166),
(11498888391543270286162538122,31157198004062619339111674511460665095040656785549707570557984841220310769477123267103361602042791916314),
(85673111593114862215,250654696026516996),
(85673236408962461191,3131958248539468087903128229460206604042),
(22458766341150875933023625,33514395384074468064330334599047946729972458922110477),
(93638678280233084396168,21167420667651),
(235520791471005255687,195577789488177540),
(51441188188624201314876604042,14002916857987),
(1065152429572,23873220471171),
(93887983580053214885595401,1131110462192079663663868995124232),
(46500922293549448906830991242,942035608338685934597),
(3196599125983362481456899492818450200590,75907538176284253270815811241232032806282)
] : Array (Nat × Nat))[i%16]!
private def pack121 (i : Nat) : Nat × Nat := (#[
(696405164112005,4691342172619658212206726),
(219454471194694929073870892518923950638373647942162,75998575358490763503786841768261292625290),
(22458766341150875932376457,191475649419316070625344046465624219850451829775887358237119188102322977928556099272365456203267839179563757037142940898438235597742240329564208713670988320552),
(43864778010060304555400,208736032987644123551131022188191582576741919944324631536223099603780626694708049719231463747992),
(27332168452812880375736771466,36028109758830385062205603884523210392714),
(27332168452813251873291181706,1190614540217243598085),
(1916543875,724654594),
(959940138820799919894771432323274730439183,5647184923203032601019944069987692835297760180320743089362805455128804592403),
(1874883083634374843544475453756395957902,5647184923203032601019944069987211685771516726445269393846439045753412491155),
(11498888391543270272535248266,4892918594585699726139078547051303727361422160105226363775972228035133418305321799295300206501352099610),
(85673394550899032327,33406305538635211960245320508458786740808759086694963671222613206039225629659282970776105367),
(11498778376304630651289666186,880262113756470855173),
(85673394550899023239,126287057445514346052159291954977489140755232349250394009786359419660486686090234632447565313337897956855579),
(3014364598512739793970275859235340,114538745193951730165302738326792304664172640770417206507287628761446476529294371266341305457566434536640283),
(22458551516219982526612105,3759557122),
(85673394550899029767,3799963625082101004791744780568964334248226317966828286896516890612229909140558547519795126528823065)
] : Array (Nat × Nat))[i%16]!
private def pack122 (i : Nat) : Nat × Nat := (#[
(167330848732224646,20040050012625522138570892422615282748843372043627234330208182034220054560494518458827338135),
(705441671348741,1584700974563473047941),
(43864511425205047729544,70906396193681462279533461433123167617418),
(86621488271476553157787401,6527799575627726730734854),
(169182594280228719316744,97271793717521668),
(46522616888836195140117942154,939142187286046867461),
(3196099773231899084904925155651234646158,16973918809902573193160838),
(3426240515,18591482713438698283444275123317568403641995103650189),
(6242382374219553559603589385761077389,253055652625479812),
(185166045636798527495,505504927037767978753140643480072),
(1892473765892,2015711362),
(167330848732226182,141863486405015521664963305961527750261589285752707391844109154804649053961265326042920234950289660508375922486794449310),
(90786548556278264942117513,932795209453373977477),
(8867613918592786483235421585732759801148577101291076328555030,10317229676650339227864516197736751423905874862055223493609500688),
(94777763900144001827336,508678696380967095595884966162440),
(326818188311429,3722708738)
] : Array (Nat × Nat))[i%16]!
private def pack123 (i : Nat) : Nat × Nat := (#[
(428621883146936267910162269769087980947637677713,253478811696826244),
(167769758141189510,9709440938528859867041542),
(3322875139,270566146),
(1136569853609861,3783723906),
(85673394550902505735,17359832716908053738746341309210706194897646380520139417170237522281995430577611973075075289505508074712893123616285),
(167330848732231430,1331267857979223235022419407306171826801547114291241114626546555015332626),
(326818063930117,18482431636948886014075913247036279435808803560461552044031531472230356879713537718873282877116037964139950268033725738843926046138531007885732),
(167330848725081478,1881376558740381228148644341322733427863553958583830480272773971976387871279131888159531992181491643462409712028),
(326818063916165,456102817485135909870441129289748766297951545013440524089137569492559909066999488021),
(638316531076,129757087437543195334212135443405553624181275600905936327224523682193),
(12542878777705530062612121329035,4604087731470785240856645641253084041),
(12542878786142457801476515961995,134757386825506593716899945935699941994435338804661333936227213881246690757010466356286653199326225902263195),
(1246711939,22390411400910092815600197536266464639417784184839348281919183583843973397494327449838317353992423875523049142067984551843776021799790801507748),
(638309704324,1400956922033880722558076909828252360560091745761645672164155512754514121820660438340624199446198005813647691548),
(638309703044,6143668692751629413127022265385892083004608794699917274342269223013156651853689122020653998937851104084404423364158552234463520),
(219648191649229435914080956276292621593595054343954,8230893466679112171940728553449165577)
] : Array (Nat × Nat))[i%16]!
private def pack124 (i : Nat) : Nat × Nat := (#[
(1246698627,4608622293299095514444016330676244938792924670575134005360123135516318187600769492788021429495608079953617391848743153633657569609259572771),
(1246707971,99845269237464457794640005108470088991585979211739828318985495346729014919390411076671917646429595939181152588668901199514901516677989864010721799875757410781141125239083),
(2434946,3069311307283148827597357842155205666463097998170751622469047118871332710264635807319583183846235840817566716755595417922347924648594136611),
(173100419,2939576194),
(92217891342774395810440,4067598226543175582092678),
(1790072603908,3040041858),
(167949105493800344307080,14020491032835),
(184516594380901078879368,518843656749490299378975608369032),
(5077552131,1554179586),
(344301548985082401415,3806795394),
(94472496322695087325137801,9427764529210962490049755260098194185),
(639958797060,13545433965917564323697670),
(167135959450334086,678355857954474061931151436561953649590843264752308573723849327798798423425709277573008903676063328565271663644),
(326437420801413,826195495450762864375498919359214110333154946052077565965260984412115466827764666693354769587221238793911079964),
(637573087492,173403510182014468),
(131798996570580922759,92152387458232414091210872199)
] : Array (Nat × Nat))[i%16]!
private def pack125 (i : Nat) : Nat × Nat := (#[
(1127758694599685,2617566722),
(102857016464356203445128,1775039123512411510021),
(6090042783200665862536,59112028893987216337936872199),
(328048109052194407815,3487935490),
(20300137179529454174822653099093348030799360913,863518676120242129312061372978526471197318907431182727112578702028974891462818201109),
(5009723523,1725179010),
(4402327939,1166295810),
(592672866978279164719852326308748,9416604133838840938143244265417221129),
(637573079684,7603320322050589590995315655709090290126364783107676219216386370888149320242818490711674520048666964244283151396284453882370592),
(47215563497937569507253897,111329306890960516),
(189244693663684094016392,13977559185923),
(326437420670341,956871845335283269111792957881080862932618565801615109364481059995817488473289796052808235760461405756223610912830729606470755491123532036052038968951932610460682701180468928501209516899140675819738163),
(96832406515680306640665481,13942674111363),
(637573087236,64214582534052081539655522483014227662665971253359835814804754196715147834403609119918565343641077389913737779899841884013484513865576792861925230095225380147697784649064611241827387392398771559427681757369397),
(591381155401321350,194018268779182468),
(154728866948,1872028290)
] : Array (Nat × Nat))[i%16]!
private def pack126 (i : Nat) : Nat × Nat := (#[
(11474573145911389345260637962,903344543035254185349),
(326437421653381,125740065476882075812996752051456321599367759024604771341545017012467150033345225633748701085365666585169323978707637278),
(637573090180,5737557946880130218619824947526628227190464982290504170943589193286944682242084343294808399511259404379032259375376238429037289714142691145956278382520454917960176682),
(2623097603,1032973954),
(1246644995,3834949634),
(640664948868,18439211213754321424739300232523011007979732926403597),
(257411101904024454,33668460085286542173605300874654622429706),
(705693438852,16538112542446867247978118),
(23020754195264390,135280168701178116),
(167137127620616838,513906106915585496621137101465053945339704204191416192336196101204302379812587081253016294377402962116955923938497167566239),
(326439702384005,6457114890943848464475933558966028165737362675660879462109294423864842121619),
(6034751524893342187784,46175011211066125651642171218241986238475195779146721389050180881501096585386900),
(343515882802821,2582720770),
(2819520084740,2283782398039197955712559007189126773443143283340),
(96876042367555782678100873,80392460462072836),
(637577543684,880893102959182099344556865608590222547621115417346389623536542076356575567001944797505344347314666786154124027772505045093390617360913687469620485018863217070072237829592108)
] : Array (Nat × Nat))[i%16]!
private def pack127 (i : Nat) : Nat × Nat := (#[
(16182639766267035655,27412427660035),
(24188363977064375454095715210,13675995981571),
(2788518406916,2306620469725400951882282623552841047154313347340),
(92271285924039916730120,17336236330857634415603590),
(637577547140,8243998406180047340681384766996099285309295884853027009262831835844711871265033083229650460142001016276647110150535309810500892592070151215754729742603303),
(1245268611,1380110233303115141391656285820455584137323406663264696921728464078705682),
(2795448835,1090651906),
(326194550755205,147706452878882307007141919446458692099267288669556773902),
(54518560726258245756710659548018807040825825896850,1393936086365681168005),
(326438993998981,2358889026428838590091477815703299577749126678858104905496751761030707425565158269573952713510730364802669997995074053013607769581166547357340433990710501726445835237780598467763855199769558513110363499020640322364755577182557242),
(637576160132,4317473890148083963728935558677423410117218083426502494311559049650715975509965695012496134996706459818972244963934254739980600106755480661912743093741118523197971659474315469045348584501544056640203519076187607870903),
(637576164484,158302362865705334620400704680700861076873070566090596833593467878860857342541948393746098935350949761459377940188909970803048798273295654411069537416987735843508683101457262646053761881315605533069009124582186367707289749051576988144700),
(637108431236,17364236231713615944029190),
(91346586975063921346296713,13685498155395),
(371764226112618707719,4234739315267198213835737752201963529),
(1245265923,11964694275562020673197457842590208627085754502227235005006856010143186743887471995140592669646296483194179516704205162699025513120262457999595395850141778570412619493058347852163890396462566239234207382463237822755010910411972613179)
] : Array (Nat × Nat))[i%16]!
private def pack128 (i : Nat) : Nat × Nat := (#[
(1249971587,150190444754051249790199319974170033845109136778240398350),
(1550000141799251167748020402420919437,1167331812665071602177005459018760),
(41220908680282953266509460490,13899724369667),
(637571639684,11627974576928346959118660557982873699304591081519016759345257583316808730220615324082456465809204787030122604915528136783440425253786144332600207669910400852446116128428322262029358),
(1245257091,10103553905882688836589113216767293628494634623335411759684266879761085252079349459179880089322177606254466997239107629875508295710833889080236348694213182878295571147773850094613166),
(687474615137797,17277506572291),
(1245260163,480825335964391656591845559200650231587640105119001064325494204007741228823969166974330842059800),
(2432130,3938921152220296450549104565818705778160191809756245543428138449208344802532350464150913810937877529),
(1622660276362362403699597838379514396164367,38354997168303998540652375379073532512402080805432077),
(487261311731518470,795198333769636565297651479051144),
(5512327640582784925782921,31261974702595),
(951682249477125,31742142806915),
(5902588244535715887965118474379,15777941975349512980378422761967157510086604330829818159015823330764379638965760960754456638737053880616772620990109),
(326474053724549,210173844697811118166931096667267794447459278582548686473899674179019188497184033282114991153418856580977691),
(5902588244535715887965119522955,172731295783301140084484122018733170337771319751976634402892031669905),
(1251299459,257493369224631300)
] : Array (Nat × Nat))[i%16]!
private def pack129 (i : Nat) : Nat × Nat := (#[
(637644636164,991233886095921944857578667132993874323618284412702686408260241000885046663780845594339325627556377755189287612470763723774353137550380605481139679107800677956265),
(637642090628,6585816247387596722202527271050286814759080923539544179793525358613334134042034096780950),
(36385996434973478176769545,7499789031697087624176134),
(12724568787487387274814109834,875648037486318419461),
(191625526260402997839496,11443122462383984731175174),
(493615361443333,1173872313840323442785163312977416),
(34041547732611325221805961,143379429739529231872006766855),
(191625008581689695875976,126085624125833697314639969927),
(17429272438580412059535488138,23969914428624922882465035854338532739608846370548749),
(637644656004,60445181982381023378308201490792083139113598783183613938619682412484070901647985622214790671104055755559777251500398866224624300894755533139840132070441626013308945724715),
(1245399683,39344822911905260928090671185083844079725741987971212251472221613436463854479972167063479844153746083253331925801084470950377181210154376282162725712103819379570141238315),
(1245380611,144765127587712339457557388828202898488122007947415378667793308661393),
(2445954,31429020499128546078378569094492730428163891457889293),
(962115346052,1818278908895628123397),
(5897784149753819985003087754,13331892046211),
(4572926211,1486132098)
] : Array (Nat × Nat))[i%16]!
private def pack130 (i : Nat) : Nat × Nat := (#[
(178498240116213385082888,932828775421654026757),
(326469833262469,238995924025189892264298940937314580739649857804),
(637641765508,790993487087227886611193239316579376131885638181174697294491112207590084144559194253726485665628106590684870817437),
(66311956874547603190280,9681370184806706308268422),
(2432386,3973087143886905401596389277860242773890809231219712347440563328595532508374510272546525641795125529),
(511759118644997,129156806138417412),
(167760790322684806,275637609318297235102525169073468286605673739),
(1409750274941701,2368421056490944907410336663100143625),
(96896824881137497043975433,13977559135363),
(2193606795069728447691303818,13066110525315),
(44026038251234402845704,914192708152445940504233714780973102010633572472776415112799021530946621977951639876665488163505564395702260764),
(5511979779,18825460032965077384255864336761025918146439315574925),
(167761528052338054,90843745830151247739629111687),
(167946006561436806,133970584192392286534163298992949964681334508633949604186566317781621870066169135352390225539471400053968511102867682974),
(328019544065285,131147632399077063830399303943),
(5377836035,1475658114)
] : Array (Nat × Nat))[i%16]!
private def pack131 (i : Nat) : Nat × Nat := (#[
(11541148750276758072204152202,5513105940937640649362714660421201360429671902254540719507159087988807660819),
(22541331427058803253589513,1734013122393798715320868159924363421042305391882259679883798597524650430622507205650580289211873896695191020385075324936245006187721272457292361132890896248174921788307601688380645544760368),
(129591609400202503047,1960021606145212033285),
(326130225925509,1120039691746422303208762348344328),
(44026038260768186848008,380402837918803932909625270070497189360957572503454646601680214765564226021658752277),
(44026037943474225104648,61350434121194185888650713370603821762043530943293762723119918913915613871594760119148350329015686011199915996163291806),
(44026037943474225100296,25839663831585982535374986962716266064508719096476833648566599612042271813376180719814032305353851588235350844662563115145085815831602626273957239336781256027568565834183120443100590),
(5909074825630439217153632062859,279126142836744364551585529526227144888545675),
(85988355358348095879,7858361454717643233756572812381629464274489897313528777879259125970249204087412060037239261898433527408463675533382137318496745492266335311691461689356088989009023055808929610270656530606675530727161281204),
(4301598979,2072126338),
(672164015159980678,3925298946),
(178613627040935009992968,6462288946907827917764358),
(85988355358347970311,18435059341092019172072268208515329864344337393034042817760521882632127918482603716819392888847117941715216816329446647228166448696319823573412),
(906568041187205,27996632337923),
(328019544061061,13841704445304450923293499328797607410402027062750943470563859039995436195028475855017301510760264316570),
(167946006558885638,33532860075181196603392058442044717582266218039282672667266823086092213083019845083934499196451682775203357567826478468516621316513)
] : Array (Nat × Nat))[i%16]!
private def pack132 (i : Nat) : Nat × Nat := (#[
(3462940547,1241762434),
(640663171972,45798358247379607466791376452332250951857098285227019919603332738355013604545556),
(1251295235,4194030245496953467024111619416679971135385823429709961501749847614006401929170425118995669559527875348696707990090585688445984),
(6247110274897631458184,53771901994199149237431505024112664136202),
(2443906,8147737221884492976123146934395730508482040029213216714633283696064559024283805741731336857520228470026437996357716161217180967618452470052516),
(2427010,2001643768302533495518410513612913082026216483816620109009935),
(2416068611,17947411468142037979711518021751576233278081684711949),
(383325159491459694343,1743075586),
(2441218,2199471954455686053541161876503081983083951559913674558973258606026130043026089569701996893827438729280195828905660707619136925114097967015685951804838),
(2437506,46842010258615569188383055936374378524278541620619564759268864973466856034096916),
(2438018,233611310246784083247230000569942805146131820831595640050482691626407761849160554967578723886923156113789979),
(1248408195,295595581532560032138407489539688098084693708007504892515407262948547088354863872069600682896199955046113678364),
(2438274,5806041621215394490813283784347472577252327859486658440575175591733691959208961170095170388814319318503662313584828293043846249389787214405876694704186195618138887210),
(2434818,1590910149984575122037204809488730964939174481259112480617761614634362130),
(4737,3946255362),
(2564877789060,772988450331226720581286108542600)
] : Array (Nat × Nat))[i%16]!
private def pack133 (i : Nat) : Nat × Nat := (#[
(577350500114701446,251951255183920900),
(151280842978213766696584,880261624269423204869),
(4565437955,506524290),
(295499810576879387143,145729103530899014035111893511),
(119477869280436417220872,514712455927338724593097548906120),
(46826413840659728084976750346,14063292835459),
(1990146179,25859558107395),
(11715261398998788487,4003591427539374604631562456585549577),
(46779489798964337669500315914,31637763096195),
(29280701779693371663958493499466596393283667872303089793941,24252047267795204636356771101256198470682597106078218967596882576),
(242735903633269215751,3439660162),
(44690181269893,2175138930096242446853),
(1029779241349468928727439752850161092721628094071036062959775917369857178,10253057279783058213135683115774895828695480360581757330595929872),
(170404227,169890562),
(831849046536964987019450888010212504837299856,4218071969187492506498629645227604988752470168050117671262185157805678552418346556048998996817902058144569501127384365679195808),
(3629560864090215687716873,106468116099557764)
] : Array (Nat × Nat))[i%16]!
private def pack134 (i : Nat) : Nat × Nat := (#[
(44994113648773,6477996042403408763094567687),
(178628592423065147881480,13977556040835),
(5329016979947717874128387098940939661,81868741936732942297302313611518757952534626280578016234947905064063263478946364390791630798881255863069295327285601932388236211873),
(10408236288960386472907006052619020,25177824364476708879371483095998174022913903316849531861665458219673093188830550651167989527),
(20328586501875754829896496196491,203038707372416772),
(1624705169017509740272365015636152014020239,669707052105672730427645220011717793562547204227005613647706680999231917491804224256820164360025986017767899327623634526225236263131682),
(87879137412,32465328957699),
(3173087193941959861958002652875454430094,1198927525633595562959668895757960),
(3173252283237323711469462921164359402382,6932792631672541449160348558449712178885236570633422365236327808477272073981185066659005276259926628890),
(1197747164742405,266748219870226674457268784091499239407125515),
(20328586501875754829896496206603,3073464888241785751883141774609268580678350522275643451371456742455214739875314362964630),
(2564877800324,2336661486087282520508210763005779251847043954316),
(77547403342726725883089033,155850081745094851919237342469900630565898422004187608718),
(5178242,1168380484099),
(77547394137684320214797705,172073949901311876),
(10408235053440581018990704743622540,17627189544469251834125692917129350130152179855620455162227123984)
] : Array (Nat × Nat))[i%16]!
private def pack135 (i : Nat) : Nat × Nat := (#[
(151443774918768422374792,165256952039051012),
(46174434444745737377532103946,110155438152345822976719353607),
(10408235053440581018990703505317260,5418400786231691856570760394264635344363561632652),
(20328584088751134802716217783819,2258023291813771679964428802643900758609563701132),
(23640717417468768861694528736651,67128872758008886585823025164222398162058),
(20328582879935910084136382834571,11129002307668300803584232763508615244104795255873786077795599228384202527763),
(60009855351900250537151881,15321172345759124306486406),
(39704309385867681347835089674,3464981555666824953675773193207923334806291765691546869010288853184902730661735427388864443888907289),
(63585811994960859435775753,1300583288136432528389),
(2487763813326663214631049,106822631304794244),
(10163261017868901463557229589746495537669989231290952043661974,32901710872393295863951045183930513185290),
(16034798694327466035018028091915,59847920070130058163343809031),
(715248465577462501512742340225656401049882256,44523445664177316150376898922563458040931171002964493),
(20328586501875754829893744729227,691126379150690653449020250286288755738315848650199686091424016099800145110464167545627915000141876676428277691310882701885341645978345960417302423530920881904169),
(60009709957357089295185673,2989769474),
(1216305749050373,274068523831096225249412709938417001759424011)
] : Array (Nat × Nat))[i%16]!
private def pack136 (i : Nat) : Nat × Nat := (#[
(4632350851,519108738),
(99297538521591265367890697,7438017784742639006991750),
(5505948547,680609410),
(165621313191676987997576,4001854338),
(4641263107,147665358999782387325775237255),
(39704270511476083652136220170,1229813662677592189626909110512723565228293286811786003678660482854088942148244345574406180177092189099542828511285800819231),
(77547403342726725883078537,11153652324424851452556210492910745137519868637474426963086200590637947382035),
(5613758595,2975227778),
(12104984762876002425970236679134860,18614759740334993713757785426907305247801520611921293),
(2734384558212,3963052162),
(77549891477733806927456649,81316003259938145343640112802229252479498),
(1127240914371077,265220956903397892),
(528391137648917894,711508341809950900191829283780073577226),
(90160184147581258642690825,108161518785747460),
(5613753219,5123440301699),
(343922593486971667335,148050793626578536418641402375)
] : Array (Nat × Nat))[i%16]!
private def pack137 (i : Nat) : Nat × Nat := (#[
(18270093429357816521554082186,13057077118339),
(34139646296025314874081229066,14002929432323),
(843596657681411440804233228643774884207465616,4148896859357253517793379278302432649),
(96785102090164608261237897,921300749273997390469),
(33520623244290248562775898378,13994301750531),
(35664532240078663716256137,5029080659689476),
(91401770410837147379121033,2210243354897027634949),
(1029779241353796993789094279966128132776501013092626826878937139479784090,545944048164952341884655392796303329403840549991694334180738726419488434903331575573),
(1985231235,816087042),
(527246971573144060820082896672075213814238442814828673807920341538682049947,90710514119125397474490832693864253088580248706278267566087412318646294744941239283091496834532251111794256882453404190),
(207114755,18064451582016220753067515078574973630202258632435597),
(348670083657795713927,32952371338499),
(7672453234745539678552928623278788491941519036668985309933936407,408523837471764680261290477447228931498392243520855285436676668668007427426551686467522316623636642442993047908200175866273848346769058),
(14985260224112382184673688717341383773323279368494111933464726,264479982337619234156811959003726715990537867),
(61085129652811107688448009,266066506684885380),
(1013780134276,1215366947930757904505592368597768)
] : Array (Nat × Nat))[i%16]!
private def pack138 (i : Nat) : Nat × Nat := (#[
(753071374648622470,1214143859209353737041356668485256),
(715248551522004266711170924309146532922993552,123468753761916668633306106911656057616960437759965347147695190347462558281095847127898680979417662662355124968100270612364672676224165911778920436736034568744),
(32581868526692346874436593034,13650150676611),
(1625407171618923641752320196624374805186959,89181449340985073829004330375),
(20328586501875754829893073784203,1015349771394413661795514541454265069443969723850496761720192772125530303535153728216057809389070797533437809156322791954878389703792876067),
(39704270511476083652134909706,17974349169654115899487238),
(5329022197585751054405317247670952845,44944221759768141285608371808576759553851296868162317),
(703874759504056966,12665370384259),
(5329016979947728630732954953711551117,13344798790810420823932684349678091807236651263653610224857993674155877478931),
(77547403342726725883075977,44727451380202050504243965269770092994895328483702285),
(20328606405605820430785488893707,83306355553140019449701410348332759975432178028694820213689659135889),
(20328606405564509256322106674571,10478280521972946807686653630484061786279766040863367471450822544),
(77547479269431382868899593,271360623104184196),
(46829043582810278658887593098,13848078839043),
(295603455835791701511,4107338837757831243015227139792785289),
(2940844598441398251331150627127029748238,279649006951236394108062482516271422344977675)
] : Array (Nat × Nat))[i%16]!
private def pack139 (i : Nat) : Nat × Nat := (#[
(176257087238932279546504,19048172100959658820476256694062890002201037947343885),
(11218431848302649343866869998495756,271702381763681156),
(2728459365161080575556813795070140947982,1098749099805910354189970327713030500299597350992536723406043872098953936896530607367206196554272995151950725610987204336159),
(2621054595,770989442),
(4635099395,17912438184405336387291361397188644284602629348499213),
(95036734813521198681363849,7371855642082359296209158),
(3859879171,375435522),
(136057973772808462626696,4056386946),
(10408246479648897459246878795891340,61573246491534585101477854581549906427860519563615214563030762376043625913199618471257148567),
(10408246479659670028126587646649228,6693341723296440085257290312620412041),
(151459772153763136490376,21805677923820698917278513023409734874169237108797235937013092240),
(577386717929744134,5901433407784913430844940420854853513),
(1127708433462789,10734644689884501965549446),
(577773178690346374,1703592708390246650117),
(39704309385867681328940066570,11521425234819473299133402532707417166033581682067805234272723723757534460983451652524271412342586686088051483433501),
(4369745987421149678710357174156984461,16852700914836436099880886881179711783178)
] : Array (Nat × Nat))[i%16]!
private def pack140 (i : Nat) : Nat × Nat := (#[
(2203663600900,2238010112648535425250652148997590892349442447884),
(295819867487818625927,748533022764640447301765474257055035553714223572430138990208252090328874598502190997),
(671962309369087750,10129431303043),
(39675224226563039602453646986,408339553584689028617990),
(39704309385952835839957285514,352498402168724358960021223884621236426042178009655814661757782498275610592411919509),
(45322877731205,1213092813315),
(295770661111682519559,1230643212891357412251278529214472),
(330434754023099611143,120204050013866628),
(5077095043,1558648578),
(151459920447815640889096,81774055057905107703512705714674359197579030847907283258157464629179932645391518611043587304841382256653416615700519325273011992609),
(295820157124639923591,825367517118676582325688619710472),
(283393986133007721408396704965758872975126627089,724158652883986429195500322583560),
(996694373241989,272152032114530960333384067347687606757523467),
(3792770051,358657282),
(2735868020868,4080507138),
(19474686308680137878856196247595784063118874018625556906645,480757767428087567009296464435720)
] : Array (Nat × Nat))[i%16]!
private def pack141 (i : Nat) : Nat × Nat := (#[
(295820157124639930119,2880372026695372909815516691698220276283747595582003765509782816343630113614197993689614670761919345098279283685202047443795235397808487800626408282662),
(344296666336453015175,515664664167521201073929441256584),
(54902814827594265739222719547066088302211862317721742996,139431317779233071234403506823),
(577773744384062342,3113587565518226836081053649613901008223303918204435606604042802251313295619094940130599003578627619512642522633142671099621167445276842275377988983334),
(151434389909847259435528,16988523391080455244822534),
(3430377095465550075712423887593398862862,1253929429739583907589975502972114556943354378959188067172751),
(351906533376066694,33357107014147),
(2726467394697828384790450362089082266510,3271931071762646197335242247603899174434820807180),
(10401274401348933140913553735949708,10572232780386520887705141378229732376110985381581720283401731836448330294692299869995588365377849798838747485657629),
(577386716288780166,3137167268440708924956091865314794669936314112524),
(1128463239623301,4252214801280059264097830611148585398455943675534539749694205138456045107189530804056084518750144902555176549383510052785573792),
(2564102374660,9924508098563),
(1128463105341189,21004678549379),
(295819866853533758983,7375272113115681886755149399499184665679362004169176040560961828080422125938402250956950),
(577773177448308102,936557172044551242872944103760008),
(151459924951396579681160,689362555044816217414993277799055667362449145313774336712700531274627202725912503480097498756594640925459211919340995727172841154173725643974093339283915586099753)
] : Array (Nat × Nat))[i%16]!
private def pack142 (i : Nat) : Nat × Nat := (#[
(1083830209826181,284013341830015632007018326183496274101353867),
(1625960505033898973356589324247662737828751,271585970152241412),
(1625960505033898961288866602368557930784783,79879585457276624384941640567570781983961444329362356680071829740049),
(256209959790837826183,214468765630099012809990),
(42392699152436811160158473,107453793989642372),
(84188150576690018935908617,34200808160183018110287687688340104230026),
(43104333095463562393505309706,26322576844163),
(95984525945505885331168277719407141281413173621620883,4367910975888263427345002278402359412367798262284),
(39704310566458904985184850826,2205252113286449104307302114668510558278664777408630325457660121965998550023580411387898887607166598342448785694587789284265948123409898019),
(1083830209022085,271798988940770214777801775033592508801250699),
(2357985539,17924027437761076238329207327145123532771053077324301),
(60009756200652518946065801,576604356640857271041647812470536),
(295819866853535004167,704758368223833130087804109334177725812328475215049550498309796184611050408747014633031853225237552791994806997764736712655553589748502805581913550667933987348649),
(84137551018295144626605449,10180041964930184812580740288825472137),
(117116572321513771109768,490591539041280904222422518082952),
(715249806484168465687991759971052371813476368,44203958760842223185379431013818838313526634215444962426363591931161499470879252)
] : Array (Nat × Nat))[i%16]!
private def pack143 (i : Nat) : Nat × Nat := (#[
(20328607010026959350830772933515,10349534922126209897119565382674048999334248265508556634756370507079693061270578105443427440759829352596864979920634232079604256),
(577773177448310534,47295663038895942216130728590464535200810044486492107598324446245828424856275557037436655869231119784800652014207437252104278972842244219595509875994896232323393787484715),
(23640717417369617128513227279755,4100418818),
(1128463237203717,5647258050927134452862062367678043336154039270658185815027263510178966707197087097413285894174862649021673246262000391075538730224531185297285155851879452768158046762),
(1909687274884,3421836802),
(46174434444745252702654438794,276581799955804676),
(925981167402757,283145494307810581427384352868736470589091339),
(42452041767617804170786576010,13151380762883),
(5438707843,672219010),
(5573450627,699761154),
(5371599235,659634306),
(2822878139908,2256591512963416099969237503948276294203158514060),
(180117104338234245127,3938399000596987093681569547178957321),
(617759184485753862,1246421166953675467845463824358536),
(77547403176611065272598793,33945007326619554079237647180386742890646139928442064132110984754082688672717928961714316631822783556853676913521691107433775585825),
(4798489731,22465888068227)
] : Array (Nat × Nat))[i%16]!
private def pack144 (i : Nat) : Nat × Nat := (#[
(100934275,2522883842),
(140792349926021,4133779074),
(39704308157704267970769273098,13761981356803),
(447116115514704262,1524259288935780580485),
(5329016345785709450638617854263567245,5537490249859715859135269677360505677877687034079195225774657803781453339155),
(151459771829319162865672,282681159535090640335464888525113732950933988205529319427384561913633060787894646823680317713043159416021147),
(474137574160400518,1968820872858286934661),
(295819866854138989959,152873412409430640832788910985981973561025736863601111522991849845274826995198127780311639490362367181295285627127382012166187743980127117777525285),
(47216775186328697086476297,3995537089323154306984239730206923273),
(5580138499,3727088514),
(577773177449490182,156488222094462160764645922552097646799403212701776743704759510925714502209142891517420230945085388295266877536663628266308063224197561232569883173),
(176178436101947669479560,222110809890044804),
(5329016030778923920044174205281848717,10072636086733320297089939545043554983886788351608147879942117904),
(23641310435709569383759112445323,32636260400003),
(1128463237206021,18685157169279796891699569234793977331334178916471304071894403294033443668491117862626152977962347785084834414615616799692945501986658367003172),
(3795517571,3972337794)
] : Array (Nat × Nat))[i%16]!
private def pack145 (i : Nat) : Nat × Nat := (#[
(2337470697732,2246579869613335798529646789247818998205313511564),
(176286991202839736963464,17808894392710083414288518),
(10408235066807174676937551463390604,7689977139592671364901504249894722517113985531082802581280855082209935411191479305261590),
(4567990531,17900609153439021604695612699870316407606580022103437),
(4568011011,18813768017776055582779777129487437078357083899055501),
(74290050165930934623911915619427586278717828395516435,604405056002445521797),
(295819866853335316231,215399200672335429700341806633759267680540623519737892231482784619572498856468220400317093315695912659681174841242911681167361196993247274399443490195259123891862313603745305623963064879),
(5208219011,4121178626),
(577773177447920518,14455195663628466914141799055460711250491296622174422968705162615429717079522038078068877174333188366829060765723158556176043487255412350091304904445081453375569611436419324149736836178695903793),
(3422559235,23615676694915),
(577350501158428038,265024062126275204),
(1128463237202949,118416962876444400960649617857734643740778464462940500176152450755593665257164943809820078810624131743421260869106679829992383356900335522505406385475510134071262779161980519325427233146472871975474),
(2564102369924,16133416462925646476586118),
(3364376835,18989490814342563660418074870525010591660922771831693),
(451556713096677126,32986838564073993604099813341798556195850),
(256742065923491718,3783680130)
] : Array (Nat × Nat))[i%16]!
private def pack146 (i : Nat) : Nat × Nat := (#[
(577773178617275270,5774056340388481767720536480083131697638425970557364077821570184845955708039373151979270084640477748106871240541321021679989817396684112163),
(1722554915844,17572928804773013181713798),
(522417662743944710,1556724564611),
(1995750514180,34155381491587),
(1128463239486853,15754611097670178150042904759002873747411298098865333304826648399420975385360319505015923800470372960143043908230768441475542041685195103141673918298308903),
(3359384451,3754296834),
(2204029764612,738654484075007575706302470578040282198040430783413884645284440643715346),
(77547402986677801672982793,2257614321239623990709653610992930858291370411222275754077369850408114111915888849565778732500158320651754146623337137742545236501654114083),
(151459771458355081392520,5559506552391834573118318430724001545),
(880090951714565,270577141395507826219050423009411962539115147),
(131761816067773695879,3930659677311947642538864940669949321),
(3289254019,269516674),
(60574604352889390005029129,108863127579744772),
(128313372157927543240840,280480002),
(295819866129599768327,1751699859682301805152750379228530610402881574856469006433317229512571836325580687875192560065196832206266022968222707737304735268713228128651455285049067845409321),
(295819866129599771015,17826635506249676241272285089611437652956400197242072475039499139167419857090872063677365300606658668992064725146141)
] : Array (Nat × Nat))[i%16]!
private def pack147 (i : Nat) : Nat × Nat := (#[
(577773176034374534,104388125902551909446866014295466264841725591614536002802602910175506079189022741296429952717711572964103059113649952796289428912049817705701341386920931543265177511226989100),
(295820166780298611975,3927190274),
(151459771458354247905672,7460185465354408814345488382910195416438795343821451655093146076360514100805739590496406977400613546874079474323229),
(1128255936407557,1353680513691819413253),
(295819866871320166663,94752655890396603491906066567),
(672446370138379014,3064290050),
(295819866129598140423,19216910567219563571306941110466446978688349273307826353529510477583356951627567917883700033941169906352067578414621),
(2392603447428,607776059688274525957),
(577773176034374022,4101346821806552578242013963253337752331157529311262482633695754692174762635837160454062031845561710434004540733740383445932576),
(1128463234442117,86545271269742170515545768906283728791196971093332821729891600759507578042500721683718598518546013252302026979706369205180995978785),
(2349207171,95431298),
(520343913897861,264479982337653143792443741808110274284425355),
(12100725305546938375096254156647308,148300139669007932724367213063),
(60608269981423919771094665,32923064199742085015940069749156255908618),
(118189563860576785336072,58531508325762547235397265031),
(3173043055591857190647742639756944102286,274700149661939937802114328828541613853436317660196880516979879610053119744857014826230524802314753488864610120040539393677778085963426)
] : Array (Nat × Nat))[i%16]!
private def pack148 (i : Nat) : Nat × Nat := (#[
(3173252364220216021871458476560261782542,354993360346037013034104523576443356670821991794092552718),
(77547402986740354415536137,42795380502355009085224921307485562880968659344793741),
(84138539986687134033595785,195168875201942744388547664043487239325558586964698933464501740598929),
(1016337465476,19570951000195),
(151459771458477254717832,348376791502584631260351554700266948240232807325606846606),
(577342220321687302,9191640228357191956171392404560686832138),
(295819866129838388103,12580006064329762930137712960980572298158054873106122735430009699240373764412423725680895513213716344477902849941661),
(151459771459731385097224,2189504318283925216134401486321679464588174040764710523253276722385594001448742556730639259204571033),
(1015531372676,30144799675139),
(3529918211,1236502786),
(330182552478564438919,284889058758268287270320383041475038001970827),
(161902921183813039031176,277354747669097220),
(118375522961082316621576,491545525738841389284488319744776),
(23267672605803503075703204106,13787773139203),
(173232003,8954721021443),
(43099608339010896356142172426,14037412925059)
] : Array (Nat × Nat))[i%16]!
private def pack149 (i : Nat) : Nat × Nat := (#[
(81191973843931802743263113,3153582722),
(203580176090280585859477205317654331252132364501522,18994214321235759611458310),
(924605298721413,6277730008254485857016397809491088137),
(95984511489483734656332161437049310000410012934275347,155636746898335950677982291975),
(18305027698240420272830359818,13607258667651),
(107111652869,265361122292970103628523323445941159668729099),
(1206821021294213,3346334978),
(450975689453880838,34594288337539),
(84198923520662142072868617,34550274274051),
(1728208192084620712331993152020141460503855605563010424692395549393561,25879013367261930817372048924219982556542361935570720234025768848),
(231202193283363899143,4213212546),
(151459771459731385102728,19390493761081493532539725182944810092753156641739946105937995725044046096634450255490529700367885751429692697067805),
(8134403,3743653890),
(31014197717361201509954829450,13908326902531),
(2021141891,844207234),
(103083162628,4232568194)
] : Array (Nat × Nat))[i%16]!
private def pack150 (i : Nat) : Nat × Nat := (#[
(33495284226889100846090108042,13985782065923),
(577773176034840582,64415588643417695884889190444811042737828658845957268732250027396966940172997180741667552307247133139338894864957993834467368141103103658671791487398987769158161751697643049750901525344329436684271429649670325),
(30948508206469245086722492810,12996598335619),
(3893499523,383064066),
(3902933251,18286890914157876831112442078367810421370535130994445),
(118220571249616983359752,19078361749660206246356614),
(307051579406951850631,3969537270166405236690606041613948937),
(20328605773919992900410532112395,4135708418),
(46196170268322476465278196618,2378688130),
(2728456682951062810965751406878585465742,35399376187597432937638638112986017732593857247500549924163137348359173459969991454070203761336963783194),
(5441454851,18053375993571415289750700316166199017837843408234381),
(577773176034836742,13126330128020734883225273882138186760493263409481433214083611585644190321946743989911776849365273130451229758534139684585256856808630812509523665268165558363044141610),
(1624769929130480496007337513433590516103823,284183667828726276),
(5329016958906990894057377023442223885,18422955873247867531727322546488758818176774220695872177343409337391738648029669859799888461174438603438916336366165658938518369508018151184932),
(1128463234443013,143702392582899806023663825119463137459413253130330407900112449453196284102295966998268641866518364242691614449163786782),
(2564102364548,60469982681091972)
] : Array (Nat × Nat))[i%16]!
private def pack151 (i : Nat) : Nat × Nat := (#[
(2202382508932,12770699640963317429044742),
(176042242614844471064584,258492428461672580),
(343832505105841075975,3851702530),
(117040606712029372299144,1319610754),
(23653045987286424405621175823243,285520840155686020),
(4164963369906615518138541320509989517,1214651084217021351116015717741087074050152700150213732609167),
(450976660817643270,6578689934580868),
(30717717839243794285658846986,13297568066691),
(78701866930632478013483401,1963454082),
(12110372536598202662339822453737228,963279225699241480095836285928751570574192486400767827795964980243353915951611874453),
(671547861534387078,34844427390083),
(124193021136569933703944,1163767902531248533544126442259848),
(77495535768975615757401865,7888675261410635025766662),
(39704270373116390067533587466,704930748033704066280879651076231868502753547),
(699053813297729158,34669716817347383582431181381033496217866),
(295819867865001181447,1305203671758234326859641135371455708951415628606223117726565432754637650769532817863474578768343213569089844882498772957402078200768052988163565021862)
] : Array (Nat × Nat))[i%16]!
private def pack152 (i : Nat) : Nat × Nat := (#[
(36875935460695846333459147914,13684598500611),
(3330475907,18099714454695096344169365892729513370059147401511693),
(536439872711899142,1289863735650880224180335997848712),
(34873219,48632834),
(2728037486109368909291289558174778591758,1241467800776281585498518113758856),
(2728040825279023314622159980052967538190,14839491259479789299998783599596564003191703658054413),
(95934826643581632565911578829527049293237529011896851,81521013230561665436272777067974082387722),
(187372708288245376105296052401419964107659020405394,1768868437304119924613),
(295819867865001182983,1285152869271497654033140980255041062219786522697811543397310994616241479754566019910249224199262451859379596810873022845984221522007048281490166639270),
(577773179423830406,14118809938930201957747384244278492794247344797671531656979012025629409798803),
(60514926974827748896480265,111329126442651652),
(3526951043,120639370033510148),
(511517048965125,2270124623486858516997),
(1128463241062149,2075757761664959221723916177622645659630237350523678477500687),
(4299564931,901072898),
(1624705213486441834165921082851008058446351,34499767749502195929419701918210515481738)
] : Array (Nat × Nat))[i%16]!
private def pack153 (i : Nat) : Nat × Nat := (#[
(3173252370090706707355314614943375114126,282622097403921986223008353991824241740428427),
(295819866818777796999,226709536785627625033671430876372246858904673564461036065145014682138478012073632544989276429069112647861787),
(1808355493764,2210888046257148887155773397473063825534971231244),
(577773177380419334,532887853796394766499414740179127029752840578945184930638715664732899109295910968430656805650712),
(36865129300785779983674449930,13727548152067),
(46196244699998695688319488266,14028907923587),
(295819866080040397703,2055748049497412180214930213511067090815306366795417969956313204291654317053217081457786914591804518623049174172039394482903049312072016478552162017446),
(1128463237071109,969242850015085447762979899671253455177836969654141539071141833963786215857457709333),
(2204029759876,377881449609338420659471935136888189111509842745346203790),
(4304745603,17004607583559345944362321327084713243690975210989328203366514960),
(671988217787071110,10872215318118805197313542),
(90134877787227406154800649,5987822243125289009025299875234003593),
(3493330947,1330648408448981951109),
(23628317402721585232044433625099,165120268531257476),
(714474446147954771135178136426000573153158032,1015949340519813090693),
(295594711815957448583,85033089197232020959211772423)
] : Array (Nat × Nat))[i%16]!
private def pack154 (i : Nat) : Nat × Nat := (#[
(151459744603675350611720,275345632028607130054799030460551323972624677205098453894041612925104318090347653419011278541732741182760204845251029847013057083297908943821953573),
(1979791235,4204016130),
(170921229818627900679,3018087298),
(151459744603675354482440,274930751199039102594902639268998914810207706780949099536567911708028552526443542023535934802521985090770748596738705471505356567940318835312218316233956014172194445492443692),
(493615363533701,5322466229142693234776689130511614345),
(3329377155,1193492482),
(295819813679053426695,478746351397244295889323806580009476337061731002854385276013870685828358268647245272375732165144),
(577773073591901190,92211462520829205673642977161553249688942370738412710579777417206289),
(1127241920098949,3949166210),
(914795692180741,19562299087747),
(3947267,2388013698),
(469784128134198022,2114540808641367456005),
(39704263245566234264432559882,5224424934871401257305564403797425421759334045452),
(271245896540495623,3948753176815616399500108539343624969),
(271245896547246087,3892936595305013202608134),
(529777141686022,35347619880963)
] : Array (Nat × Nat))[i%16]!
private def pack155 (i : Nat) : Nat × Nat := (#[
(9095868462063667818475179242503564,505507674623928013821991739460232),
(77547389151496550626631177,393979775230287743950948822930497240743481732709031788180604079060306607577995059212452442782029999116404929775534180677879761069213963058874334281608310160749009398023865132),
(3173208631850060705137296576479401496078,311929675262424767563958949713928),
(77494262614149514423370249,1217793372939515327983115827903172676691529717094873008965391),
(1396970113093325573011398851865282753286415,159400205496604693761571159943),
(1396970113093325573011399040305136828492687,85468253428260017671674278668984906718501368869236333484017446289297),
(77547389237082709207688073,1733506815561773483820410740140879553932488142178987587763954913413515688729301895856315451422801817),
(46160484480204842268710086666,13675965572867),
(1624682819507231081030295847194810554394767,35393955657347),
(90157196248376980912159369,2377986037702469094789),
(240065258798893637767,128323608595809449077062868743),
(218061236753852520518174858996525102442433956761874,159663618265466280146527011079),
(151459744603677166421256,11150017786427044626288334697295035092045423166109559641204872673759289062941703063130791685587817457311337993995933),
(20314655978723610503652963525515,359200406981969022835469332731626040632550328072118208270),
(23634168053562805394655850660491,19490688151987459625260166),
(831782434515614371040178417971275446255767824,3089504925084371652657876493852907389221829951577526803847695)
] : Array (Nat × Nat))[i%16]!
private def pack156 (i : Nat) : Nat × Nat := (#[
(1079675870348659017972912315123982373430031,12921014325891),
(151459744603677166418824,119685723545207051504589713922989998583509726590418553344713375140603834497765652),
(39677062458444551765014291338,290718376884914820),
(176088273922612096154248,4327802114),
(81760942043384909079688,484248448693550999024577614457224),
(122913511618791011656712,28390473223171),
(218061164276432992981026365687477165195457026141074,117050386496612795804977011406883209093680845529304555873918315888299218015896340),
(831837327104312869953256094694050396656259600,35904330913271366097572016648854842849930),
(1128172154999429,3736407488723241135503995191553111561),
(1134568459047157931050589037898933203259919,12921014326915),
(295819813679056965639,396868998335032653580220081808091205596537086404650615566),
(240402649489705344519,1260446839100726438964836791942664),
(671725208382614406,767601515577497746500072464721032),
(275740286956995335,67981897578399944209249533880797833),
(2856656711172,16116565113987),
(151459744603677164970888,365684694613095732581081868907653789353948792233845271961271545849417233177526592618993323568985565725081050089356585989076919435552128966266469600974218194952587825437481004)
] : Array (Nat × Nat))[i%16]!
private def pack157 (i : Nat) : Nat × Nat := (#[
(295819813679056962823,2212291760623820281466550303546990097470048400654594076453382543803713381394503119322401779677134745),
(77488311147757521800200713,1258787840579393549744251668530952),
(10400321792486669998365933876224908,279300813126720165857130642417511666769146635),
(577773073591908102,368180748954046946841663372335289549605802889017011039374767341118268889798726994897237807102505755456797011507100673202971976251806685894934005413),
(871828739408261,31245413356291),
(1128463034359173,5989484732870326473228366088501938485321837491725087961587050136293924269861763270618417462933835763761659055720545177963069344),
(77547340724280344617829641,47988424060939955528309383522935717036651131045171725),
(3322889091,18123064260396833553514710351463211726546717049818125),
(577773073598527238,32128123786414689661351512050101146779631208798356205933277619791050129660788800433730672650587781726106),
(39704278637073193336782009994,4064613378),
(295819813682447790727,732223180069046995497581992648958395902935237412908158548166863393848873234535704248064976581009427219567246926735671303583),
(577773073598530822,5857961927928336998242294605037470852524742803340),
(1128463034372101,2391043797586411680251366573321242360084303060496992550207297376016238078221216006539756978684357513684450803612),
(2204029363972,1399730346751730859720494754769230793139416181419050033085486778853584742099172426186306995605217650091187630213523643131011337583283142286680056617510),
(2562461618564,2302325995179691608594463640300528231453670325132),
(295819813356028445959,275414393810505590486662758763941683895806845934728905733690593499688579882274704258019381672083169942961637506671667004328380380699170)
] : Array (Nat × Nat))[i%16]!
private def pack158 (i : Nat) : Nat × Nat := (#[
(577773072960996742,268804647029075049625119165367985179484256363525373617777944107000133984302789283546773592011529142136166939),
(1128463033126917,566606515353600871603900957224551233929129712740350671493070081019524196221194820117),
(5004808323,3948160130),
(4304744835,171679927824644000745265325957234881566941595571684764285186781648726579329141272434305036365083094845751195),
(118428557536277511881736,62792155605551760969782475399),
(39704238571123570415820678026,25560298998297023002441435160883726522352014231592291511814669535237157349131808784529227671),
(1409405068516869,1329472491544430996101),
(28709877525125,266573784488525022217685465424206152870638347),
(4534381059,937541890),
(109519491,101750759793621447429),
(295589778254706057735,141089695275101938042094868231),
(295819461837984243335,15839540032916756944405260468152579925553776840794451149856759905913735412422240240977747444761724533205750377830941),
(914822403,497086210),
(295819463244722881799,1348724458193950477493914291636448891074486914136038917752018315020877273812731000517774327390682795408374238613619360670879),
(295820350793169584391,779352868218193616145702945507976),
(159468603574108638855,4169699318980252994472280951207788937)
] : Array (Nat × Nat))[i%16]!
private def pack159 (i : Nat) : Nat × Nat := (#[
(81647925028446179429768,484246322627315014029254462649736),
(1444587221944581,272669623425641882455427198588159056978165131),
(127645862061608387152264,874492793591034239493),
(4327958822505133108284782755742695949,1676772685635315212135472689251845435849880724769407285177961383961557853883805166486509176335638779015389596912051408469510557165629022089921963075649630009514537),
(4471541635,1817361410),
(3960605571,395361154),
(4328762385737810571033427506979096333,273536307434850606356735034528969670408263340227905735494240931621948581270215182387527144691378152635062811),
(295819463244722873223,172339684655085208840838611306694952757477710053149985973705730529916866711663319152303902548189780928529706818038575564649645422946722),
(5376318979,293605657921505540),
(300120522469446844807,86512898),
(1624596335965228991953151655672116706017935,36004655757955),
(2130010486194398159781527437448428716046,2330908216316326795781),
(425900721962283896281934322234107040468665838737,89185636282815842953064957211960112727178),
(425900723004473378360298503458233299338084635153,88904750188530771698495179692760314306592067799359318345368171141649),
(5376313603,18275181728096734329599940431319847243530303836571917),
(151459565181298114971400,19447093651796511412041107673821609484761767363189894746268271283244478759706096100922015710451095526257043134962205)
] : Array (Nat × Nat))[i%16]!
private def pack160 (i : Nat) : Nat × Nat := (#[
(40328140008520507256369660682,14045992368387),
(230900089783880515847,4239613058),
(4158483606476740168444109271117812621,16024050260353536755595503146293506369397723418017421),
(295819463244722880775,4777419192193718775200033047292328444180096268681464941737120666762485771265541206923798),
(1152374187696773,140819812042305572895740633351),
(3960623619,268563059870018948),
(2021020163,11248069819779),
(23642270213958633543912881145611,48854463436675406255919927228009360158292107312236685),
(4405792131,41967761208090884),
(1015526588548,19217645899907),
(79342575619416350522417801,112949351528279684),
(20306632328780503204749182894347,13831246562661770783497208521492900685848258927018777270510517092033684265491),
(872620675,86487810),
(1127588273144581,10475988199862338800443232962688274313),
(721607133245291782,34690922170079011888268883070474337337610),
(32221064399188100919644464394,13650389722755)
] : Array (Nat × Nat))[i%16]!
private def pack161 (i : Nat) : Nat × Nat := (#[
(176157872552218071748104,19069642287123171673005830),
(77547297372824632515054985,2104377479225034993458241516784229574645155255776085470384274798324426405048425037480739167181814826047963657243793729509658470011459841005277855364262),
(151459565181298110380936,217509853313634941444693234404380247509705867),
(295819463244722871815,14452097128013807888681022699186659527883006622403342047051789456),
(950994279923845,19690849524227),
(4400152963,36099039181059),
(4400172675,2410254764705608817925),
(46176309244730577835095377674,2221399056455724173445),
(577772389149849350,1602804998600321569397316606341307789937046052354619675595453615740080825618350794267509343067309729795193542933281007415645612501532859870254166839281821284836521),
(62980650630959663777399305,13900231880195),
(20328558625769577715190219604235,5689770195417223481303483927098071669016766319809369818878057998302197448449668368586366234122320556293387869025367582455741431479805631011),
(32251903995118980434497980682,3214548055354139683480569180445686281),
(47755185198304660667839893386,14046014400771),
(295819463244719605511,14517393253088971232116468721107947586501647406873003188566042008380760971653611255343554878399214511341757507952838685458616734601021835102891942326175030531882444583404205481266907249542440113),
(366262772453810822,10355870744936321972587468901772039044261613165492981262310391312),
(577148050355781894,1240412825137247505993663427074568)
] : Array (Nat × Nat))[i%16]!
private def pack162 (i : Nat) : Nat × Nat := (#[
(577772389149842950,34291990440275606472677972518364219082775505931421440585243011809469399478117886484254007259784767101672738907090420334026689101601),
(2726334345871189442360671756532689871758,211228390219614808037683236957556494730040892210365067820155183477009),
(365922423449268710519128497206014617182851183505,194618943783325898180718387217034660804492470857006498301315725403153),
(520877025592325,9883583340950310593704509742724130825),
(189095894864442345399176,4360416758945834823006470),
(577772389149853446,6133810362238795544568698477159563921519955408445288637681276773151568145633387951970689211253594483495927307692546323858460174190052334115),
(1128461697558277,8113017489417921901397377991714041576089315707306145512936123728843664381013906635105430),
(295820350293076230407,7295701323216837655512584232266900617),
(10408253268904055376056711067551500,24620019920082491883270185036020601129566149868417328098777050943385193813597269522510207511),
(20328619665828233156050886145803,73043384974904059315600249553983447772509094899363627346519501841553),
(5329025673678876352541511196871116557,99990796812029952815329153866248),
(2204026753028,2744728000056073737266408198306676681214038839893511678418743671209646373543845788623645265719947245194127863663842515841925786174558800948560094464966855710444110767305824623149),
(1462182767500805,10291490434569921816473995679687430405334296517629057081911020688),
(136540318222691336711,556819142987947888519248007),
(546992235790361756136232319832134682768703760,36654267772736788295615425799),
(218043815202501074565408626918297813360195269502994,82593296290456233635311605365281404456714)
] : Array (Nat × Nat))[i%16]!
private def pack163 (i : Nat) : Nat × Nat := (#[
(1128461695599877,83183828052272247548512318641829045811780766423141917482441226572087246167980258815272619045700838413805565014371187325712704557414292871672340793556412661672),
(86008734340,19099428510218924172148870),
(1128463406873221,1410679783777767007365),
(468329631876,2243729383923822970435931086551120509780324003084),
(914690051,484501506),
(3172962739499807006682030772788796281358,13990540039179545838497841485153394617062485851702783417691980451414222782640906402068876865801014398362),
(12104825971737594994835618771770892,1007740241747054068924444777933864263612662654407376634719772657847480794271157020821),
(151459564918892021482120,2493864425570836604610643652620306454765376059353978707103577217845889577618718442744322133217429470185303581852),
(39704336668701122098837529482,3122099205079486087185359900308454288936777759087607985977704679143184604005815337624726),
(151459564918892021491720,3179914201216106921618463580382990283149306547763612882790739596661288579270429165915520961430549308335611262291105257526688752231452325292372422392126098743361124105712978906797),
(599710014429286278,34179631418340749772033008303750654623882),
(295819462732210979463,707232636185649812258656132964997494597859517777983454243055867552148829507832938512780759420430421906455598838442889567054153907657250),
(577772388148849542,58075169305854204767396318815423916738419538375909209773394258204893745121214177322035673082727265322774807629883231790012696636846063312865608472746145852381737),
(77547532556056723007546249,34295555280775990255403148423),
(23657435100090826939933613425291,156607544444824632392394637447),
(577772388148853638,27863817267245907498521455682458686214631135149590492631361067803940074229858551714706745551530991689461284509605345178358318735330830715484512321084545575)
] : Array (Nat × Nat))[i%16]!
private def pack164 (i : Nat) : Nat × Nat := (#[
(77547532555838263489012617,4466310914),
(577772388148855430,2314794074068389994446901615878547811441571653985700048845853550383182157846371535632365905020416482166410009116),
(1128461695603205,753335601264324852701986310516772513208722926873605553004409035937414583274288290068930217044703480885972834948286993114340045806380194),
(687612496319237,2084002306),
(2574850,2225560066),
(9967746,2027379202),
(1340169800452,2269600258),
(2617704963,142039554),
(2651193987,145185282),
(1340198051588,148331010),
(1352013699,592927234),
(7145602,2076662274),
(8457602,1893161474),
(723175113732,604461570),
(1620579715,607607298),
(2543898624516,579295746)
] : Array (Nat × Nat))[i%16]!
private def pack165 (i : Nat) : Nat × Nat := (#[
(198969740911521502727,1849121282),
(2199931156484,462903810),
(4330229379,457660930),
(4296871171,456612354),
(5036184707,595024386),
(791626023684,591878658),
(9705090,1850169858),
(544016771,331831810),
(1340231409412,138893826),
(5036250243,597121538),
(3624929667,330783234),
(1856030928388,327637506),
(1855997570564,337074690),
(657837621764,581392898),
(2199964514308,453466626),
(959894325561758488290702394494360994252687,2444712450)
] : Array (Nat × Nat))[i%16]!
private def pack166 (i : Nat) : Nat × Nat := (#[
(7966567931601813847293266613322764,164311391163880248826366514439),
(1128461695593605,50684092521186976802042126237782987347763919596588475811473389533885941420963759227491353297197692598040268261852110631906550821926443492582564),
(2204026749188,299264556779295587350223614257186956890334013008169039683133318126869544103006860318667876320382700265930651),
(123012838834734965930632,15036673290775760818548614),
(123012838834734958124552,279886418843011076),
(4304739715,1358303591075358720102188120431639099115881980839472663068999267019455051062926669379382595379448534950090546646528665592991),
(9719810,18439144624427098394446567829784037020301324079095309),
(1137243795173765,4471761359147573368777758364660719721121988336908),
(5413219203,24785382123523),
(758374628007301,3126080002),
(298120820077246752903,1855008286403895655352345963717846847739728716190786690244722914228881653739745842766730994504409112397321985308),
(5167654915,15070427275011),
(582267226713372550,20332269096338875364007174),
(2547663906820,744019643654041809607921648878358492869060107),
(1137240677174533,796027255455433909608481390574524647925193723875354949121765857208854034),
(2749686456811567382769484016976902041870,83111341486597001455405632040470223871123122838286058192753886253826842310497556)
] : Array (Nat × Nat))[i%16]!
private def pack167 (i : Nat) : Nat × Nat := (#[
(152637859878295133632264,422190177766861503336719871558699418032879436400447726995764563112807309682194935871579847086872),
(229356490866949,273718032930837313443499412651030495457792395),
(298120820074795182855,7794560553393035887428759935299860111057073272940770230207979311580134554622597663958412912370896286825731103478736076895036200627041744875594394276830156218969301033889338340949661738076609117541518240180),
(298120820074795186055,35103580003777643513811683457836753409795673711213998980958661768928511126510093716838341522569655815185974385753118269985915046046015629154870577897949521145825567812504856784975794134175127587933324425076205247322942520),
(667854827261153798,300710583467394948),
(40013204224119258819093217674,2104666980115344223169103630319693896047639731397185051755303184),
(30783500431506197908104,150654557869221074181),
(40013204224119258423756075274,374298298345866047972608044590961713476225569076245226028425224890600173208748886452417887434392),
(582267226708584326,11355156129161561521125715544580115298018378014408552425647715107449482013203),
(4975896323,300154111782315524),
(20490783778149635687187246690699,16960003596927358846069126),
(298120820075032105735,46542690617884928667044062079714782015059732707174516249106554773002730837658532113909393199005674773411655114705521003609576709149184379591347319701477142539013186151408992640331694),
(581660622811440006,7306419598565925799691944865372231689),
(8003331,3360088066),
(582267226709047046,30495953187090406790344073568480675924106861320145121404111354583163533721305155913464180631),
(1137240677166085,1796093002026983923086825856330472298055849242508)
] : Array (Nat × Nat))[i%16]!
private def pack168 (i : Nat) : Nat × Nat := (#[
(174868893195778569877384,988891859147993353795430932571656),
(1137240677170565,563268287705335201755752398875155166005937121813808572857051781702223305443321562347702397202328),
(2221173197572,1125102087452167328171988859808052950531576724077644949699107861614982547953503394873569550932903322997114824220),
(1303818330180229,33124865413301570440544342771453722254858),
(2221615305604,10504076293393702434431903200206076583632315411236384824826853776),
(667863810655010054,20444623552681431138854406),
(2546520164996,300722830041437444),
(3690994947,2317813762),
(1053045962372,1095166691211654831751294520795774543141916709900),
(1303818330179589,33114662547274002016103128533753139453450),
(78150584104819976698013577,12698698515365003264440255632082628253076218878889236577723693793908772139188833936771280682495626505844793476150941),
(78150584104819976696838281,7619168331076578700031672063824190240609278780828925700473014853708027874191009256236448913725362299306163441268381),
(23470506159966909888358266185483,465315435792742183054692423982593256703206240323081876230198867886128638822570968669592746489240),
(152637859579726516987784,37246997132291),
(91431824953108734954656393,7717155708717882161705990),
(298120819491653353479,37949058633771482179509653120160157296971003646884036567541172079153733339355917101820709761590156096538)
] : Array (Nat × Nat))[i%16]!
private def pack169 (i : Nat) : Nat × Nat := (#[
(483089711236,150236448612442373730189141511),
(1137240674940677,4635572173900289039500187616850619482405970440432129693734198119403191936096279733325425792669738521),
(2221173193220,1730740118642865254550956768822272122742898998117787043531279502714785368027493616515037656578762373341233139320949506339058188880195536440751747942584471030107761234857724486081503714374704),
(4338228867,16232574645876296878941702),
(1137242552147077,597454556106473922432637575368117101238189195),
(1365511273398661,2197271682),
(298121311591451609863,55563315028818120994685434284240202141748201778026030657474963109218658052931862785700682007),
(582268186702053894,74092987523072672683077953031),
(1137242554911621,8711791142296028838703982870917075498722536172184648230386555152),
(1137242552152453,49930313088785914242665338534113487136030805274940685),
(1137242552158981,33188188611629284519411304509804650982352593073407555372211628784656506437738843459411268887),
(2221176859652,117756878603025758550364544230595578889129293746654926195245934782083644096906344872519809285345927834475382152596615901050587453716125978230976283942137688056551062529572557173519787793882415654450),
(582268187041006214,214198514373539653298148185586018547957150606296451026445416361976898299665276373514137851346232484618774934504550904067354334277216346389039168745182240210752024033812913734463682574767),
(4966328067,134774358077363460),
(58997947658176962834286985,13667604317315),
(582268187041015814,1891626608379784275710768287167243893641662398772889994890596390801090523219093855252467804674167781611687090373259348604119555514793106341145330805699802476576408395188501959418930639624467767547691315)
] : Array (Nat × Nat))[i%16]!
private def pack170 (i : Nat) : Nat × Nat := (#[
(152638283226318048413960,5576428185421989968006731855515473898840247839102161424493836082429035812755),
(298121311765005611783,18948896455351532821468243068412053271573371451874778920220714261250672371230971285808207055391251334075319225525846163737896397086905598498084),
(582268187041018758,183578983633863582001619253546581336911174999216579792678134637073938307296794956049219515863863957089976987),
(1137242552814469,756163718304004359756922558971540886528522635),
(10491271100838605491510090424988428,2557623871660821234298297903111962519531596554582603646248747396274633932903412017650899951504510807251066520476),
(40021023181299531957090079370,4404795869464923482588150137588072439649745223308),
(1137242552808325,16432169060043510444040550614346651686192013176292559927074228440633521910459589859033026749443178474260324239824157),
(1805805242756,2270899379788511110197133524754567599542405314316),
(2547865112836,274939904426837347321866776455166314372683147),
(2221176860932,28578797331408832510572857905960219722870898013995074039179173834350296613738859651915333908231365771713626036137113214071746274011895223406901903898476711),
(4338236035,72709723292058964360865785532240420165891009236031647057994321774844764323891319916495579427530323931502797735431011486),
(298121497376446624135,285361304443333366716179178141236540416243636877999499394610866171240414283685057370266954837976460889021303380546642401206938050780706),
(298121497376446624391,60999615818261711410491697760427777060629006102783273450903369752737533837363418665624456700972093289021313008749021342),
(1084295672640005,1898187650),
(1137243260996997,15446574422125918950604410125572702570667666204752593459436831919606105409555),
(2221178244100,22396583278057336975377500710857078422419987013239413459057662224)
] : Array (Nat × Nat))[i%16]!
private def pack171 (i : Nat) : Nat × Nat := (#[
(1302856461602053,9045907946787127553976535163074015113),
(1137243260860293,51099678321083575675820042831352011245662663571176589),
(1137243260847877,205779488327020865341243004983886248618555543971124045592055919543150002057894058284200741411971357638953627),
(2221178243844,55680709493728484978769291586258208220366839870865673031438708403300246555757204),
(4338238723,14090164014211),
(190078183659678001476744,14937845047994510749152390),
(582189606383400582,1168821637970243672024734766452488),
(2545513405700,141530530894437636),
(446716583300,3135780738),
(2221179089412,1038562708503057193089968737594160765881181680954812535116594045471691096880481602837),
(1137243693656069,24477934378023985333156570247237746564537202749813698741794873935973208434997186597403103079926620889376204046018270261230253437421641305460644),
(2221179089156,55449867318863592248910483943116413446314920231138427063280228059721359248523483416474713239),
(4338240387,5718003301489069268821162404616672022057076658947816065753528857483416210707),
(4338233731,12312795511293562734214385018267737219722636329635844904012324231112207929619),
(1302856461603333,2555898778485560956061089054125584731104437347400107530046863),
(341788505000899917703,88554221965174276)
] : Array (Nat × Nat))[i%16]!
private def pack172 (i : Nat) : Nat × Nat := (#[
(1755605378914550723786736573604174242856335,7546813258141920475365638),
(8473090,58216643624846322284826333435507349469401656091839120717724413320438310768860722561341549519614404898186180971546277567350741812997258077346737175166058257929945817308715),
(4337651843,19083333806479882930860931460692910992538637681857421),
(358077654249228999943,2597841794),
(3631827971,1297409538),
(16206836086627454941499560755595,296469578143740548),
(152523013231995608709128,684080736125968749073856647960010266390969002994195035010404688539385401732914545548652022979795960129569732578568479620937585326608657632853228138674761301005225),
(5366418511408328054605796193743863821,111595877097862588657646285910926134393195204000698910401403213235690804590679221776504473890301494044431259),
(1312511275506949,2597842946),
(581846713707023750,69999796817203972414020321143620649320878188298669940080706543749272709763151422264955121431),
(189145362551940694227848,14142857819779),
(1136419362708997,23931894106221102978269338869554701306103702976212875241704690576),
(20471279607627424098007187402251,620210288766589371957222871926444612247050984395709079503794765767234877471862592405),
(2449998211,2742417922),
(152522918656383509482760,2256897880617765011212715219987448380310857931544278067614607),
(297896325500815227527,2263433289377619671503423914832816559144172946609074894604637697708577350993644421275653575673381919043794499079204778168995825576785990947)
] : Array (Nat × Nat))[i%16]!
private def pack173 (i : Nat) : Nat × Nat := (#[
(5376332547,2578662274),
(581846352931651846,9227716056136367503958517443876637194885841960140194018380169242044002752787),
(297846160695485343623,128246884412451669798165189511),
(1136418658070149,269285798335383461488095223128213870317948648313086278269807428179357087382139120336503030212994096989425122384384303465971872950686754),
(9665871512523364004888004592651,7166300666283012750945030),
(69695100940096358908425,13035424974595),
(152303372427423668306568,3967056146096802760395982541259561225),
(36872373628705459325305353,227964114563),
(2746060433521845286213502983157961992334,11454240316363788585620447954475720329),
(10491109828742260862076792549746444,13636960507289075405271980534846129464251466880875328186526145078206117856659),
(10481295159107433529825782453709964,10184721687437177229359620648889278337070318857775938936743076080783200901395),
(20471279607627171939342892935051,10184721831380006706154032597126212563211795828689807365386463763543351525139),
(78091734352067153986397321,55173586291984471556504458119),
(20471279609993145542039860816011,417124851605068087425514912988424320514924662777401703528595134326317756318715243352674244523672),
(78164859578696319918492425,85996659622474636725090655619754613118442664214063637529624120431505),
(78164995763459951499497865,20495858663356324509972870)
] : Array (Nat × Nat))[i%16]!
private def pack174 (i : Nat) : Nat × Nat := (#[
(40007716477018343373282495754,2543511406418433698561869299002887585769830297839379503017715830535833706128481886704662),
(4406594947,2009339778),
(39982967988267862386802435850,3470091291983708012551754279126517228089303845849269026722703),
(1136418658069509,66832910187266262585714970747089835964733934226577253463952495364140309130392181721654349591),
(2219567691524,28388411936091639760597793498312234004411428986291020008752976912),
(10481295161046169926140207688386956,112208308383423581292336812935),
(618022343880279046,283462443084356484),
(10481295161046169926140207685377676,5873353929345463906091085984257189031880759827296748907726024549884723352897995081087526228277909192849974573681627107412171040),
(20471279611418300636118067642763,3075507160736635425267037546110377424949949861955239469429415917178842557521869731541526),
(40577086446964766281337742346,13598774616195),
(39982992783475404476516081162,7749182479992828258440775772455288125865661619077687863736224520165498883170269722235918281754007504334887596601885),
(5608392579,18837219126534867708010214041993239066179318464069133),
(3633711107,2223710535782333618263337556061694803104849213068),
(152522918472506889358088,15211238509610214895230470),
(39982967991051368429918100874,2504203588548131747803639381413192763574080955002105621943183),
(59401724097854566833927689,1525025951568740526597)
] : Array (Nat × Nat))[i%16]!
private def pack175 (i : Nat) : Nat × Nat := (#[
(5043917827,2253730746003719783520243088551750758426742089868),
(9835650,4490551170),
(5004808579,12665930143235),
(581846354844254214,3598000587312996191810475761021778445025677433682991796637372889841287154391951184187658489332345898083997202097123325087970319358558245795),
(176277587738403693808392,71300678576945680215514767877826803937930),
(298207184293014098567,11267717495978764450419705310206032265),
(581730816900999046,37867241378691),
(154883974839734175079560,282443342426063655319952246456032740967238411),
(5612974979,3575075586),
(1136418661805189,18436500928312376227383347782499576368946577070489956455757302936738897104607944816000045164188202598524006118757277),
(581580596260045702,146646302766795502777740962553528821561742192124997702542),
(582189882708151174,11535116984022167613393438203019039625),
(152522918667035530439560,63804777180515242683289760149822580153517785914925803332120376994201312258301979074473005975),
(527887793653765,32263107593410752444363887402215260252554),
(1136418661812101,10134685086714897400227090429723976656208424609953223857483717837704571392287892799376132744676384396411608613273966435738762375865716552146999318204166055),
(152522918667035530363784,2933162114389643909715235206155552718232702137333295067696481128285463704437508435054935323100771861299094959204947177368496822125105756951259062506406)
] : Array (Nat × Nat))[i%16]!
private def pack176 (i : Nat) : Nat × Nat := (#[
(78091734383849823330513673,9495861775657069174275378275908808902756025717219668354563716778599820104034911654129766376896848607539419588105117),
(152522918718456687174664,3567284297065554059031867342737346944669239187467515732485943623334612105036978126574689529271718809),
(297851385542695528199,502186253882309276131417329382275188377817995),
(152527404593696809759624,2965837077901945999954415765193282929173252567160199169186914550210111053971),
(1136383358285445,97996467463173181187565327239),
(2219567698820,6399874999480922159147619959667214123456951262690901663387970816055586725136093153869639460314557829766973631981160373941069519302775313315),
(10767106,4654148482),
(1074738307,312732290),
(36528025771269,4280625794),
(302507765795943357831,350676821834642829395688491856392),
(1073948035,123951106),
(1342440835,168203778),
(1341983050756,2275172919914244265191685351539750647709494119564),
(343774035721861736455,57737562813097380173713836105480),
(4150872368700390648532935837451,17994299346708274968048442209062026122742435761381517),
(1774331692932,4678177154)
] : Array (Nat × Nat))[i%16]!
private def pack177 (i : Nat) : Nat × Nat := (#[
(1136418660951045,176109056347869438497343910494666525540722755587675660698595230590861841585035963293032180298447454616149415986433921950),
(5107353603,2225139791247289373306990112540791791134156580364),
(2221275685508,2738062722),
(1683698747524,22723754871299),
(2219567697156,19919474473501611857637763691718100123637990749570505010849196772881300468323108223177125598242961919602597633008866997833801089636394602876933029),
(139348995,291426664501522883509906851724103401074672031372),
(1136418660496133,2184307940113791691112735416278226848361197803637065676099838170417731103908313255317659814277457177),
(1136418650990341,2318130663018160813693878174786233993084410653203207648213439805866162126570783532215177919568076187983914716956),
(2219567687556,165737548281309226279738513909708103338470421193743479973904929826065),
(2219567690628,21003269475885620329457050099277370145787377894375962556326011266713034547646375704153639683130351855596121526427328593809738932637215123517122949139762169254846754493355),
(4335093123,10792348922433461654141597693003981800672002014361660204531316488775790114176791502055168434923396858026565819231801898802859808),
(4606019459,1480800258),
(1136417414461317,7788669089418365392502341497256863577824259141252511305124932845582932322494650718393238),
(2219565262596,21261449592542311441843908010350525418036195424645744598085708863373805550658117271041184179740886069939278607586205),
(4333708291,1408393555008315965280372901057416),
(20788810677543514673404956377483,9136623519854034151104823074049349129)
] : Array (Nat × Nat))[i%16]!
private def pack178 (i : Nat) : Nat × Nat := (#[
(2219565266692,940654024805064213541348308222860148588836403668594286084388069509756528615708038298322548264584170329608864156),
(4335088387,972457875701774758932489391277498671686937567932653300920516974845810196981234073418264635151602733403654955520988229511293603509313376331374686120011632340364609905420832560254568665144306501674374067),
(744134458744506502,26295486964615765311938584505989705782666),
(1136416642178693,75411433447420132661012938849107227972419567434347831116470516390100271262814740820815819462948451067671723914086060268153993740321),
(2219563752964,1093468045959206203326409290072968),
(231026870125319953671,26700114480259),
(4335085443,6603912977269176075381953233388162513145951286619958105602837273222022694359268767027873858975955074180737844928939579873152800),
(8466946,435459508919134945035828333961814891114487961784061705608360644914623217624115226804867453981592),
(2218820650244,636358910428434535072621544485997020407104907),
(4333646083,26252964246463914317894852358142609422364169460681427227377537407076584174619906745691202830494136216977369496755687095889321559905404761552272102478599071640946264737300553382363474238217881009),
(8466818,963206144466775001811521371673480),
(8472450,208169980570039831464646932590678333053106742541584496122434723301009),
(8454274,183820375932911012408897435352566807514860126721023566293607265905880267333660209057118311158617607221768783157738705459339104152492824869814718383648927289883962050431131138132004223697695009952398031888494386892185049826909221273847213974155203519),
(4404103811,188531153524737876779635795235968698881388076390437568156044465708817),
(8473218,4717901442),
(16513,4719154050)
] : Array (Nat × Nat))[i%16]!
private def pack179 (i : Nat) : Nat × Nat := (#[
(9764866,172624342044267655449368119943),
(8594562,5979721428049267587764164358876359662381998952330196740107307618391007828275371992673132474581578882662416246370996339831446206115773729443),
(4402925187,1917518482011701346541329088013523088069618437277157151681606583291792018),
(2254293126404,13642974596900323515702560059540125054107477773352408705188543080303821393721300793143471794710134515838077468953702793899840299572857511445958982681915809464636313613412605239379427406262094513),
(4402924931,1473024232532935650077260724072543539014677454874970839727671515656100931348396805481835927754558105),
(8599426,25092118462382442517741551216911358950826732798985472574989157694831862115753334082870645593547967162236907109154511962695504923641653049251366596618022387624448105706245784592763566),
(8604930,8319239501767257293334347760494234249),
(8586114,1630836663408448268692915582393538892278983491783391634999112228237622920088304513831975880256703129),
(9781634,118414529753319891234364929537189690338278883398316017980211150631073839526446411444747132017960047641500822346221653231509179927144493353361644301441763347388196710684271549501584510118389294353074),
(16769,38742799207043),
(3469623866865130273942993315737338982670,116261598841675348822216093573875857499566920454482835218364185318802924464218889249702252309475681388513947),
(1479822035460,78151261227337771239261917063),
(6776609114971003860110617302403601165,237593061654579190547058957922020830069526745744506043264871008096145),
(50489672384940117332070117002,168633996777346959279610891701917844914191212046287682843490953777041),
(25830904093022788030471865244939,37483444279183285624613577506700519853962),
(756569428140549,220652670680381861687409305035877418591284258289725779921274496666257)
] : Array (Nat × Nat))[i%16]!
private def pack180 (i : Nat) : Nat × Nat := (#[
(4541058,173425518154664580),
(1477573942532,1354320311807817550033303183608456),
(101549641986977690222728,2183053695181936590472950930897863429075058284734688620709109999532633005074214922326327879692772054003745345436),
(1477674664324,8584265426076848906317862808427359319539439301744837112720275325442268276089725916281917771042253012137985835499382557809860880819015579234662877019727205812487045914789559193517),
(1202797281540,6297519250111071178510214),
(2886083331,318246300548647556),
(699335682641773062,1489094540252004536197),
(1016937923204,1853348866),
(756569700237317,3616674902812611816015384543411780414322159214585831689346188363727250105537940182075821011652785712129686554718580972290140171836554452858765819038374),
(1477675195780,659787494427641884413139968143938368492171100466335365734638007329036848953539413759559162697358331288950923711835304208971870273851298),
(68803801343572073808768252955746407698959,2159482709828833346281654156760848392366200402775904152504975),
(5073883779,300394790216655489276843378831761651389502475),
(512628267202364077403834992117644,245321273518026632591610875044147917334174812711711641358),
(2886084355,3767403739356241916668304564236360839705208427767257247320521610468080739866842391500906092222270105),
(756570210584325,2185610928847809205637),
(387363346015912070,335368808237501549419368717289337740297114878648142188554728513549548519025074547194083152546456)
] : Array (Nat × Nat))[i%16]!
private def pack181 (i : Nat) : Nat × Nat := (#[
(756569035187333,24938708953016006023651769782494344740353274528387158414695721785611448216330948702218275479),
(102069920703327374599,60622643290918376217140316807),
(1477673896836,27997446934614039464717283317872513720294480724508774222745689678886120585219507887730908458052167987671303555699929154493402102661514555491029259608706983),
(137515377668,1326502290333785665669),
(2886081795,1057684115446266193142683632713134488601743033080686426653543508247228909691317801775483116700445187847833046940),
(756572123248261,43180917561870860502472086818512993574154),
(1477672061700,1713958886059223224233488637293092466366595819145657610710346353627156370),
(23487454677772278922709094517771,670779273316631512360658799348531700521132731189814277171071668705588754),
(264229811537925,270925590913049817405861909371438982119852555),
(1196509846834693,280478210),
(2337134227972,4764001538),
(2886078211,144235078539373985700807699224525762581451981019835562656315657313463678198178763319185805154893456153158050712306136597924162130482802038015517013352142916264),
(5636866,146657669718782702308769952775),
(2894603395,21336700479873194791592198),
(240258931157144847623,298518983483076356),
(1482034203268,508666213986907033864585891372732279400087162206007818438469413177302500048882993896109128002074568223491791914345601975885751651977890)
] : Array (Nat × Nat))[i%16]!
private def pack182 (i : Nat) : Nat × Nat := (#[
(2894598019,18322082528654002863288832977634280264033102632372877),
(1482041859332,268486525264214189907099155675677532743692312605983370958936548101295013620277053994042241992746562316883337247341573551646657130843004545298647717),
(1482041864836,7356876416481564238800707874955216889606885201368098110438258272526609650926003034697011869706489231915958975369014954690287503496526140160068891282179974766336265174579345412013),
(1482041859588,22557902407134699017570933240327006821706506133452769712444852880),
(34753687353491154238695685002,1789425922),
(2894612995,1618798794441975760628978012940612031946768743368808002990942599310677421880768075257596799195416316469547025857444008604031615185092655182172405248111690731016105),
(2894597635,2256733083979740817896232539769181404145577738435484691408864820848002410188249835373365442458995353),
(5653506,34134439088844697200923677186723472902965055704623007608491627622252888682524111503992072666444709373710962277650040570697557118607143382601636),
(5656834,1707829602455777001760957829519148107944688228857189407579969741332885328109387351689814100382633881),
(5639426,265336739344117730766383804033412690359964765960056677193521596129822532401177257976956714535576),
(5646082,1278044045053738555792073492198148567047816814802900193167628302632968796665712456468372280404673650046110478987377799384991),
(11009,39174081667331),
(19073,4744557039177617297072806754201946761),
(4993,4473809154),
(5761,4492683522),
(12545,22269830686979)
] : Array (Nat × Nat))[i%16]!
private def pack183 (i : Nat) : Nat × Nat := (#[
(17537,93840204015134980),
(33281,301006319505697028),
(49921,768167064422101608709),
(9985,18971358718211),
(8961,18928409045763),
(8705,23231903362179),
(10241,68930184025795716),
(9217,63863677393628420),
(3329,1437216182058081962738717437775752),
(5413019139,11545994614370188329464802481765358312895934613965782156025991543271260541085719135173532971502967213927776249116370488237026592),
(10572290,169545930516856789948583721585057435297056467825837989062398441889392367856208435322424499623067152621443959060304341373379156272427882223384240250323413290920),
(10570626,434514994169726252276135428870843876415811707095237830828715146961546770),
(3969,18327491803662747454442526923173149983169684975439757),
(20481,4509460738),
(21377,36958681756035),
(19329,4799918466)
] : Array (Nat × Nat))[i%16]!
private def pack184 (i : Nat) : Nat × Nat := (#[
(18177,30301500273155),
(0,1614984039274974343941)
] : Array (Nat × Nat))[i%16]!
private def packed (i : Nat) : Nat × Nat := (if i < 1472 then (if i < 736 then (if i < 368 then (if i < 176 then (if i < 80 then (if i < 32 then (if i < 16 then (pack0 i) else (pack1 i)) else (if i < 48 then (pack2 i) else (if i < 64 then (pack3 i) else (pack4 i)))) else (if i < 128 then (if i < 96 then (pack5 i) else (if i < 112 then (pack6 i) else (pack7 i))) else (if i < 144 then (pack8 i) else (if i < 160 then (pack9 i) else (pack10 i))))) else (if i < 272 then (if i < 224 then (if i < 192 then (pack11 i) else (if i < 208 then (pack12 i) else (pack13 i))) else (if i < 240 then (pack14 i) else (if i < 256 then (pack15 i) else (pack16 i)))) else (if i < 320 then (if i < 288 then (pack17 i) else (if i < 304 then (pack18 i) else (pack19 i))) else (if i < 336 then (pack20 i) else (if i < 352 then (pack21 i) else (pack22 i)))))) else (if i < 544 then (if i < 448 then (if i < 400 then (if i < 384 then (pack23 i) else (pack24 i)) else (if i < 416 then (pack25 i) else (if i < 432 then (pack26 i) else (pack27 i)))) else (if i < 496 then (if i < 464 then (pack28 i) else (if i < 480 then (pack29 i) else (pack30 i))) else (if i < 512 then (pack31 i) else (if i < 528 then (pack32 i) else (pack33 i))))) else (if i < 640 then (if i < 592 then (if i < 560 then (pack34 i) else (if i < 576 then (pack35 i) else (pack36 i))) else (if i < 608 then (pack37 i) else (if i < 624 then (pack38 i) else (pack39 i)))) else (if i < 688 then (if i < 656 then (pack40 i) else (if i < 672 then (pack41 i) else (pack42 i))) else (if i < 704 then (pack43 i) else (if i < 720 then (pack44 i) else (pack45 i))))))) else (if i < 1104 then (if i < 912 then (if i < 816 then (if i < 768 then (if i < 752 then (pack46 i) else (pack47 i)) else (if i < 784 then (pack48 i) else (if i < 800 then (pack49 i) else (pack50 i)))) else (if i < 864 then (if i < 832 then (pack51 i) else (if i < 848 then (pack52 i) else (pack53 i))) else (if i < 880 then (pack54 i) else (if i < 896 then (pack55 i) else (pack56 i))))) else (if i < 1008 then (if i < 960 then (if i < 928 then (pack57 i) else (if i < 944 then (pack58 i) else (pack59 i))) else (if i < 976 then (pack60 i) else (if i < 992 then (pack61 i) else (pack62 i)))) else (if i < 1056 then (if i < 1024 then (pack63 i) else (if i < 1040 then (pack64 i) else (pack65 i))) else (if i < 1072 then (pack66 i) else (if i < 1088 then (pack67 i) else (pack68 i)))))) else (if i < 1280 then (if i < 1184 then (if i < 1136 then (if i < 1120 then (pack69 i) else (pack70 i)) else (if i < 1152 then (pack71 i) else (if i < 1168 then (pack72 i) else (pack73 i)))) else (if i < 1232 then (if i < 1200 then (pack74 i) else (if i < 1216 then (pack75 i) else (pack76 i))) else (if i < 1248 then (pack77 i) else (if i < 1264 then (pack78 i) else (pack79 i))))) else (if i < 1376 then (if i < 1328 then (if i < 1296 then (pack80 i) else (if i < 1312 then (pack81 i) else (pack82 i))) else (if i < 1344 then (pack83 i) else (if i < 1360 then (pack84 i) else (pack85 i)))) else (if i < 1424 then (if i < 1392 then (pack86 i) else (if i < 1408 then (pack87 i) else (pack88 i))) else (if i < 1440 then (pack89 i) else (if i < 1456 then (pack90 i) else (pack91 i)))))))) else (if i < 2208 then (if i < 1840 then (if i < 1648 then (if i < 1552 then (if i < 1504 then (if i < 1488 then (pack92 i) else (pack93 i)) else (if i < 1520 then (pack94 i) else (if i < 1536 then (pack95 i) else (pack96 i)))) else (if i < 1600 then (if i < 1568 then (pack97 i) else (if i < 1584 then (pack98 i) else (pack99 i))) else (if i < 1616 then (pack100 i) else (if i < 1632 then (pack101 i) else (pack102 i))))) else (if i < 1744 then (if i < 1696 then (if i < 1664 then (pack103 i) else (if i < 1680 then (pack104 i) else (pack105 i))) else (if i < 1712 then (pack106 i) else (if i < 1728 then (pack107 i) else (pack108 i)))) else (if i < 1792 then (if i < 1760 then (pack109 i) else (if i < 1776 then (pack110 i) else (pack111 i))) else (if i < 1808 then (pack112 i) else (if i < 1824 then (pack113 i) else (pack114 i)))))) else (if i < 2016 then (if i < 1920 then (if i < 1872 then (if i < 1856 then (pack115 i) else (pack116 i)) else (if i < 1888 then (pack117 i) else (if i < 1904 then (pack118 i) else (pack119 i)))) else (if i < 1968 then (if i < 1936 then (pack120 i) else (if i < 1952 then (pack121 i) else (pack122 i))) else (if i < 1984 then (pack123 i) else (if i < 2000 then (pack124 i) else (pack125 i))))) else (if i < 2112 then (if i < 2064 then (if i < 2032 then (pack126 i) else (if i < 2048 then (pack127 i) else (pack128 i))) else (if i < 2080 then (pack129 i) else (if i < 2096 then (pack130 i) else (pack131 i)))) else (if i < 2160 then (if i < 2128 then (pack132 i) else (if i < 2144 then (pack133 i) else (pack134 i))) else (if i < 2176 then (pack135 i) else (if i < 2192 then (pack136 i) else (pack137 i))))))) else (if i < 2576 then (if i < 2384 then (if i < 2288 then (if i < 2240 then (if i < 2224 then (pack138 i) else (pack139 i)) else (if i < 2256 then (pack140 i) else (if i < 2272 then (pack141 i) else (pack142 i)))) else (if i < 2336 then (if i < 2304 then (pack143 i) else (if i < 2320 then (pack144 i) else (pack145 i))) else (if i < 2352 then (pack146 i) else (if i < 2368 then (pack147 i) else (pack148 i))))) else (if i < 2480 then (if i < 2432 then (if i < 2400 then (pack149 i) else (if i < 2416 then (pack150 i) else (pack151 i))) else (if i < 2448 then (pack152 i) else (if i < 2464 then (pack153 i) else (pack154 i)))) else (if i < 2528 then (if i < 2496 then (pack155 i) else (if i < 2512 then (pack156 i) else (pack157 i))) else (if i < 2544 then (pack158 i) else (if i < 2560 then (pack159 i) else (pack160 i)))))) else (if i < 2768 then (if i < 2672 then (if i < 2624 then (if i < 2592 then (pack161 i) else (if i < 2608 then (pack162 i) else (pack163 i))) else (if i < 2640 then (pack164 i) else (if i < 2656 then (pack165 i) else (pack166 i)))) else (if i < 2720 then (if i < 2688 then (pack167 i) else (if i < 2704 then (pack168 i) else (pack169 i))) else (if i < 2736 then (pack170 i) else (if i < 2752 then (pack171 i) else (pack172 i))))) else (if i < 2864 then (if i < 2816 then (if i < 2784 then (pack173 i) else (if i < 2800 then (pack174 i) else (pack175 i))) else (if i < 2832 then (pack176 i) else (if i < 2848 then (pack177 i) else (pack178 i)))) else (if i < 2912 then (if i < 2880 then (pack179 i) else (if i < 2896 then (pack180 i) else (pack181 i))) else (if i < 2928 then (pack182 i) else (if i < 2944 then (pack183 i) else (pack184 i)))))))))
/-- The low seven bits store the length. The remaining digits are in
little-endian order, with nine bits per literal or thirteen bits per hint. -/
private def unpack (base : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | len+1, val => val % base :: unpack base len (val / base)

private def learned (i : Nat) : List Nat × List Nat :=
  let v := packed i
  (unpack 512 (v.1 % 128) (v.1 / 128), unpack 8192 (v.2 % 128) (v.2 / 128))

private abbrev pass := stepOK input9 learned 1638

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 10000 in
private theorem block0 : ∀ i, 0 ≤ i → i < 192 → pass i = true :=
  (@pass_merge pass 0 96 192 (@pass_merge pass 0 48 96 (@pass_merge pass 0 24 48 (@pass_merge pass 0 12 24 (pass_range pass 0 12 (by decide +kernel)) (pass_range pass 12 12 (by decide +kernel))) (@pass_merge pass 24 36 48 (pass_range pass 24 12 (by decide +kernel)) (pass_range pass 36 12 (by decide +kernel)))) (@pass_merge pass 48 72 96 (@pass_merge pass 48 60 72 (pass_range pass 48 12 (by decide +kernel)) (pass_range pass 60 12 (by decide +kernel))) (@pass_merge pass 72 84 96 (pass_range pass 72 12 (by decide +kernel)) (pass_range pass 84 12 (by decide +kernel))))) (@pass_merge pass 96 144 192 (@pass_merge pass 96 120 144 (@pass_merge pass 96 108 120 (pass_range pass 96 12 (by decide +kernel)) (pass_range pass 108 12 (by decide +kernel))) (@pass_merge pass 120 132 144 (pass_range pass 120 12 (by decide +kernel)) (pass_range pass 132 12 (by decide +kernel)))) (@pass_merge pass 144 168 192 (@pass_merge pass 144 156 168 (pass_range pass 144 12 (by decide +kernel)) (pass_range pass 156 12 (by decide +kernel))) (@pass_merge pass 168 180 192 (pass_range pass 168 12 (by decide +kernel)) (pass_range pass 180 12 (by decide +kernel))))))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 10000 in
private theorem block192 : ∀ i, 192 ≤ i → i < 384 → pass i = true :=
  (@pass_merge pass 192 288 384 (@pass_merge pass 192 240 288 (@pass_merge pass 192 216 240 (@pass_merge pass 192 204 216 (pass_range pass 192 12 (by decide +kernel)) (pass_range pass 204 12 (by decide +kernel))) (@pass_merge pass 216 228 240 (pass_range pass 216 12 (by decide +kernel)) (pass_range pass 228 12 (by decide +kernel)))) (@pass_merge pass 240 264 288 (@pass_merge pass 240 252 264 (pass_range pass 240 12 (by decide +kernel)) (pass_range pass 252 12 (by decide +kernel))) (@pass_merge pass 264 276 288 (pass_range pass 264 12 (by decide +kernel)) (pass_range pass 276 12 (by decide +kernel))))) (@pass_merge pass 288 336 384 (@pass_merge pass 288 312 336 (@pass_merge pass 288 300 312 (pass_range pass 288 12 (by decide +kernel)) (pass_range pass 300 12 (by decide +kernel))) (@pass_merge pass 312 324 336 (pass_range pass 312 12 (by decide +kernel)) (pass_range pass 324 12 (by decide +kernel)))) (@pass_merge pass 336 360 384 (@pass_merge pass 336 348 360 (pass_range pass 336 12 (by decide +kernel)) (pass_range pass 348 12 (by decide +kernel))) (@pass_merge pass 360 372 384 (pass_range pass 360 12 (by decide +kernel)) (pass_range pass 372 12 (by decide +kernel))))))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 10000 in
private theorem block384 : ∀ i, 384 ≤ i → i < 576 → pass i = true :=
  (@pass_merge pass 384 480 576 (@pass_merge pass 384 432 480 (@pass_merge pass 384 408 432 (@pass_merge pass 384 396 408 (pass_range pass 384 12 (by decide +kernel)) (pass_range pass 396 12 (by decide +kernel))) (@pass_merge pass 408 420 432 (pass_range pass 408 12 (by decide +kernel)) (pass_range pass 420 12 (by decide +kernel)))) (@pass_merge pass 432 456 480 (@pass_merge pass 432 444 456 (pass_range pass 432 12 (by decide +kernel)) (pass_range pass 444 12 (by decide +kernel))) (@pass_merge pass 456 468 480 (pass_range pass 456 12 (by decide +kernel)) (pass_range pass 468 12 (by decide +kernel))))) (@pass_merge pass 480 528 576 (@pass_merge pass 480 504 528 (@pass_merge pass 480 492 504 (pass_range pass 480 12 (by decide +kernel)) (pass_range pass 492 12 (by decide +kernel))) (@pass_merge pass 504 516 528 (pass_range pass 504 12 (by decide +kernel)) (pass_range pass 516 12 (by decide +kernel)))) (@pass_merge pass 528 552 576 (@pass_merge pass 528 540 552 (pass_range pass 528 12 (by decide +kernel)) (pass_range pass 540 12 (by decide +kernel))) (@pass_merge pass 552 564 576 (pass_range pass 552 12 (by decide +kernel)) (pass_range pass 564 12 (by decide +kernel))))))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 10000 in
private theorem block576 : ∀ i, 576 ≤ i → i < 768 → pass i = true :=
  (@pass_merge pass 576 672 768 (@pass_merge pass 576 624 672 (@pass_merge pass 576 600 624 (@pass_merge pass 576 588 600 (pass_range pass 576 12 (by decide +kernel)) (pass_range pass 588 12 (by decide +kernel))) (@pass_merge pass 600 612 624 (pass_range pass 600 12 (by decide +kernel)) (pass_range pass 612 12 (by decide +kernel)))) (@pass_merge pass 624 648 672 (@pass_merge pass 624 636 648 (pass_range pass 624 12 (by decide +kernel)) (pass_range pass 636 12 (by decide +kernel))) (@pass_merge pass 648 660 672 (pass_range pass 648 12 (by decide +kernel)) (pass_range pass 660 12 (by decide +kernel))))) (@pass_merge pass 672 720 768 (@pass_merge pass 672 696 720 (@pass_merge pass 672 684 696 (pass_range pass 672 12 (by decide +kernel)) (pass_range pass 684 12 (by decide +kernel))) (@pass_merge pass 696 708 720 (pass_range pass 696 12 (by decide +kernel)) (pass_range pass 708 12 (by decide +kernel)))) (@pass_merge pass 720 744 768 (@pass_merge pass 720 732 744 (pass_range pass 720 12 (by decide +kernel)) (pass_range pass 732 12 (by decide +kernel))) (@pass_merge pass 744 756 768 (pass_range pass 744 12 (by decide +kernel)) (pass_range pass 756 12 (by decide +kernel))))))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 10000 in
private theorem block768 : ∀ i, 768 ≤ i → i < 960 → pass i = true :=
  (@pass_merge pass 768 864 960 (@pass_merge pass 768 816 864 (@pass_merge pass 768 792 816 (@pass_merge pass 768 780 792 (pass_range pass 768 12 (by decide +kernel)) (pass_range pass 780 12 (by decide +kernel))) (@pass_merge pass 792 804 816 (pass_range pass 792 12 (by decide +kernel)) (pass_range pass 804 12 (by decide +kernel)))) (@pass_merge pass 816 840 864 (@pass_merge pass 816 828 840 (pass_range pass 816 12 (by decide +kernel)) (pass_range pass 828 12 (by decide +kernel))) (@pass_merge pass 840 852 864 (pass_range pass 840 12 (by decide +kernel)) (pass_range pass 852 12 (by decide +kernel))))) (@pass_merge pass 864 912 960 (@pass_merge pass 864 888 912 (@pass_merge pass 864 876 888 (pass_range pass 864 12 (by decide +kernel)) (pass_range pass 876 12 (by decide +kernel))) (@pass_merge pass 888 900 912 (pass_range pass 888 12 (by decide +kernel)) (pass_range pass 900 12 (by decide +kernel)))) (@pass_merge pass 912 936 960 (@pass_merge pass 912 924 936 (pass_range pass 912 12 (by decide +kernel)) (pass_range pass 924 12 (by decide +kernel))) (@pass_merge pass 936 948 960 (pass_range pass 936 12 (by decide +kernel)) (pass_range pass 948 12 (by decide +kernel))))))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 10000 in
private theorem block960 : ∀ i, 960 ≤ i → i < 1152 → pass i = true :=
  (@pass_merge pass 960 1056 1152 (@pass_merge pass 960 1008 1056 (@pass_merge pass 960 984 1008 (@pass_merge pass 960 972 984 (pass_range pass 960 12 (by decide +kernel)) (pass_range pass 972 12 (by decide +kernel))) (@pass_merge pass 984 996 1008 (pass_range pass 984 12 (by decide +kernel)) (pass_range pass 996 12 (by decide +kernel)))) (@pass_merge pass 1008 1032 1056 (@pass_merge pass 1008 1020 1032 (pass_range pass 1008 12 (by decide +kernel)) (pass_range pass 1020 12 (by decide +kernel))) (@pass_merge pass 1032 1044 1056 (pass_range pass 1032 12 (by decide +kernel)) (pass_range pass 1044 12 (by decide +kernel))))) (@pass_merge pass 1056 1104 1152 (@pass_merge pass 1056 1080 1104 (@pass_merge pass 1056 1068 1080 (pass_range pass 1056 12 (by decide +kernel)) (pass_range pass 1068 12 (by decide +kernel))) (@pass_merge pass 1080 1092 1104 (pass_range pass 1080 12 (by decide +kernel)) (pass_range pass 1092 12 (by decide +kernel)))) (@pass_merge pass 1104 1128 1152 (@pass_merge pass 1104 1116 1128 (pass_range pass 1104 12 (by decide +kernel)) (pass_range pass 1116 12 (by decide +kernel))) (@pass_merge pass 1128 1140 1152 (pass_range pass 1128 12 (by decide +kernel)) (pass_range pass 1140 12 (by decide +kernel))))))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 10000 in
private theorem block1152 : ∀ i, 1152 ≤ i → i < 1344 → pass i = true :=
  (@pass_merge pass 1152 1248 1344 (@pass_merge pass 1152 1200 1248 (@pass_merge pass 1152 1176 1200 (@pass_merge pass 1152 1164 1176 (pass_range pass 1152 12 (by decide +kernel)) (pass_range pass 1164 12 (by decide +kernel))) (@pass_merge pass 1176 1188 1200 (pass_range pass 1176 12 (by decide +kernel)) (pass_range pass 1188 12 (by decide +kernel)))) (@pass_merge pass 1200 1224 1248 (@pass_merge pass 1200 1212 1224 (pass_range pass 1200 12 (by decide +kernel)) (pass_range pass 1212 12 (by decide +kernel))) (@pass_merge pass 1224 1236 1248 (pass_range pass 1224 12 (by decide +kernel)) (pass_range pass 1236 12 (by decide +kernel))))) (@pass_merge pass 1248 1296 1344 (@pass_merge pass 1248 1272 1296 (@pass_merge pass 1248 1260 1272 (pass_range pass 1248 12 (by decide +kernel)) (pass_range pass 1260 12 (by decide +kernel))) (@pass_merge pass 1272 1284 1296 (pass_range pass 1272 12 (by decide +kernel)) (pass_range pass 1284 12 (by decide +kernel)))) (@pass_merge pass 1296 1320 1344 (@pass_merge pass 1296 1308 1320 (pass_range pass 1296 12 (by decide +kernel)) (pass_range pass 1308 12 (by decide +kernel))) (@pass_merge pass 1320 1332 1344 (pass_range pass 1320 12 (by decide +kernel)) (pass_range pass 1332 12 (by decide +kernel))))))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 10000 in
private theorem block1344 : ∀ i, 1344 ≤ i → i < 1536 → pass i = true :=
  (@pass_merge pass 1344 1440 1536 (@pass_merge pass 1344 1392 1440 (@pass_merge pass 1344 1368 1392 (@pass_merge pass 1344 1356 1368 (pass_range pass 1344 12 (by decide +kernel)) (pass_range pass 1356 12 (by decide +kernel))) (@pass_merge pass 1368 1380 1392 (pass_range pass 1368 12 (by decide +kernel)) (pass_range pass 1380 12 (by decide +kernel)))) (@pass_merge pass 1392 1416 1440 (@pass_merge pass 1392 1404 1416 (pass_range pass 1392 12 (by decide +kernel)) (pass_range pass 1404 12 (by decide +kernel))) (@pass_merge pass 1416 1428 1440 (pass_range pass 1416 12 (by decide +kernel)) (pass_range pass 1428 12 (by decide +kernel))))) (@pass_merge pass 1440 1488 1536 (@pass_merge pass 1440 1464 1488 (@pass_merge pass 1440 1452 1464 (pass_range pass 1440 12 (by decide +kernel)) (pass_range pass 1452 12 (by decide +kernel))) (@pass_merge pass 1464 1476 1488 (pass_range pass 1464 12 (by decide +kernel)) (pass_range pass 1476 12 (by decide +kernel)))) (@pass_merge pass 1488 1512 1536 (@pass_merge pass 1488 1500 1512 (pass_range pass 1488 12 (by decide +kernel)) (pass_range pass 1500 12 (by decide +kernel))) (@pass_merge pass 1512 1524 1536 (pass_range pass 1512 12 (by decide +kernel)) (pass_range pass 1524 12 (by decide +kernel))))))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 10000 in
private theorem block1536 : ∀ i, 1536 ≤ i → i < 1728 → pass i = true :=
  (@pass_merge pass 1536 1632 1728 (@pass_merge pass 1536 1584 1632 (@pass_merge pass 1536 1560 1584 (@pass_merge pass 1536 1548 1560 (pass_range pass 1536 12 (by decide +kernel)) (pass_range pass 1548 12 (by decide +kernel))) (@pass_merge pass 1560 1572 1584 (pass_range pass 1560 12 (by decide +kernel)) (pass_range pass 1572 12 (by decide +kernel)))) (@pass_merge pass 1584 1608 1632 (@pass_merge pass 1584 1596 1608 (pass_range pass 1584 12 (by decide +kernel)) (pass_range pass 1596 12 (by decide +kernel))) (@pass_merge pass 1608 1620 1632 (pass_range pass 1608 12 (by decide +kernel)) (pass_range pass 1620 12 (by decide +kernel))))) (@pass_merge pass 1632 1680 1728 (@pass_merge pass 1632 1656 1680 (@pass_merge pass 1632 1644 1656 (pass_range pass 1632 12 (by decide +kernel)) (pass_range pass 1644 12 (by decide +kernel))) (@pass_merge pass 1656 1668 1680 (pass_range pass 1656 12 (by decide +kernel)) (pass_range pass 1668 12 (by decide +kernel)))) (@pass_merge pass 1680 1704 1728 (@pass_merge pass 1680 1692 1704 (pass_range pass 1680 12 (by decide +kernel)) (pass_range pass 1692 12 (by decide +kernel))) (@pass_merge pass 1704 1716 1728 (pass_range pass 1704 12 (by decide +kernel)) (pass_range pass 1716 12 (by decide +kernel))))))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 10000 in
private theorem block1728 : ∀ i, 1728 ≤ i → i < 1920 → pass i = true :=
  (@pass_merge pass 1728 1824 1920 (@pass_merge pass 1728 1776 1824 (@pass_merge pass 1728 1752 1776 (@pass_merge pass 1728 1740 1752 (pass_range pass 1728 12 (by decide +kernel)) (pass_range pass 1740 12 (by decide +kernel))) (@pass_merge pass 1752 1764 1776 (pass_range pass 1752 12 (by decide +kernel)) (pass_range pass 1764 12 (by decide +kernel)))) (@pass_merge pass 1776 1800 1824 (@pass_merge pass 1776 1788 1800 (pass_range pass 1776 12 (by decide +kernel)) (pass_range pass 1788 12 (by decide +kernel))) (@pass_merge pass 1800 1812 1824 (pass_range pass 1800 12 (by decide +kernel)) (pass_range pass 1812 12 (by decide +kernel))))) (@pass_merge pass 1824 1872 1920 (@pass_merge pass 1824 1848 1872 (@pass_merge pass 1824 1836 1848 (pass_range pass 1824 12 (by decide +kernel)) (pass_range pass 1836 12 (by decide +kernel))) (@pass_merge pass 1848 1860 1872 (pass_range pass 1848 12 (by decide +kernel)) (pass_range pass 1860 12 (by decide +kernel)))) (@pass_merge pass 1872 1896 1920 (@pass_merge pass 1872 1884 1896 (pass_range pass 1872 12 (by decide +kernel)) (pass_range pass 1884 12 (by decide +kernel))) (@pass_merge pass 1896 1908 1920 (pass_range pass 1896 12 (by decide +kernel)) (pass_range pass 1908 12 (by decide +kernel))))))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 10000 in
private theorem block1920 : ∀ i, 1920 ≤ i → i < 2112 → pass i = true :=
  (@pass_merge pass 1920 2016 2112 (@pass_merge pass 1920 1968 2016 (@pass_merge pass 1920 1944 1968 (@pass_merge pass 1920 1932 1944 (pass_range pass 1920 12 (by decide +kernel)) (pass_range pass 1932 12 (by decide +kernel))) (@pass_merge pass 1944 1956 1968 (pass_range pass 1944 12 (by decide +kernel)) (pass_range pass 1956 12 (by decide +kernel)))) (@pass_merge pass 1968 1992 2016 (@pass_merge pass 1968 1980 1992 (pass_range pass 1968 12 (by decide +kernel)) (pass_range pass 1980 12 (by decide +kernel))) (@pass_merge pass 1992 2004 2016 (pass_range pass 1992 12 (by decide +kernel)) (pass_range pass 2004 12 (by decide +kernel))))) (@pass_merge pass 2016 2064 2112 (@pass_merge pass 2016 2040 2064 (@pass_merge pass 2016 2028 2040 (pass_range pass 2016 12 (by decide +kernel)) (pass_range pass 2028 12 (by decide +kernel))) (@pass_merge pass 2040 2052 2064 (pass_range pass 2040 12 (by decide +kernel)) (pass_range pass 2052 12 (by decide +kernel)))) (@pass_merge pass 2064 2088 2112 (@pass_merge pass 2064 2076 2088 (pass_range pass 2064 12 (by decide +kernel)) (pass_range pass 2076 12 (by decide +kernel))) (@pass_merge pass 2088 2100 2112 (pass_range pass 2088 12 (by decide +kernel)) (pass_range pass 2100 12 (by decide +kernel))))))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 10000 in
private theorem block2112 : ∀ i, 2112 ≤ i → i < 2304 → pass i = true :=
  (@pass_merge pass 2112 2208 2304 (@pass_merge pass 2112 2160 2208 (@pass_merge pass 2112 2136 2160 (@pass_merge pass 2112 2124 2136 (pass_range pass 2112 12 (by decide +kernel)) (pass_range pass 2124 12 (by decide +kernel))) (@pass_merge pass 2136 2148 2160 (pass_range pass 2136 12 (by decide +kernel)) (pass_range pass 2148 12 (by decide +kernel)))) (@pass_merge pass 2160 2184 2208 (@pass_merge pass 2160 2172 2184 (pass_range pass 2160 12 (by decide +kernel)) (pass_range pass 2172 12 (by decide +kernel))) (@pass_merge pass 2184 2196 2208 (pass_range pass 2184 12 (by decide +kernel)) (pass_range pass 2196 12 (by decide +kernel))))) (@pass_merge pass 2208 2256 2304 (@pass_merge pass 2208 2232 2256 (@pass_merge pass 2208 2220 2232 (pass_range pass 2208 12 (by decide +kernel)) (pass_range pass 2220 12 (by decide +kernel))) (@pass_merge pass 2232 2244 2256 (pass_range pass 2232 12 (by decide +kernel)) (pass_range pass 2244 12 (by decide +kernel)))) (@pass_merge pass 2256 2280 2304 (@pass_merge pass 2256 2268 2280 (pass_range pass 2256 12 (by decide +kernel)) (pass_range pass 2268 12 (by decide +kernel))) (@pass_merge pass 2280 2292 2304 (pass_range pass 2280 12 (by decide +kernel)) (pass_range pass 2292 12 (by decide +kernel))))))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 10000 in
private theorem block2304 : ∀ i, 2304 ≤ i → i < 2496 → pass i = true :=
  (@pass_merge pass 2304 2400 2496 (@pass_merge pass 2304 2352 2400 (@pass_merge pass 2304 2328 2352 (@pass_merge pass 2304 2316 2328 (pass_range pass 2304 12 (by decide +kernel)) (pass_range pass 2316 12 (by decide +kernel))) (@pass_merge pass 2328 2340 2352 (pass_range pass 2328 12 (by decide +kernel)) (pass_range pass 2340 12 (by decide +kernel)))) (@pass_merge pass 2352 2376 2400 (@pass_merge pass 2352 2364 2376 (pass_range pass 2352 12 (by decide +kernel)) (pass_range pass 2364 12 (by decide +kernel))) (@pass_merge pass 2376 2388 2400 (pass_range pass 2376 12 (by decide +kernel)) (pass_range pass 2388 12 (by decide +kernel))))) (@pass_merge pass 2400 2448 2496 (@pass_merge pass 2400 2424 2448 (@pass_merge pass 2400 2412 2424 (pass_range pass 2400 12 (by decide +kernel)) (pass_range pass 2412 12 (by decide +kernel))) (@pass_merge pass 2424 2436 2448 (pass_range pass 2424 12 (by decide +kernel)) (pass_range pass 2436 12 (by decide +kernel)))) (@pass_merge pass 2448 2472 2496 (@pass_merge pass 2448 2460 2472 (pass_range pass 2448 12 (by decide +kernel)) (pass_range pass 2460 12 (by decide +kernel))) (@pass_merge pass 2472 2484 2496 (pass_range pass 2472 12 (by decide +kernel)) (pass_range pass 2484 12 (by decide +kernel))))))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 10000 in
private theorem block2496 : ∀ i, 2496 ≤ i → i < 2688 → pass i = true :=
  (@pass_merge pass 2496 2592 2688 (@pass_merge pass 2496 2544 2592 (@pass_merge pass 2496 2520 2544 (@pass_merge pass 2496 2508 2520 (pass_range pass 2496 12 (by decide +kernel)) (pass_range pass 2508 12 (by decide +kernel))) (@pass_merge pass 2520 2532 2544 (pass_range pass 2520 12 (by decide +kernel)) (pass_range pass 2532 12 (by decide +kernel)))) (@pass_merge pass 2544 2568 2592 (@pass_merge pass 2544 2556 2568 (pass_range pass 2544 12 (by decide +kernel)) (pass_range pass 2556 12 (by decide +kernel))) (@pass_merge pass 2568 2580 2592 (pass_range pass 2568 12 (by decide +kernel)) (pass_range pass 2580 12 (by decide +kernel))))) (@pass_merge pass 2592 2640 2688 (@pass_merge pass 2592 2616 2640 (@pass_merge pass 2592 2604 2616 (pass_range pass 2592 12 (by decide +kernel)) (pass_range pass 2604 12 (by decide +kernel))) (@pass_merge pass 2616 2628 2640 (pass_range pass 2616 12 (by decide +kernel)) (pass_range pass 2628 12 (by decide +kernel)))) (@pass_merge pass 2640 2664 2688 (@pass_merge pass 2640 2652 2664 (pass_range pass 2640 12 (by decide +kernel)) (pass_range pass 2652 12 (by decide +kernel))) (@pass_merge pass 2664 2676 2688 (pass_range pass 2664 12 (by decide +kernel)) (pass_range pass 2676 12 (by decide +kernel))))))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 10000 in
private theorem block2688 : ∀ i, 2688 ≤ i → i < 2880 → pass i = true :=
  (@pass_merge pass 2688 2784 2880 (@pass_merge pass 2688 2736 2784 (@pass_merge pass 2688 2712 2736 (@pass_merge pass 2688 2700 2712 (pass_range pass 2688 12 (by decide +kernel)) (pass_range pass 2700 12 (by decide +kernel))) (@pass_merge pass 2712 2724 2736 (pass_range pass 2712 12 (by decide +kernel)) (pass_range pass 2724 12 (by decide +kernel)))) (@pass_merge pass 2736 2760 2784 (@pass_merge pass 2736 2748 2760 (pass_range pass 2736 12 (by decide +kernel)) (pass_range pass 2748 12 (by decide +kernel))) (@pass_merge pass 2760 2772 2784 (pass_range pass 2760 12 (by decide +kernel)) (pass_range pass 2772 12 (by decide +kernel))))) (@pass_merge pass 2784 2832 2880 (@pass_merge pass 2784 2808 2832 (@pass_merge pass 2784 2796 2808 (pass_range pass 2784 12 (by decide +kernel)) (pass_range pass 2796 12 (by decide +kernel))) (@pass_merge pass 2808 2820 2832 (pass_range pass 2808 12 (by decide +kernel)) (pass_range pass 2820 12 (by decide +kernel)))) (@pass_merge pass 2832 2856 2880 (@pass_merge pass 2832 2844 2856 (pass_range pass 2832 12 (by decide +kernel)) (pass_range pass 2844 12 (by decide +kernel))) (@pass_merge pass 2856 2868 2880 (pass_range pass 2856 12 (by decide +kernel)) (pass_range pass 2868 12 (by decide +kernel))))))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 10000 in
private theorem block2880 : ∀ i, 2880 ≤ i → i < 2946 → pass i = true :=
  (@pass_merge pass 2880 2916 2946 (@pass_merge pass 2880 2892 2916 (pass_range pass 2880 12 (by decide +kernel)) (@pass_merge pass 2892 2904 2916 (pass_range pass 2892 12 (by decide +kernel)) (pass_range pass 2904 12 (by decide +kernel)))) (@pass_merge pass 2916 2928 2946 (pass_range pass 2916 12 (by decide +kernel)) (@pass_merge pass 2928 2940 2946 (pass_range pass 2928 12 (by decide +kernel)) (pass_range pass 2940 6 (by decide +kernel)))))

private theorem verified : ∀ i, 0 ≤ i → i < 2946 → pass i = true :=
  (@pass_merge pass 0 1536 2946 (@pass_merge pass 0 768 1536 (@pass_merge pass 0 384 768 (@pass_merge pass 0 192 384 block0 block192) (@pass_merge pass 384 576 768 block384 block576)) (@pass_merge pass 768 1152 1536 (@pass_merge pass 768 960 1152 block768 block960) (@pass_merge pass 1152 1344 1536 block1152 block1344))) (@pass_merge pass 1536 2304 2946 (@pass_merge pass 1536 1920 2304 (@pass_merge pass 1536 1728 1920 block1536 block1728) (@pass_merge pass 1920 2112 2304 block1920 block2112)) (@pass_merge pass 2304 2688 2946 (@pass_merge pass 2304 2496 2688 block2304 block2496) (@pass_merge pass 2688 2880 2946 block2688 block2880))))

theorem nine (col : Fin 9 → Fin 9 → Fin 9 → Bool)
    (good : ∀ a b c d, a < b → b < c → c < d →
      ((col a b c = col a b d ∧ col a b d = col a c d) ∨
       (col a b c = col a b d ∧ col a c d = col b c d) ∨
       (col a b d = col a c d ∧ col a c d = col b c d))) :
    ∃ T : Finset (Fin 9), T.card = 5 ∧ ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ d ∈ T,
      a < b → b < c → c < d → col a b c = col a b d ∧ col a c d = col b c d := by
  change witness col
  by_contra bad
  have h := steps_sound input9 learned 1638 2946 (fun i => verified i (Nat.zero_le i))
    (assn col) (input_sat col good bad) 2945 (by decide)
  have e : (learned 2945).1 = [] := by decide +kernel
  simp [e] at h
end E107Finite



theorem OMA.solution : OMA.R_Erdos107_erdos_107_R1_H1_R1.H1 := by
  intro col polygon legal
  exact E107Finite.nine col legal
