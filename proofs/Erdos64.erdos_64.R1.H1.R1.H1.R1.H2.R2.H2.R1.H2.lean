import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H2_R1

/-!
# Proof of Erdos64.erdos_64.R1.H1.R1.H1.R1.H2.R2.H2.R1.H2

We discharge hypothesis `H2` of the involution-quotient reduction
`Erdos64.erdos_64.R1.H1.R1.H1.R1.H2.R2.H2.R1`.

We prove a stronger local theorem: whenever a group `K` acts on a type `X`,
`f : K →* Multiplicative B` is a homomorphism to an abelian group `B` whose
kernel `f.ker` is abelian, and `a, b : K` satisfy `a * a ∈ f.ker`, separation
(`∀ z, a • z ≠ z ∧ b • z ≠ z ∧ a • z ≠ b • z`), and at least one non-commuting
point `y : X` (`a • (b • y) ≠ b • (a • y)`), the bi-Cayley graph `biGraph X a b`
contains a simple cycle of length 4, 8, or 16.

Proof outline:
1. Build a sound computable normalizer `normWord` for words in `a, a⁻¹, b, b⁻¹`
   modulo the metabelian relations (`f.ker` abelian and `a^2 ∈ f.ker`).
2. At any non-commuting point `y`, the universal metabelian 16-walk
   `[b⁻¹ a b, a²] = 1` (rotated to start at `y`) either yields a simple 4-, 8-,
   or 16-cycle, or forces one of three explicit stabilizer relations `A1, B1, D1`
   at `y`.
3. Applying the same lemma to two graph-isomorphic views of `biGraph X a b`
   — `(a⁻¹, a⁻¹ b)` at `a • y` and `(a⁻¹, b⁻¹)` at `(a * b) • y` — eliminates
   every combination except `(D1, D3)` via explicit 4- and 8-cycles.
4. Hence every non-commuting point satisfies `D1` and `D3`. Picking a
   non-commuting `y`:
   - If `b • y` (or symmetrically `b⁻¹ • y`) is non-commuting, then `D1, D3`
     hold at two consecutive `b`-translates, closing the dihedral 16-cycle
     `seqDih` with all collisions eliminated by 4- and 8-cycles.
   - Otherwise both `b • y` and `b⁻¹ • y` commute. The second universal
     metabelian 16-cycle `seqW3` forces `a • (b⁻¹ • y)` to commute as well,
     which closes the 16-cycle `seq1b` with all collisions eliminated.
-/

namespace MetabelianInvolutionProof

open SimpleGraph

/- ## Section 1: Words and computable metabelian normal form -/

inductive Letter : Type
  | a | ai | b | bi
  deriving DecidableEq

abbrev Word := List Letter

def letterInv : Letter → Letter
  | .a => .ai
  | .ai => .a
  | .b => .bi
  | .bi => .b

def wordInv : Word → Word
  | [] => []
  | l :: xs => wordInv xs ++ [letterInv l]

def wordConj (s w : Word) : Word := wordInv s ++ w ++ s

def substWord (wa wb : Word) : Word → Word
  | [] => []
  | .a :: xs => wa ++ substWord wa wb xs
  | .ai :: xs => wordInv wa ++ substWord wa wb xs
  | .b :: xs => wb ++ substWord wa wb xs
  | .bi :: xs => wordInv wb ++ substWord wa wb xs

def genWord : Fin 3 → Word
  | 0 => []
  | 1 => [.a]
  | 2 => [.b]

def pairWord (fi ti : Fin 3) : Word := wordInv (genWord ti) ++ genWord fi

def walkWordList : List (Fin 3 × Fin 3) → Word
  | [] => []
  | p :: ps => walkWordList ps ++ pairWord p.1 p.2

def walkFWord (seq : Fin 8 → Fin 3 × Fin 3) : Nat → Word
  | 0 => []
  | n + 1 =>
    let p := seq ⟨n % 8, Nat.mod_lt _ (by omega)⟩
    pairWord p.1 p.2 ++ walkFWord seq n

def walkTWord (seq : Fin 8 → Fin 3 × Fin 3) (i : Fin 8) : Word :=
  genWord (seq i).1 ++ walkFWord seq i.val

structure NF where
  valid : Bool
  h : Bool
  d : Int
  u : Int
  c0 : List Int
  c1 : List Int
  deriving DecidableEq

def zeros17 : List Int := List.replicate 17 0

def nfOne : NF := ⟨true, false, 0, 0, zeros17, zeros17⟩

def shiftUp (xs : List Int) : Bool × List Int :=
  (xs.getLast? == some 0, 0 :: xs.dropLast)

def shiftDown : List Int → Bool × List Int
  | [] => (false, [])
  | x :: tl => if x == 0 then (true, tl ++ [0]) else (false, x :: tl)

def addAt : Nat → Int → List Int → List Int
  | _, _, [] => []
  | 0, δ, x :: xs => (x + δ) :: xs
  | n + 1, δ, x :: xs => x :: addAt n δ xs

def stepA (m : NF) : NF :=
  if m.h then ⟨m.valid, false, m.d, m.u + 1, m.c1, m.c0⟩
  else ⟨m.valid, true, m.d, m.u, m.c1, m.c0⟩

def stepLetter (l : Letter) (m : NF) : NF :=
  match l with
  | .a => stepA m
  | .ai =>
    let m1 := stepA m
    ⟨m1.valid, m1.h, m1.d, m1.u - 1, m1.c0, m1.c1⟩
  | .b =>
    let r0 := shiftUp m.c0
    let r1 := shiftUp m.c1
    let nc0 := addAt 8 (m.u + if m.h then 1 else 0) r0.2
    let nc1 := addAt 8 m.u r1.2
    ⟨m.valid && r0.1 && r1.1, m.h, m.d + 1, m.u, nc0, nc1⟩
  | .bi =>
    let r0 := shiftDown m.c0
    let r1 := shiftDown m.c1
    let nc0 := addAt 7 (-m.u - if m.h then 1 else 0) r0.2
    let nc1 := addAt 7 (-m.u) r1.2
    ⟨m.valid && r0.1 && r1.1, m.h, m.d - 1, m.u, nc0, nc1⟩

def normWord : Word → NF
  | [] => nfOne
  | l :: xs => stepLetter l (normWord xs)

/- ## Section 2: Group evaluation and soundness of `normWord` -/

def evalLetter {K : Type*} [Group K] (a b : K) : Letter → K
  | .a => a
  | .ai => a⁻¹
  | .b => b
  | .bi => b⁻¹

def evalWord {K : Type*} [Group K] (a b : K) : Word → K
  | [] => 1
  | l :: xs => evalLetter a b l * evalWord a b xs

private lemma evalWord_append {K : Type*} [Group K] (a b : K) (w₁ w₂ : Word) :
    evalWord a b (w₁ ++ w₂) = evalWord a b w₁ * evalWord a b w₂ := by
  induction w₁ with
  | nil => simp [evalWord]
  | cons l xs ih => simp [evalWord, ih, mul_assoc]

private lemma evalLetter_inv {K : Type*} [Group K] (a b : K) (l : Letter) :
    evalLetter a b (letterInv l) = (evalLetter a b l)⁻¹ := by
  cases l <;> simp [letterInv, evalLetter]

private lemma evalWord_inv {K : Type*} [Group K] (a b : K) (w : Word) :
    evalWord a b (wordInv w) = (evalWord a b w)⁻¹ := by
  induction w with
  | nil => simp [wordInv, evalWord]
  | cons l xs ih =>
    simp [wordInv, evalWord, evalWord_append, ih, evalLetter_inv, mul_inv_rev]

private lemma evalWord_conj {K : Type*} [Group K] (a b : K) (s w : Word) :
    evalWord a b (wordConj s w) = (evalWord a b s)⁻¹ * evalWord a b w * evalWord a b s := by
  simp [wordConj, evalWord_append, evalWord_inv, mul_assoc]

private lemma evalWord_subst {K : Type*} [Group K] (a b : K) (wa wb w : Word) :
    evalWord (evalWord a b wa) (evalWord a b wb) w = evalWord a b (substWord wa wb w) := by
  induction w with
  | nil => rfl
  | cons l xs ih =>
    cases l <;> simp [substWord, evalWord, evalLetter, evalWord_append, evalWord_inv, ih]

private lemma addAt_length (n : Nat) (δ : Int) (xs : List Int) :
    (addAt n δ xs).length = xs.length := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [addAt]
  | succ n ih => cases xs <;> simp [addAt, ih]

private lemma eq_dropLast_append_zero {xs : List Int} (h : xs.getLast? = some 0) :
    xs = xs.dropLast ++ [0] := by
  cases xs with
  | nil => simp at h
  | cons x tl =>
    have hne : x :: tl ≠ [] := List.cons_ne_nil x tl
    have hlast : (x :: tl).getLast hne = 0 := by
      rw [List.getLast?_eq_some_getLast hne] at h
      exact Option.some.inj h
    rw [← hlast]
    exact (List.dropLast_append_getLast hne).symm

private lemma shiftUp_length {xs : List Int} (h : (shiftUp xs).1 = true) :
    (shiftUp xs).2.length = xs.length := by
  have hl : xs.getLast? = some 0 := by simpa [shiftUp] using h
  have heq := eq_dropLast_append_zero hl
  have hlen : xs.length = xs.dropLast.length + 1 := by
    conv_lhs => rw [heq]
    simp
  simp only [shiftUp, List.length_cons]
  omega

private lemma shiftDown_length {xs : List Int} (h : (shiftDown xs).1 = true) :
    (shiftDown xs).2.length = xs.length := by
  cases xs with
  | nil => simp [shiftDown] at h
  | cons x tl =>
    by_cases hx : x = 0
    · subst hx; simp [shiftDown]
    · have hbeq : (x == 0) = false := beq_false_of_ne hx
      simp [shiftDown, hbeq] at h

section Soundness

variable {K B : Type*} [Group K] [AddCommGroup B]

private def kerU (f : K →* Multiplicative B) (a : K) (ha2 : a * a ∈ f.ker) : f.ker :=
  ⟨a * a, ha2⟩

private lemma comm0_mem (f : K →* Multiplicative B) (a b : K) :
    b * a * b⁻¹ * a⁻¹ ∈ f.ker := by
  change f (b * a * b⁻¹ * a⁻¹) = 1
  simp [map_mul, map_inv, mul_comm]

private def kerComm0 (f : K →* Multiplicative B) (a b : K) : f.ker :=
  ⟨b * a * b⁻¹ * a⁻¹, comm0_mem f a b⟩

private lemma kerC_mem (f : K →* Multiplicative B) (a b : K) (t : Bool) (k : ℤ) :
    (if t then a else 1) * b ^ k * (kerComm0 f a b : K) * b ^ (-k) * (if t then a⁻¹ else 1) ∈ f.ker := by
  change f _ = 1
  cases t <;> simp [kerComm0, map_mul, map_inv, map_zpow, mul_comm]

private def kerC (f : K →* Multiplicative B) (a b : K) (t : Bool) (k : ℤ) : f.ker :=
  ⟨(if t then a else 1) * b ^ k * (kerComm0 f a b : K) * b ^ (-k) * (if t then a⁻¹ else 1),
    kerC_mem f a b t k⟩

private lemma ker_mul_comm (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (x y : f.ker) : (x : K) * (y : K) = (y : K) * (x : K) :=
  congrArg Subtype.val (hker x y)

private lemma conj_a_U (f : K →* Multiplicative B) (a : K) (ha2 : a * a ∈ f.ker) :
    a * (kerU f a ha2 : K) = (kerU f a ha2 : K) * a := by
  simp [kerU, mul_assoc]

private lemma conj_a_C (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (ha2 : a * a ∈ f.ker) (t : Bool) (k : ℤ) :
    a * (kerC f a b t k : K) = (kerC f a b (!t) k : K) * a := by
  cases t
  · simp [kerC, mul_assoc]
  · change a * (a * b ^ k * (kerComm0 f a b : K) * b ^ (-k) * a⁻¹) =
      (1 * b ^ k * (kerComm0 f a b : K) * b ^ (-k) * 1) * a
    have hcu := ker_mul_comm f hker (kerU f a ha2) (kerC f a b false k)
    have h1 : a * (a * b ^ k * (kerComm0 f a b : K) * b ^ (-k) * a⁻¹) =
        (kerU f a ha2 : K) * (kerC f a b false k : K) * a⁻¹ := by
      simp [kerU, kerC, mul_assoc]
    rw [h1, hcu]
    simp [kerU, kerC, mul_assoc]

private lemma conj_b_C (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (t : Bool) (k : ℤ) :
    b * (kerC f a b t k : K) = (kerC f a b t (k + 1) : K) * b := by
  cases t
  · change b * (1 * b ^ k * (kerComm0 f a b : K) * b ^ (-k) * 1) =
      (1 * b ^ (k + 1) * (kerComm0 f a b : K) * b ^ (-(k + 1)) * 1) * b
    rw [one_mul, mul_one, one_mul, mul_one, zpow_add_one, neg_add, zpow_add, zpow_neg_one]
    group
  · have hcf : b * (kerC f a b false k : K) * b⁻¹ = (kerC f a b false (k + 1) : K) := by
      change b * (1 * b ^ k * (kerComm0 f a b : K) * b ^ (-k) * 1) * b⁻¹ =
        1 * b ^ (k + 1) * (kerComm0 f a b : K) * b ^ (-(k + 1)) * 1
      rw [one_mul, mul_one, one_mul, mul_one, zpow_add_one, neg_add, zpow_add, zpow_neg_one]
      group
    have hba : b * a * b⁻¹ = (kerComm0 f a b : K) * a := by
      simp [kerComm0, mul_assoc]
    have hba_inv : b * a⁻¹ * b⁻¹ = a⁻¹ * (kerComm0 f a b : K)⁻¹ := by
      have h' : (b * a * b⁻¹)⁻¹ = ((kerComm0 f a b : K) * a)⁻¹ := congrArg Inv.inv hba
      simpa [mul_inv_rev, mul_assoc] using h'
    have hconj_eq : b * (kerC f a b true k : K) * b⁻¹ = (kerC f a b true (k + 1) : K) := by
      have hct : (kerC f a b true k : K) = a * (kerC f a b false k : K) * a⁻¹ := by
        simp [kerC, mul_assoc]
      have hct' : (kerC f a b true (k + 1) : K) = a * (kerC f a b false (k + 1) : K) * a⁻¹ := by
        simp [kerC, mul_assoc]
      rw [hct, hct']
      calc
        b * (a * (kerC f a b false k : K) * a⁻¹) * b⁻¹
            = (b * a * b⁻¹) * (b * (kerC f a b false k : K) * b⁻¹) * (b * a⁻¹ * b⁻¹) := by group
        _ = ((kerComm0 f a b : K) * a) * (kerC f a b false (k + 1) : K) *
              (a⁻¹ * (kerComm0 f a b : K)⁻¹) := by rw [hba, hcf, hba_inv]
        _ = (kerComm0 f a b : K) * (kerC f a b true (k + 1) : K) * (kerComm0 f a b : K)⁻¹ := by
              rw [hct']; group
        _ = (kerC f a b true (k + 1) : K) * (kerComm0 f a b : K) * (kerComm0 f a b : K)⁻¹ := by
              rw [ker_mul_comm f hker (kerComm0 f a b) (kerC f a b true (k + 1))]
        _ = (kerC f a b true (k + 1) : K) := by group
        _ = a * (kerC f a b false (k + 1) : K) * a⁻¹ := hct'
    calc
      b * (kerC f a b true k : K) = (b * (kerC f a b true k : K) * b⁻¹) * b := by group
      _ = (kerC f a b true (k + 1) : K) * b := by rw [hconj_eq]

private lemma conj_bi_C (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (t : Bool) (k : ℤ) :
    b⁻¹ * (kerC f a b t k : K) = (kerC f a b t (k - 1) : K) * b⁻¹ := by
  have h := conj_b_C f hker a b t (k - 1)
  rw [sub_add_cancel] at h
  calc
    b⁻¹ * (kerC f a b t k : K)
        = b⁻¹ * ((kerC f a b t k : K) * b) * b⁻¹ := by group
    _ = b⁻¹ * (b * (kerC f a b t (k - 1) : K)) * b⁻¹ := by rw [← h]
    _ = (kerC f a b t (k - 1) : K) * b⁻¹ := by group

private lemma conj_b_U (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (ha2 : a * a ∈ f.ker) :
    b * (kerU f a ha2 : K) =
      ((kerU f a ha2 * kerC f a b false 0 * kerC f a b true 0 : f.ker) : K) * b := by
  have hcomm :
      ((kerU f a ha2 * kerC f a b false 0 * kerC f a b true 0 : f.ker) : K) =
      (kerC f a b false 0 : K) * (kerC f a b true 0 : K) * (kerU f a ha2 : K) := by
    have h1 := ker_mul_comm f hker (kerU f a ha2) (kerC f a b false 0 * kerC f a b true 0)
    simpa [mul_assoc] using h1
  rw [hcomm]
  simp only [kerU, kerC, kerComm0, zpow_zero, mul_one, one_mul, Bool.false_eq_true, ↓reduceIte]
  group

private lemma conj_bi_U (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (ha2 : a * a ∈ f.ker) :
    b⁻¹ * (kerU f a ha2 : K) =
      ((kerU f a ha2 * (kerC f a b false (-1))⁻¹ * (kerC f a b true (-1))⁻¹ : f.ker) : K) * b⁻¹ := by
  have h1 := conj_b_U f hker a b ha2
  have h2 := conj_bi_C f hker a b false 0
  have h3 := conj_bi_C f hker a b true 0
  have h2' : b⁻¹ * (kerC f a b false 0 : K) * b = (kerC f a b false (-1) : K) := by
    calc b⁻¹ * (kerC f a b false 0 : K) * b
        = (kerC f a b false (0 - 1) : K) * b⁻¹ * b := by rw [h2]
      _ = (kerC f a b false (-1) : K) := by simp
  have h3' : b⁻¹ * (kerC f a b true 0 : K) * b = (kerC f a b true (-1) : K) := by
    calc b⁻¹ * (kerC f a b true 0 : K) * b
        = (kerC f a b true (0 - 1) : K) * b⁻¹ * b := by rw [h3]
      _ = (kerC f a b true (-1) : K) := by simp
  have hinv : b⁻¹ * (kerU f a ha2 : K) * b =
      ((kerU f a ha2 * (kerC f a b false (-1))⁻¹ * (kerC f a b true (-1))⁻¹ : f.ker) : K) := by
    have h4 : (kerU f a ha2 : K) =
        b⁻¹ * ((kerU f a ha2 * kerC f a b false 0 * kerC f a b true 0 : f.ker) : K) * b := by
      calc (kerU f a ha2 : K) = b⁻¹ * (b * (kerU f a ha2 : K)) := by group
        _ = b⁻¹ * (((kerU f a ha2 * kerC f a b false 0 * kerC f a b true 0 : f.ker) : K) * b) := by
            rw [h1]
        _ = _ := by group
    have h5 : (kerU f a ha2 : K) =
        (b⁻¹ * (kerU f a ha2 : K) * b) * (kerC f a b false (-1) : K) * (kerC f a b true (-1) : K) := by
      calc (kerU f a ha2 : K)
          = b⁻¹ * ((kerU f a ha2 : K) * (kerC f a b false 0 : K) * (kerC f a b true 0 : K)) * b := by
            simpa [Subgroup.coe_mul] using h4
        _ = (b⁻¹ * (kerU f a ha2 : K) * b) * (b⁻¹ * (kerC f a b false 0 : K) * b) *
            (b⁻¹ * (kerC f a b true 0 : K) * b) := by group
        _ = (b⁻¹ * (kerU f a ha2 : K) * b) * (kerC f a b false (-1) : K) * (kerC f a b true (-1) : K) := by
            rw [h2', h3']
    calc b⁻¹ * (kerU f a ha2 : K) * b
        = ((b⁻¹ * (kerU f a ha2 : K) * b) * (kerC f a b false (-1) : K) *
            (kerC f a b true (-1) : K)) * (kerC f a b true (-1) : K)⁻¹ *
            (kerC f a b false (-1) : K)⁻¹ := by group
      _ = (kerU f a ha2 : K) * (kerC f a b true (-1) : K)⁻¹ *
            (kerC f a b false (-1) : K)⁻¹ := by rw [← h5]
      _ = ((kerU f a ha2 * (kerC f a b true (-1))⁻¹ * (kerC f a b false (-1))⁻¹ : f.ker) : K) := by
            simp [Subgroup.coe_mul]
      _ = ((kerU f a ha2 * (kerC f a b false (-1))⁻¹ * (kerC f a b true (-1))⁻¹ : f.ker) : K) := by
            let _ : CommGroup f.ker := { (inferInstance : Group f.ker) with mul_comm := hker }
            congr 1; rw [mul_assoc, mul_comm (kerC f a b true (-1))⁻¹, ← mul_assoc]
  calc b⁻¹ * (kerU f a ha2 : K) = (b⁻¹ * (kerU f a ha2 : K) * b) * b⁻¹ := by group
    _ = _ := by rw [hinv]

private lemma b_mul_a (f : K →* Multiplicative B) (a b : K) :
    b * a = (kerC f a b false 0 : K) * a * b := by
  simp only [kerC, kerComm0, zpow_zero, mul_one, one_mul, Bool.false_eq_true, ↓reduceIte]
  group

private lemma bi_mul_a (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) : b⁻¹ * a = ((kerC f a b false (-1))⁻¹ : K) * a * b⁻¹ := by
  have h1 := b_mul_a f a b
  have h2 := conj_bi_C f hker a b false 0
  have hba : (kerC f a b false 0 : K)⁻¹ * b * a = a * b := by
    calc (kerC f a b false 0 : K)⁻¹ * b * a
        = (kerC f a b false 0 : K)⁻¹ * (b * a) := by group
      _ = (kerC f a b false 0 : K)⁻¹ * ((kerC f a b false 0 : K) * a * b) := by rw [h1]
      _ = a * b := by group
  have h2i : b⁻¹ * (kerC f a b false 0 : K)⁻¹ = ((kerC f a b false (-1))⁻¹ : K) * b⁻¹ := by
    have h := congrArg (fun x => (kerC f a b false (-1) : K)⁻¹ * x * (kerC f a b false 0 : K)⁻¹)
      (show b⁻¹ * (kerC f a b false 0 : K) = (kerC f a b false (-1) : K) * b⁻¹ by simpa using h2)
    have h' : (kerC f a b false (-1) : K)⁻¹ * (b⁻¹ * (kerC f a b false 0 : K)) *
        (kerC f a b false 0 : K)⁻¹ =
        (kerC f a b false (-1) : K)⁻¹ * ((kerC f a b false (-1) : K) * b⁻¹) *
        (kerC f a b false 0 : K)⁻¹ := h
    have h'' : (kerC f a b false (-1) : K)⁻¹ * b⁻¹ = b⁻¹ * (kerC f a b false 0 : K)⁻¹ := by
      simpa [mul_assoc] using h'
    exact h''.symm
  calc b⁻¹ * a = b⁻¹ * (a * b) * b⁻¹ := by group
    _ = b⁻¹ * ((kerC f a b false 0 : K)⁻¹ * b * a) * b⁻¹ := by rw [← hba]
    _ = (b⁻¹ * (kerC f a b false 0 : K)⁻¹) * b * a * b⁻¹ := by group
    _ = ((kerC f a b false (-1))⁻¹ : K) * b⁻¹ * b * a * b⁻¹ := by rw [h2i]
    _ = ((kerC f a b false (-1))⁻¹ : K) * a * b⁻¹ := by group

private lemma conj_zpow_eq {g : K} {x y : K} (h : g * x = y * g) (n : ℤ) :
    g * x ^ n = y ^ n * g := by
  have h' : MulAut.conj g x = y := by
    change g * x * g⁻¹ = y
    rw [h]; group
  have hz : MulAut.conj g (x ^ n) = y ^ n := by rw [map_zpow, h']
  change g * x ^ n * g⁻¹ = y ^ n at hz
  calc g * x ^ n = (g * x ^ n * g⁻¹) * g := by group
    _ = y ^ n * g := by rw [hz]

private def evalList (f : K →* Multiplicative B) (a b : K) (t : Bool) : ℤ → List Int → f.ker
  | _, [] => 1
  | k, e :: xs => kerC f a b t k ^ e * evalList f a b t (k + 1) xs

private lemma evalList_append_zero (f : K →* Multiplicative B) (a b : K) (t : Bool)
    (k : ℤ) (xs : List Int) :
    evalList f a b t k (xs ++ [0]) = evalList f a b t k xs := by
  induction xs generalizing k with
  | nil => simp [evalList]
  | cons x tl ih => simp [evalList, ih]

private lemma evalList_addAt (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (t : Bool) (k : ℤ) (n : Nat) (δ : Int) (xs : List Int)
    (hn : n < xs.length) :
    evalList f a b t k (addAt n δ xs) =
      kerC f a b t (k + (n : ℤ)) ^ δ * evalList f a b t k xs := by
  let _ : CommGroup f.ker := { (inferInstance : Group f.ker) with mul_comm := hker }
  induction n generalizing k xs with
  | zero =>
    cases xs with
    | nil => simp at hn
    | cons x tl =>
      simp only [addAt, evalList, Nat.cast_zero, add_zero]
      rw [zpow_add, mul_comm (kerC f a b t k ^ x), mul_assoc]
  | succ n ih =>
    cases xs with
    | nil => simp at hn
    | cons x tl =>
      simp only [addAt, evalList]
      rw [ih (k + 1) tl (by simpa using hn)]
      have hk : k + 1 + (n : ℤ) = k + ((n + 1 : Nat) : ℤ) := by push_cast; ring
      rw [hk, mul_left_comm]

private lemma conj_a_evalList (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (ha2 : a * a ∈ f.ker) (t : Bool) (k : ℤ) (xs : List Int) :
    a * (evalList f a b t k xs : K) = (evalList f a b (!t) k xs : K) * a := by
  induction xs generalizing k with
  | nil => simp [evalList]
  | cons x tl ih =>
    simp only [evalList, Subgroup.coe_mul, Subgroup.coe_zpow]
    have hc := conj_zpow_eq (conj_a_C f hker a b ha2 t k) x
    calc a * ((kerC f a b t k : K) ^ x * (evalList f a b t (k + 1) tl : K))
        = (a * (kerC f a b t k : K) ^ x) * (evalList f a b t (k + 1) tl : K) := by group
      _ = ((kerC f a b (!t) k : K) ^ x * a) * (evalList f a b t (k + 1) tl : K) := by rw [hc]
      _ = (kerC f a b (!t) k : K) ^ x * (a * (evalList f a b t (k + 1) tl : K)) := by group
      _ = (kerC f a b (!t) k : K) ^ x * ((evalList f a b (!t) (k + 1) tl : K) * a) := by rw [ih]
      _ = ((kerC f a b (!t) k : K) ^ x * (evalList f a b (!t) (k + 1) tl : K)) * a := by group

private lemma conj_b_evalList (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (t : Bool) (k : ℤ) (xs : List Int) :
    b * (evalList f a b t k xs : K) = (evalList f a b t (k + 1) xs : K) * b := by
  induction xs generalizing k with
  | nil => simp [evalList]
  | cons x tl ih =>
    simp only [evalList, Subgroup.coe_mul, Subgroup.coe_zpow]
    have hc := conj_zpow_eq (conj_b_C f hker a b t k) x
    calc b * ((kerC f a b t k : K) ^ x * (evalList f a b t (k + 1) tl : K))
        = (b * (kerC f a b t k : K) ^ x) * (evalList f a b t (k + 1) tl : K) := by group
      _ = ((kerC f a b t (k + 1) : K) ^ x * b) * (evalList f a b t (k + 1) tl : K) := by rw [hc]
      _ = (kerC f a b t (k + 1) : K) ^ x * (b * (evalList f a b t (k + 1) tl : K)) := by group
      _ = (kerC f a b t (k + 1) : K) ^ x * ((evalList f a b t (k + 1 + 1) tl : K) * b) := by rw [ih]
      _ = ((kerC f a b t (k + 1) : K) ^ x * (evalList f a b t (k + 1 + 1) tl : K)) * b := by group

private lemma conj_bi_evalList (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (t : Bool) (k : ℤ) (xs : List Int) :
    b⁻¹ * (evalList f a b t k xs : K) = (evalList f a b t (k - 1) xs : K) * b⁻¹ := by
  induction xs generalizing k with
  | nil => simp [evalList]
  | cons x tl ih =>
    simp only [evalList, Subgroup.coe_mul, Subgroup.coe_zpow]
    have hc := conj_zpow_eq (conj_bi_C f hker a b t k) x
    have hk : k + 1 - 1 = k - 1 + 1 := by ring
    calc b⁻¹ * ((kerC f a b t k : K) ^ x * (evalList f a b t (k + 1) tl : K))
        = (b⁻¹ * (kerC f a b t k : K) ^ x) * (evalList f a b t (k + 1) tl : K) := by group
      _ = ((kerC f a b t (k - 1) : K) ^ x * b⁻¹) * (evalList f a b t (k + 1) tl : K) := by rw [hc]
      _ = (kerC f a b t (k - 1) : K) ^ x * (b⁻¹ * (evalList f a b t (k + 1) tl : K)) := by group
      _ = (kerC f a b t (k - 1) : K) ^ x * ((evalList f a b t (k + 1 - 1) tl : K) * b⁻¹) := by rw [ih]
      _ = ((kerC f a b t (k - 1) : K) ^ x * (evalList f a b t (k - 1 + 1) tl : K)) * b⁻¹ := by
          rw [hk]; group

private lemma evalList_shiftUp (f : K →* Multiplicative B) (a b : K) (t : Bool) (k : ℤ)
    {xs : List Int} (h : (shiftUp xs).1 = true) :
    evalList f a b t k (shiftUp xs).2 = evalList f a b t (k + 1) xs := by
  have hl : xs.getLast? = some 0 := by simpa [shiftUp] using h
  have heq := eq_dropLast_append_zero hl
  simp only [shiftUp, evalList, zpow_zero, one_mul]
  conv_rhs => rw [heq]
  rw [evalList_append_zero]

private lemma evalList_shiftDown (f : K →* Multiplicative B) (a b : K) (t : Bool) (k : ℤ)
    {xs : List Int} (h : (shiftDown xs).1 = true) :
    evalList f a b t k (shiftDown xs).2 = evalList f a b t (k - 1) xs := by
  cases xs with
  | nil => simp [shiftDown] at h
  | cons x tl =>
    by_cases hx : x = 0
    · subst hx
      simp only [shiftDown, beq_self_eq_true, ↓reduceIte, evalList, zpow_zero, one_mul]
      rw [evalList_append_zero]
      have hk : k - 1 + 1 = k := by ring
      rw [hk]
    · have hbeq : (x == 0) = false := beq_false_of_ne hx
      simp [shiftDown, hbeq] at h

private def evalNF (f : K →* Multiplicative B) (a b : K) (ha2 : a * a ∈ f.ker) (m : NF) : K :=
  ((evalList f a b false (-8) m.c0 * evalList f a b true (-8) m.c1 *
      kerU f a ha2 ^ m.u : f.ker) : K) *
    (if m.h then a else 1) * b ^ m.d

private lemma evalNF_stepA (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (ha2 : a * a ∈ f.ker) (m : NF) :
    evalNF f a b ha2 (stepA m) = a * evalNF f a b ha2 m := by
  let _ : CommGroup f.ker := { (inferInstance : Group f.ker) with mul_comm := hker }
  have hc0 := conj_a_evalList f hker a b ha2 false (-8) m.c0
  have hc1 := conj_a_evalList f hker a b ha2 true (-8) m.c1
  have hu := conj_zpow_eq (conj_a_U f a ha2) m.u
  have hmove :
      a * ((evalList f a b false (-8) m.c0 * evalList f a b true (-8) m.c1 *
        kerU f a ha2 ^ m.u : f.ker) : K) =
      ((evalList f a b false (-8) m.c1 * evalList f a b true (-8) m.c0 *
        kerU f a ha2 ^ m.u : f.ker) : K) * a := by
    simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
    calc a * ((evalList f a b false (-8) m.c0 : K) * (evalList f a b true (-8) m.c1 : K) *
            (kerU f a ha2 : K) ^ m.u)
        = (a * (evalList f a b false (-8) m.c0 : K)) * (evalList f a b true (-8) m.c1 : K) *
            (kerU f a ha2 : K) ^ m.u := by group
      _ = ((evalList f a b true (-8) m.c0 : K) * a) * (evalList f a b true (-8) m.c1 : K) *
            (kerU f a ha2 : K) ^ m.u := by
            rw [show a * (evalList f a b false (-8) m.c0 : K) =
                (evalList f a b true (-8) m.c0 : K) * a by simpa using hc0]
      _ = (evalList f a b true (-8) m.c0 : K) * (a * (evalList f a b true (-8) m.c1 : K)) *
            (kerU f a ha2 : K) ^ m.u := by group
      _ = (evalList f a b true (-8) m.c0 : K) * ((evalList f a b false (-8) m.c1 : K) * a) *
            (kerU f a ha2 : K) ^ m.u := by
            rw [show a * (evalList f a b true (-8) m.c1 : K) =
                (evalList f a b false (-8) m.c1 : K) * a by simpa using hc1]
      _ = (evalList f a b true (-8) m.c0 : K) * (evalList f a b false (-8) m.c1 : K) *
            (a * (kerU f a ha2 : K) ^ m.u) := by group
      _ = (evalList f a b true (-8) m.c0 : K) * (evalList f a b false (-8) m.c1 : K) *
            ((kerU f a ha2 : K) ^ m.u * a) := by rw [hu]
      _ = ((evalList f a b true (-8) m.c0 : K) * (evalList f a b false (-8) m.c1 : K)) *
            (kerU f a ha2 : K) ^ m.u * a := by group
      _ = ((evalList f a b false (-8) m.c1 : K) * (evalList f a b true (-8) m.c0 : K)) *
            (kerU f a ha2 : K) ^ m.u * a := by
            rw [ker_mul_comm f hker (evalList f a b true (-8) m.c0) (evalList f a b false (-8) m.c1)]
  cases mh : m.h
  · simp only [stepA, mh, Bool.false_eq_true, ↓reduceIte, evalNF]
    calc ((evalList f a b false (-8) m.c1 * evalList f a b true (-8) m.c0 *
            kerU f a ha2 ^ m.u : f.ker) : K) * a * b ^ m.d
        = a * ((evalList f a b false (-8) m.c0 * evalList f a b true (-8) m.c1 *
            kerU f a ha2 ^ m.u : f.ker) : K) * b ^ m.d := by rw [hmove]
      _ = a * (((evalList f a b false (-8) m.c0 * evalList f a b true (-8) m.c1 *
            kerU f a ha2 ^ m.u : f.ker) : K) * 1 * b ^ m.d) := by group
  · simp only [stepA, mh, ↓reduceIte, Bool.false_eq_true, evalNF]
    have haa : a * a = (kerU f a ha2 : K) := rfl
    calc ((evalList f a b false (-8) m.c1 * evalList f a b true (-8) m.c0 *
            kerU f a ha2 ^ (m.u + 1) : f.ker) : K) * 1 * b ^ m.d
        = ((evalList f a b false (-8) m.c1 * evalList f a b true (-8) m.c0 *
            kerU f a ha2 ^ m.u : f.ker) : K) * (kerU f a ha2 : K) * b ^ m.d := by
            simp [zpow_add, Subgroup.coe_mul, mul_assoc]
      _ = ((evalList f a b false (-8) m.c1 * evalList f a b true (-8) m.c0 *
            kerU f a ha2 ^ m.u : f.ker) : K) * a * a * b ^ m.d := by rw [← haa]; group
      _ = (a * ((evalList f a b false (-8) m.c0 * evalList f a b true (-8) m.c1 *
            kerU f a ha2 ^ m.u : f.ker) : K)) * a * b ^ m.d := by rw [hmove]
      _ = a * (((evalList f a b false (-8) m.c0 * evalList f a b true (-8) m.c1 *
            kerU f a ha2 ^ m.u : f.ker) : K) * a * b ^ m.d) := by group

private lemma evalNF_step_ai (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (ha2 : a * a ∈ f.ker) (m : NF) :
    evalNF f a b ha2 (stepLetter .ai m) = a⁻¹ * evalNF f a b ha2 m := by
  let _ : CommGroup f.ker := { (inferInstance : Group f.ker) with mul_comm := hker }
  have ha := evalNF_stepA f hker a b ha2 m
  have hai : a⁻¹ = (kerU f a ha2 : K)⁻¹ * a := by
    change a⁻¹ = (a * a)⁻¹ * a
    group
  have hstep : evalNF f a b ha2 (stepLetter .ai m) =
      (kerU f a ha2 : K)⁻¹ * evalNF f a b ha2 (stepA m) := by
    simp only [stepLetter, evalNF]
    let m1 := stepA m
    have hker_eq :
        ((evalList f a b false (-8) m1.c0 * evalList f a b true (-8) m1.c1 *
          kerU f a ha2 ^ (m1.u - 1) : f.ker) : K) =
        (kerU f a ha2 : K)⁻¹ *
        ((evalList f a b false (-8) m1.c0 * evalList f a b true (-8) m1.c1 *
          kerU f a ha2 ^ m1.u : f.ker) : K) := by
      have hsub : kerU f a ha2 ^ (m1.u - 1) = (kerU f a ha2)⁻¹ * kerU f a ha2 ^ m1.u := by
        rw [sub_eq_add_neg, zpow_add, zpow_neg_one, mul_comm]
      have hEq :
          evalList f a b false (-8) m1.c0 * evalList f a b true (-8) m1.c1 *
            kerU f a ha2 ^ (m1.u - 1) =
          (kerU f a ha2)⁻¹ *
          (evalList f a b false (-8) m1.c0 * evalList f a b true (-8) m1.c1 *
            kerU f a ha2 ^ m1.u) := by
        rw [hsub]; ac_rfl
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val hEq
    change ((evalList f a b false (-8) m1.c0 * evalList f a b true (-8) m1.c1 *
        kerU f a ha2 ^ (m1.u - 1) : f.ker) : K) * (if m1.h then a else 1) * b ^ m1.d =
      (kerU f a ha2 : K)⁻¹ * (((evalList f a b false (-8) m1.c0 * evalList f a b true (-8) m1.c1 *
        kerU f a ha2 ^ m1.u : f.ker) : K) * (if m1.h then a else 1) * b ^ m1.d)
    rw [hker_eq]; group
  rw [hstep, ha, hai]; group

private lemma evalNF_step_b (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (ha2 : a * a ∈ f.ker)
    (m : NF) (hl0 : m.c0.length = 17) (hl1 : m.c1.length = 17)
    (hv : (stepLetter .b m).valid = true) :
    evalNF f a b ha2 (stepLetter .b m) = b * evalNF f a b ha2 m ∧
    (stepLetter .b m).c0.length = 17 ∧ (stepLetter .b m).c1.length = 17 := by
  have _ : Std.Commutative (α := f.ker) (· * ·) := ⟨hker⟩
  simp only [stepLetter, Bool.and_eq_true] at hv
  obtain ⟨⟨_, hu0⟩, hu1⟩ := hv
  have hlen0 : (shiftUp m.c0).2.length = 17 := (shiftUp_length hu0).trans hl0
  have hlen1 : (shiftUp m.c1).2.length = 17 := (shiftUp_length hu1).trans hl1
  refine ⟨?_, ?_, ?_⟩
  · simp only [stepLetter, evalNF]
    rw [evalList_addAt f hker a b false (-8) 8 _ _ (by omega)]
    rw [evalList_addAt f hker a b true (-8) 8 _ _ (by omega)]
    rw [evalList_shiftUp f a b false (-8) hu0, evalList_shiftUp f a b true (-8) hu1]
    have hidx : (-8 : ℤ) + (8 : Nat) = 0 := by norm_num
    rw [hidx]
    have hc0 := conj_b_evalList f hker a b false (-8) m.c0
    have hc1 := conj_b_evalList f hker a b true (-8) m.c1
    have hu := conj_zpow_eq (conj_b_U f hker a b ha2) m.u
    have hbu_eq :
        ((kerU f a ha2 * kerC f a b false 0 * kerC f a b true 0 : f.ker) : K) ^ m.u =
        ((kerU f a ha2 ^ m.u * kerC f a b false 0 ^ m.u * kerC f a b true 0 ^ m.u : f.ker) : K) := by
      let _ : CommGroup f.ker := { (inferInstance : Group f.ker) with mul_comm := hker }
      rw [← Subgroup.coe_zpow, mul_zpow, mul_zpow]
    rw [hbu_eq] at hu
    have hbd : b * b ^ m.d = b ^ (m.d + 1) := by
      rw [add_comm m.d 1, zpow_add, zpow_one]
    have hmove :
        b * ((evalList f a b false (-8) m.c0 * evalList f a b true (-8) m.c1 *
          kerU f a ha2 ^ m.u : f.ker) : K) =
        ((evalList f a b false (-8 + 1) m.c0 * evalList f a b true (-8 + 1) m.c1 *
          (kerU f a ha2 ^ m.u * kerC f a b false 0 ^ m.u * kerC f a b true 0 ^ m.u) : f.ker) : K) * b := by
      simp only [Subgroup.coe_mul, Subgroup.coe_zpow] at hu ⊢
      calc b * ((evalList f a b false (-8) m.c0 : K) * (evalList f a b true (-8) m.c1 : K) *
              (kerU f a ha2 : K) ^ m.u)
          = (b * (evalList f a b false (-8) m.c0 : K)) * (evalList f a b true (-8) m.c1 : K) *
              (kerU f a ha2 : K) ^ m.u := by group
        _ = ((evalList f a b false (-8 + 1) m.c0 : K) * b) * (evalList f a b true (-8) m.c1 : K) *
              (kerU f a ha2 : K) ^ m.u := by rw [hc0]
        _ = (evalList f a b false (-8 + 1) m.c0 : K) * (b * (evalList f a b true (-8) m.c1 : K)) *
              (kerU f a ha2 : K) ^ m.u := by group
        _ = (evalList f a b false (-8 + 1) m.c0 : K) * ((evalList f a b true (-8 + 1) m.c1 : K) * b) *
              (kerU f a ha2 : K) ^ m.u := by rw [hc1]
        _ = (evalList f a b false (-8 + 1) m.c0 : K) * (evalList f a b true (-8 + 1) m.c1 : K) *
              (b * (kerU f a ha2 : K) ^ m.u) := by group
        _ = (evalList f a b false (-8 + 1) m.c0 : K) * (evalList f a b true (-8 + 1) m.c1 : K) *
              (((kerU f a ha2 : K) ^ m.u * (kerC f a b false 0 : K) ^ m.u *
                (kerC f a b true 0 : K) ^ m.u) * b) := by rw [hu]
        _ = _ := by group
    by_cases mh : m.h = true
    · simp only [mh, ↓reduceIte]
      have hrearr : ∀ p q r s t u : f.ker,
          p * q * r * (s * t) * u = r * t * (u * p * s) * q := by
        intro p q r s t u; ac_rfl
      have hker_eq :
          kerC f a b false 0 ^ (m.u + 1) * evalList f a b false (-8 + 1) m.c0 *
            (kerC f a b true 0 ^ m.u * evalList f a b true (-8 + 1) m.c1) * kerU f a ha2 ^ m.u =
          evalList f a b false (-8 + 1) m.c0 * evalList f a b true (-8 + 1) m.c1 *
            (kerU f a ha2 ^ m.u * kerC f a b false 0 ^ m.u * kerC f a b true 0 ^ m.u) *
            kerC f a b false 0 := by
        rw [zpow_add_one]
        exact hrearr _ _ _ _ _ _
      rw [hker_eq, ← hbd]
      have hba := b_mul_a f a b
      calc ((evalList f a b false (-8 + 1) m.c0 * evalList f a b true (-8 + 1) m.c1 *
              (kerU f a ha2 ^ m.u * kerC f a b false 0 ^ m.u * kerC f a b true 0 ^ m.u) *
              kerC f a b false 0 : f.ker) : K) * a * (b * b ^ m.d)
          = ((evalList f a b false (-8 + 1) m.c0 * evalList f a b true (-8 + 1) m.c1 *
              (kerU f a ha2 ^ m.u * kerC f a b false 0 ^ m.u *
                kerC f a b true 0 ^ m.u) : f.ker) : K) *
              ((kerC f a b false 0 : K) * a * b) * b ^ m.d := by
              simp only [Subgroup.coe_mul]; group
        _ = ((evalList f a b false (-8 + 1) m.c0 * evalList f a b true (-8 + 1) m.c1 *
              (kerU f a ha2 ^ m.u * kerC f a b false 0 ^ m.u *
                kerC f a b true 0 ^ m.u) : f.ker) : K) * (b * a) * b ^ m.d := by rw [← hba]
        _ = (((evalList f a b false (-8 + 1) m.c0 * evalList f a b true (-8 + 1) m.c1 *
              (kerU f a ha2 ^ m.u * kerC f a b false 0 ^ m.u *
                kerC f a b true 0 ^ m.u) : f.ker) : K) * b) * a * b ^ m.d := by group
        _ = (b * ((evalList f a b false (-8) m.c0 * evalList f a b true (-8) m.c1 *
              kerU f a ha2 ^ m.u : f.ker) : K)) * a * b ^ m.d := by rw [← hmove]
        _ = b * (((evalList f a b false (-8) m.c0 * evalList f a b true (-8) m.c1 *
              kerU f a ha2 ^ m.u : f.ker) : K) * a * b ^ m.d) := by group
    · have mh' : m.h = false := Bool.eq_false_iff.mpr mh
      simp only [mh', Bool.false_eq_true, ↓reduceIte, add_zero]
      have hker_eq :
          kerC f a b false 0 ^ m.u * evalList f a b false (-8 + 1) m.c0 *
            (kerC f a b true 0 ^ m.u * evalList f a b true (-8 + 1) m.c1) * kerU f a ha2 ^ m.u =
          evalList f a b false (-8 + 1) m.c0 * evalList f a b true (-8 + 1) m.c1 *
            (kerU f a ha2 ^ m.u * kerC f a b false 0 ^ m.u * kerC f a b true 0 ^ m.u) := by ac_rfl
      rw [hker_eq, ← hbd]
      calc ((evalList f a b false (-8 + 1) m.c0 * evalList f a b true (-8 + 1) m.c1 *
              (kerU f a ha2 ^ m.u * kerC f a b false 0 ^ m.u *
                kerC f a b true 0 ^ m.u) : f.ker) : K) * 1 * (b * b ^ m.d)
          = (((evalList f a b false (-8 + 1) m.c0 * evalList f a b true (-8 + 1) m.c1 *
              (kerU f a ha2 ^ m.u * kerC f a b false 0 ^ m.u *
                kerC f a b true 0 ^ m.u) : f.ker) : K) * b) * b ^ m.d := by group
        _ = (b * ((evalList f a b false (-8) m.c0 * evalList f a b true (-8) m.c1 *
              kerU f a ha2 ^ m.u : f.ker) : K)) * b ^ m.d := by rw [← hmove]
        _ = b * (((evalList f a b false (-8) m.c0 * evalList f a b true (-8) m.c1 *
              kerU f a ha2 ^ m.u : f.ker) : K) * 1 * b ^ m.d) := by group
  · simp [stepLetter, addAt_length, hlen0]
  · simp [stepLetter, addAt_length, hlen1]

private lemma evalNF_step_bi (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (ha2 : a * a ∈ f.ker)
    (m : NF) (hl0 : m.c0.length = 17) (hl1 : m.c1.length = 17)
    (hv : (stepLetter .bi m).valid = true) :
    evalNF f a b ha2 (stepLetter .bi m) = b⁻¹ * evalNF f a b ha2 m ∧
    (stepLetter .bi m).c0.length = 17 ∧ (stepLetter .bi m).c1.length = 17 := by
  have _ : Std.Commutative (α := f.ker) (· * ·) := ⟨hker⟩
  simp only [stepLetter, Bool.and_eq_true] at hv
  obtain ⟨⟨_, hd0⟩, hd1⟩ := hv
  have hlen0 : (shiftDown m.c0).2.length = 17 := (shiftDown_length hd0).trans hl0
  have hlen1 : (shiftDown m.c1).2.length = 17 := (shiftDown_length hd1).trans hl1
  refine ⟨?_, ?_, ?_⟩
  · simp only [stepLetter, evalNF]
    rw [evalList_addAt f hker a b false (-8) 7 _ _ (by omega)]
    rw [evalList_addAt f hker a b true (-8) 7 _ _ (by omega)]
    rw [evalList_shiftDown f a b false (-8) hd0, evalList_shiftDown f a b true (-8) hd1]
    have hidx : (-8 : ℤ) + (7 : Nat) = -1 := by norm_num
    rw [hidx]
    have hc0 := conj_bi_evalList f hker a b false (-8) m.c0
    have hc1 := conj_bi_evalList f hker a b true (-8) m.c1
    have hu := conj_zpow_eq (conj_bi_U f hker a b ha2) m.u
    have hbu_eq :
        ((kerU f a ha2 * (kerC f a b false (-1))⁻¹ * (kerC f a b true (-1))⁻¹ : f.ker) : K) ^ m.u =
        ((kerU f a ha2 ^ m.u * kerC f a b false (-1) ^ (-m.u) *
          kerC f a b true (-1) ^ (-m.u) : f.ker) : K) := by
      let _ : CommGroup f.ker := { (inferInstance : Group f.ker) with mul_comm := hker }
      rw [← Subgroup.coe_zpow, mul_zpow, mul_zpow, inv_zpow, inv_zpow, zpow_neg, zpow_neg]
    rw [hbu_eq] at hu
    have hbd : b⁻¹ * b ^ m.d = b ^ (m.d - 1) := by
      rw [sub_eq_neg_add, zpow_add, zpow_neg_one]
    have hmove :
        b⁻¹ * ((evalList f a b false (-8) m.c0 * evalList f a b true (-8) m.c1 *
          kerU f a ha2 ^ m.u : f.ker) : K) =
        ((evalList f a b false (-8 - 1) m.c0 * evalList f a b true (-8 - 1) m.c1 *
          (kerU f a ha2 ^ m.u * kerC f a b false (-1) ^ (-m.u) *
            kerC f a b true (-1) ^ (-m.u)) : f.ker) : K) * b⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_zpow] at hu ⊢
      calc b⁻¹ * ((evalList f a b false (-8) m.c0 : K) * (evalList f a b true (-8) m.c1 : K) *
              (kerU f a ha2 : K) ^ m.u)
          = (b⁻¹ * (evalList f a b false (-8) m.c0 : K)) * (evalList f a b true (-8) m.c1 : K) *
              (kerU f a ha2 : K) ^ m.u := by group
        _ = ((evalList f a b false (-8 - 1) m.c0 : K) * b⁻¹) * (evalList f a b true (-8) m.c1 : K) *
              (kerU f a ha2 : K) ^ m.u := by rw [hc0]
        _ = (evalList f a b false (-8 - 1) m.c0 : K) * (b⁻¹ * (evalList f a b true (-8) m.c1 : K)) *
              (kerU f a ha2 : K) ^ m.u := by group
        _ = (evalList f a b false (-8 - 1) m.c0 : K) * ((evalList f a b true (-8 - 1) m.c1 : K) * b⁻¹) *
              (kerU f a ha2 : K) ^ m.u := by rw [hc1]
        _ = (evalList f a b false (-8 - 1) m.c0 : K) * (evalList f a b true (-8 - 1) m.c1 : K) *
              (b⁻¹ * (kerU f a ha2 : K) ^ m.u) := by group
        _ = (evalList f a b false (-8 - 1) m.c0 : K) * (evalList f a b true (-8 - 1) m.c1 : K) *
              (((kerU f a ha2 : K) ^ m.u * (kerC f a b false (-1) : K) ^ (-m.u) *
                (kerC f a b true (-1) : K) ^ (-m.u)) * b⁻¹) := by rw [hu]
        _ = _ := by group
    by_cases mh : m.h = true
    · simp only [mh, ↓reduceIte]
      have hrearr : ∀ p q r s t u : f.ker,
          p * q * r * (s * t) * u = r * t * (u * p * s) * q := by
        intro p q r s t u; ac_rfl
      have hker_eq :
          kerC f a b false (-1) ^ (-m.u - 1) * evalList f a b false (-8 - 1) m.c0 *
            (kerC f a b true (-1) ^ (-m.u) * evalList f a b true (-8 - 1) m.c1) * kerU f a ha2 ^ m.u =
          evalList f a b false (-8 - 1) m.c0 * evalList f a b true (-8 - 1) m.c1 *
            (kerU f a ha2 ^ m.u * kerC f a b false (-1) ^ (-m.u) * kerC f a b true (-1) ^ (-m.u)) *
            (kerC f a b false (-1))⁻¹ := by
        rw [sub_eq_add_neg, zpow_add, zpow_neg_one]
        exact hrearr _ _ _ _ _ _
      rw [hker_eq, ← hbd]
      have hba := bi_mul_a f hker a b
      calc ((evalList f a b false (-8 - 1) m.c0 * evalList f a b true (-8 - 1) m.c1 *
              (kerU f a ha2 ^ m.u * kerC f a b false (-1) ^ (-m.u) *
                kerC f a b true (-1) ^ (-m.u)) *
              (kerC f a b false (-1))⁻¹ : f.ker) : K) * a * (b⁻¹ * b ^ m.d)
          = ((evalList f a b false (-8 - 1) m.c0 * evalList f a b true (-8 - 1) m.c1 *
              (kerU f a ha2 ^ m.u * kerC f a b false (-1) ^ (-m.u) *
                kerC f a b true (-1) ^ (-m.u)) : f.ker) : K) *
              (((kerC f a b false (-1))⁻¹ : K) * a * b⁻¹) * b ^ m.d := by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        _ = ((evalList f a b false (-8 - 1) m.c0 * evalList f a b true (-8 - 1) m.c1 *
              (kerU f a ha2 ^ m.u * kerC f a b false (-1) ^ (-m.u) *
                kerC f a b true (-1) ^ (-m.u)) : f.ker) : K) * (b⁻¹ * a) * b ^ m.d := by
              rw [← hba]
        _ = (((evalList f a b false (-8 - 1) m.c0 * evalList f a b true (-8 - 1) m.c1 *
              (kerU f a ha2 ^ m.u * kerC f a b false (-1) ^ (-m.u) *
                kerC f a b true (-1) ^ (-m.u)) : f.ker) : K) * b⁻¹) * a * b ^ m.d := by group
        _ = (b⁻¹ * ((evalList f a b false (-8) m.c0 * evalList f a b true (-8) m.c1 *
              kerU f a ha2 ^ m.u : f.ker) : K)) * a * b ^ m.d := by rw [← hmove]
        _ = b⁻¹ * (((evalList f a b false (-8) m.c0 * evalList f a b true (-8) m.c1 *
              kerU f a ha2 ^ m.u : f.ker) : K) * a * b ^ m.d) := by group
    · have mh' : m.h = false := Bool.eq_false_iff.mpr mh
      simp only [mh', Bool.false_eq_true, ↓reduceIte, sub_zero]
      have hker_eq :
          kerC f a b false (-1) ^ (-m.u) * evalList f a b false (-8 - 1) m.c0 *
            (kerC f a b true (-1) ^ (-m.u) * evalList f a b true (-8 - 1) m.c1) * kerU f a ha2 ^ m.u =
          evalList f a b false (-8 - 1) m.c0 * evalList f a b true (-8 - 1) m.c1 *
            (kerU f a ha2 ^ m.u * kerC f a b false (-1) ^ (-m.u) * kerC f a b true (-1) ^ (-m.u)) := by
        ac_rfl
      rw [hker_eq, ← hbd]
      calc ((evalList f a b false (-8 - 1) m.c0 * evalList f a b true (-8 - 1) m.c1 *
              (kerU f a ha2 ^ m.u * kerC f a b false (-1) ^ (-m.u) *
                kerC f a b true (-1) ^ (-m.u)) : f.ker) : K) * 1 * (b⁻¹ * b ^ m.d)
          = (((evalList f a b false (-8 - 1) m.c0 * evalList f a b true (-8 - 1) m.c1 *
              (kerU f a ha2 ^ m.u * kerC f a b false (-1) ^ (-m.u) *
                kerC f a b true (-1) ^ (-m.u)) : f.ker) : K) * b⁻¹) * b ^ m.d := by group
        _ = (b⁻¹ * ((evalList f a b false (-8) m.c0 * evalList f a b true (-8) m.c1 *
              kerU f a ha2 ^ m.u : f.ker) : K)) * b ^ m.d := by rw [← hmove]
        _ = b⁻¹ * (((evalList f a b false (-8) m.c0 * evalList f a b true (-8) m.c1 *
              kerU f a ha2 ^ m.u : f.ker) : K) * 1 * b ^ m.d) := by group
  · simp [stepLetter, addAt_length, hlen0]
  · simp [stepLetter, addAt_length, hlen1]

private lemma stepLetter_valid_mono (l : Letter) (m : NF)
    (hv : (stepLetter l m).valid = true) : m.valid = true := by
  cases l with
  | a => cases mh : m.h <;> simp [stepLetter, stepA, mh] at hv <;> exact hv
  | ai => cases mh : m.h <;> simp [stepLetter, stepA, mh] at hv <;> exact hv
  | b => simp only [stepLetter, Bool.and_eq_true] at hv; exact hv.1.1
  | bi => simp only [stepLetter, Bool.and_eq_true] at hv; exact hv.1.1

private lemma evalNF_normWord_aux (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (ha2 : a * a ∈ f.ker) (w : Word) (hv : (normWord w).valid = true) :
    evalNF f a b ha2 (normWord w) = evalWord a b w ∧
    (normWord w).c0.length = 17 ∧ (normWord w).c1.length = 17 := by
  induction w with
  | nil =>
    refine ⟨?_, ?_, ?_⟩
    · simp [normWord, nfOne, evalNF, evalWord, zeros17, evalList]
    · simp [normWord, nfOne, zeros17]
    · simp [normWord, nfOne, zeros17]
  | cons l xs ih =>
    have hv' : (normWord xs).valid = true := stepLetter_valid_mono l (normWord xs) hv
    obtain ⟨heq, hl0, hl1⟩ := ih hv'
    cases l with
    | a =>
      refine ⟨?_, ?_, ?_⟩
      · rw [normWord, stepLetter, evalNF_stepA f hker a b ha2, heq]; rfl
      · cases mh : (normWord xs).h <;> simp [normWord, stepLetter, stepA, mh, hl1]
      · cases mh : (normWord xs).h <;> simp [normWord, stepLetter, stepA, mh, hl0]
    | ai =>
      refine ⟨?_, ?_, ?_⟩
      · rw [normWord, evalNF_step_ai f hker a b ha2, heq]; rfl
      · cases mh : (normWord xs).h <;> simp [normWord, stepLetter, stepA, mh, hl1]
      · cases mh : (normWord xs).h <;> simp [normWord, stepLetter, stepA, mh, hl0]
    | b =>
      obtain ⟨he, l0, l1⟩ := evalNF_step_b f hker a b ha2 (normWord xs) hl0 hl1 hv
      exact ⟨by rw [normWord, he, heq]; rfl, l0, l1⟩
    | bi =>
      obtain ⟨he, l0, l1⟩ := evalNF_step_bi f hker a b ha2 (normWord xs) hl0 hl1 hv
      exact ⟨by rw [normWord, he, heq]; rfl, l0, l1⟩

private lemma evalWord_eq_of_norm (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (ha2 : a * a ∈ f.ker) {w₁ w₂ : Word}
    (hv : (normWord w₁).valid = true) (h : normWord w₁ = normWord w₂) :
    evalWord a b w₁ = evalWord a b w₂ := by
  have hv₂ : (normWord w₂).valid = true := h ▸ hv
  have h1 := (evalNF_normWord_aux f hker a b ha2 w₁ hv).1
  have h2 := (evalNF_normWord_aux f hker a b ha2 w₂ hv₂).1
  rw [← h1, ← h2, h]

end Soundness

/- ## Section 3: Bi-Cayley graph and cycle extraction -/

def biGraph {K : Type*} (X : Type*) [Group K] [MulAction K X] (a b : K) :
    SimpleGraph (Bool × X) :=
  SimpleGraph.fromRel (fun u v : Bool × X =>
    u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = a • u.2 ∨ v.2 = b • u.2))

def genOf {K : Type*} [Group K] (a b : K) : Fin 3 → K
  | 0 => 1
  | 1 => a
  | 2 => b

private lemma evalWord_genWord {K : Type*} [Group K] (a b : K) (i : Fin 3) :
    evalWord a b (genWord i) = genOf a b i := by
  fin_cases i <;> simp [genWord, evalWord, evalLetter, genOf]

private lemma evalWord_pairWord {K : Type*} [Group K] (a b : K) (fi ti : Fin 3) :
    evalWord a b (pairWord fi ti) = (genOf a b ti)⁻¹ * genOf a b fi := by
  simp [pairWord, evalWord_append, evalWord_inv, evalWord_genWord]

private lemma biGraph_adj_gen {K X : Type*} [Group K] [MulAction K X] (a b : K)
    (t : Fin 3) (x : X) :
    (biGraph X a b).Adj (false, x) (true, genOf a b t • x) := by
  refine ⟨by simp, Or.inl ⟨rfl, rfl, ?_⟩⟩
  fin_cases t
  · left; simp [genOf]
  · right; left; rfl
  · right; right; rfl

private lemma genOf_inj_on_point {K X : Type*} [Group K] [MulAction K X] {a b : K}
    (hsep : ∀ z : X, a • z ≠ z ∧ b • z ≠ z ∧ a • z ≠ b • z)
    (z : X) {i j : Fin 3} (h : genOf a b i • z = genOf a b j • z) : i = j := by
  obtain ⟨ha, hb, hab⟩ := hsep z
  fin_cases i <;> fin_cases j <;> simp [genOf] at h ⊢
  · exact (ha h.symm).elim
  · exact (hb h.symm).elim
  · exact (ha h).elim
  · exact (hab h).elim
  · exact (hb h).elim
  · exact (hab h.symm).elim

private lemma bipartite_cycle_copy {K X : Type*} [Group K] [MulAction K X] {a b : K}
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (F T : Fin n → X)
    (hF : Function.Injective F) (hT : Function.Injective T)
    (hfwd : ∀ i : Fin n, (biGraph X a b).Adj (false, F i) (true, T i))
    (hbwd : ∀ i : Fin n, (biGraph X a b).Adj (true, T i) (false, F (i + 1))) :
    cycleGraph (2 * n) ⊑ biGraph X a b := by
  have _ : NeZero (2 * n) := ⟨by omega⟩
  let φ : Fin (2 * n) → Bool × X := fun i =>
    if i.val % 2 = 0 then (false, F ⟨i.val / 2, by omega⟩)
    else (true, T ⟨i.val / 2, by omega⟩)
  have hφ_inj : Function.Injective φ := by
    intro i j hij
    dsimp only [φ] at hij
    by_cases hi : i.val % 2 = 0 <;> by_cases hj : j.val % 2 = 0
    · simp only [hi, hj, ↓reduceIte, Prod.mk.injEq, true_and] at hij
      have hdiv : i.val / 2 = j.val / 2 := congrArg Fin.val (hF hij)
      exact Fin.ext (by omega)
    · simp only [hi, hj, ↓reduceIte, Prod.mk.injEq] at hij
      exact (Bool.false_ne_true hij.1).elim
    · simp only [hi, hj, ↓reduceIte, Prod.mk.injEq] at hij
      exact (Bool.false_ne_true hij.1.symm).elim
    · simp only [hi, hj, ↓reduceIte, Prod.mk.injEq, true_and] at hij
      have hdiv : i.val / 2 = j.val / 2 := congrArg Fin.val (hT hij)
      exact Fin.ext (by omega)
  have hstep : ∀ i : Fin (2 * n), (biGraph X a b).Adj (φ i) (φ (i + 1)) := by
    intro i
    have h1 : (1 : Fin (2 * n)).val = 1 := by
      rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    have h1n : (1 : Fin n).val = 1 := by
      rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    have hadd : (i + 1 : Fin (2 * n)).val = (i.val + 1) % (2 * n) := by
      rw [Fin.val_add, h1]
    dsimp only [φ]
    by_cases hi : i.val % 2 = 0
    · have hlt : i.val + 1 < 2 * n := by omega
      have hval : (i + 1 : Fin (2 * n)).val = i.val + 1 := by
        rw [hadd, Nat.mod_eq_of_lt hlt]
      have hodd : ¬ (i + 1 : Fin (2 * n)).val % 2 = 0 := by omega
      have hdiv : (⟨(i + 1 : Fin (2 * n)).val / 2, by omega⟩ : Fin n) =
          ⟨i.val / 2, by omega⟩ := by
        apply Fin.ext; dsimp only; omega
      simp only [hi, hodd, ↓reduceIte, hdiv]
      exact hfwd ⟨i.val / 2, by omega⟩
    · have hlt_cases : i.val + 1 < 2 * n ∨ i.val + 1 = 2 * n := by omega
      rcases hlt_cases with hlt | heq
      · have hval : (i + 1 : Fin (2 * n)).val = i.val + 1 := by
          rw [hadd, Nat.mod_eq_of_lt hlt]
        have heven : (i + 1 : Fin (2 * n)).val % 2 = 0 := by omega
        have hdiv : (⟨(i + 1 : Fin (2 * n)).val / 2, by omega⟩ : Fin n) =
            (⟨i.val / 2, by omega⟩ : Fin n) + 1 := by
          apply Fin.ext
          change (i + 1 : Fin (2 * n)).val / 2 = (i.val / 2 + (1 : Fin n).val) % n
          rw [h1n, Nat.mod_eq_of_lt (by omega)]
          omega
        simp only [hi, heven, ↓reduceIte, hdiv]
        exact hbwd ⟨i.val / 2, by omega⟩
      · have hval : (i + 1 : Fin (2 * n)).val = 0 := by
          rw [hadd, heq, Nat.mod_self]
        have heven : (i + 1 : Fin (2 * n)).val % 2 = 0 := by omega
        have hdiv : (⟨(i + 1 : Fin (2 * n)).val / 2, by omega⟩ : Fin n) =
            (⟨i.val / 2, by omega⟩ : Fin n) + 1 := by
          apply Fin.ext
          change (i + 1 : Fin (2 * n)).val / 2 = (i.val / 2 + (1 : Fin n).val) % n
          rw [h1n, hval]
          have hqn : i.val / 2 + 1 = n := by omega
          rw [hqn, Nat.mod_self]
        simp only [hi, heven, ↓reduceIte, hdiv]
        exact hbwd ⟨i.val / 2, by omega⟩
  refine ⟨⟨⟨φ, ?_⟩, hφ_inj⟩⟩
  intro i j hij
  have hlt1 : 1 < 2 * n := by omega
  have h' : i - j = 1 ∨ j - i = 1 := by
    simpa only [Fin.ext_iff, Fin.val_one', Nat.mod_eq_of_lt hlt1] using cycleGraph_adj'.mp hij
  rcases h' with h' | h'
  · have eq : i = j + 1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h'
    rw [eq]
    exact (hstep j).symm
  · have eq : j = i + 1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h'
    rw [eq]
    exact hstep i

private lemma walk4_gives_C4 {K X : Type*} [Group K] [MulAction K X] {a b : K}
    (hsep : ∀ z : X, a • z ≠ z ∧ b • z ≠ z ∧ a • z ≠ b • z)
    (p0 p1 : Fin 3 × Fin 3)
    (hs0 : p0.1 ≠ p0.2) (_hs1 : p1.1 ≠ p1.2) (hl0 : p0.2 ≠ p1.1) (_hl1 : p1.2 ≠ p0.1)
    (z : X) (hclose : evalWord a b (walkWordList [p0, p1]) • z = z) :
    cycleGraph 4 ⊑ biGraph X a b := by
  let F0 := z
  let T0 := genOf a b p0.1 • F0
  let F1 := (genOf a b p0.2)⁻¹ • T0
  let T1 := genOf a b p1.1 • F1
  have hF0_eq : (genOf a b p1.2)⁻¹ • T1 = F0 := by
    dsimp only [T1, F1, T0, F0]
    simpa [walkWordList, evalWord_append, evalWord_pairWord, mul_smul] using hclose
  have hFne : F0 ≠ F1 := by
    intro h
    have h' : genOf a b p0.2 • F0 = genOf a b p0.1 • F0 := by
      dsimp only [F1, T0] at h
      calc genOf a b p0.2 • F0 = genOf a b p0.2 • ((genOf a b p0.2)⁻¹ • (genOf a b p0.1 • F0)) := by
            rw [← h]
        _ = genOf a b p0.1 • F0 := smul_inv_smul _ _
    exact hs0 (genOf_inj_on_point hsep F0 h'.symm)
  have hTne : T0 ≠ T1 := by
    intro h
    have h' : genOf a b p0.2 • F1 = genOf a b p1.1 • F1 := by
      calc genOf a b p0.2 • F1 = T0 := smul_inv_smul _ T0
        _ = T1 := h
    exact hl0 (genOf_inj_on_point hsep F1 h')
  have hFinj : Function.Injective ![F0, F1] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hTinj : Function.Injective ![T0, T1] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  apply bipartite_cycle_copy (n := 2) (by omega) ![F0, F1] ![T0, T1] hFinj hTinj
  · intro i
    fin_cases i
    · exact biGraph_adj_gen a b p0.1 F0
    · exact biGraph_adj_gen a b p1.1 F1
  · intro i
    fin_cases i
    · have h : T0 = genOf a b p0.2 • F1 := (smul_inv_smul _ T0).symm
      simpa [h] using (biGraph_adj_gen a b p0.2 F1).symm
    · have h : T1 = genOf a b p1.2 • F0 := by
        calc T1 = genOf a b p1.2 • ((genOf a b p1.2)⁻¹ • T1) := (smul_inv_smul _ T1).symm
          _ = genOf a b p1.2 • F0 := by rw [hF0_eq]
      simpa [h] using (biGraph_adj_gen a b p1.2 F0).symm

private lemma walk8_gives_C4_or_C8 {K X : Type*} [Group K] [MulAction K X] {a b : K}
    (hsep : ∀ z : X, a • z ≠ z ∧ b • z ≠ z ∧ a • z ≠ b • z)
    (p0 p1 p2 p3 : Fin 3 × Fin 3)
    (hs0 : p0.1 ≠ p0.2) (hs1 : p1.1 ≠ p1.2) (hs2 : p2.1 ≠ p2.2) (hs3 : p3.1 ≠ p3.2)
    (hl0 : p0.2 ≠ p1.1) (hl1 : p1.2 ≠ p2.1) (hl2 : p2.2 ≠ p3.1) (hl3 : p3.2 ≠ p0.1)
    (z : X) (hclose : evalWord a b (walkWordList [p0, p1, p2, p3]) • z = z) :
    cycleGraph 4 ⊑ biGraph X a b ∨ cycleGraph 8 ⊑ biGraph X a b := by
  let F0 := z
  let T0 := genOf a b p0.1 • F0
  let F1 := (genOf a b p0.2)⁻¹ • T0
  let T1 := genOf a b p1.1 • F1
  let F2 := (genOf a b p1.2)⁻¹ • T1
  let T2 := genOf a b p2.1 • F2
  let F3 := (genOf a b p2.2)⁻¹ • T2
  let T3 := genOf a b p3.1 • F3
  have hF0_eq : (genOf a b p3.2)⁻¹ • T3 = F0 := by
    dsimp only [T3, F3, T2, F2, T1, F1, T0, F0]
    simpa [walkWordList, evalWord_append, evalWord_pairWord, mul_smul] using hclose
  let F : Fin 4 → X := ![F0, F1, F2, F3]
  let T : Fin 4 → X := ![T0, T1, T2, T3]
  have hfwd : ∀ i : Fin 4, (biGraph X a b).Adj (false, F i) (true, T i) := by
    intro i; fin_cases i
    · exact biGraph_adj_gen a b p0.1 F0
    · exact biGraph_adj_gen a b p1.1 F1
    · exact biGraph_adj_gen a b p2.1 F2
    · exact biGraph_adj_gen a b p3.1 F3
  have hbwd : ∀ i : Fin 4, (biGraph X a b).Adj (true, T i) (false, F (i + 1)) := by
    intro i; fin_cases i
    · have h : T0 = genOf a b p0.2 • F1 := (smul_inv_smul _ T0).symm
      simpa [F, T, h] using (biGraph_adj_gen a b p0.2 F1).symm
    · have h : T1 = genOf a b p1.2 • F2 := (smul_inv_smul _ T1).symm
      simpa [F, T, h] using (biGraph_adj_gen a b p1.2 F2).symm
    · have h : T2 = genOf a b p2.2 • F3 := (smul_inv_smul _ T2).symm
      simpa [F, T, h] using (biGraph_adj_gen a b p2.2 F3).symm
    · have h : T3 = genOf a b p3.2 • F0 := by
        calc T3 = genOf a b p3.2 • ((genOf a b p3.2)⁻¹ • T3) := (smul_inv_smul _ T3).symm
          _ = genOf a b p3.2 • F0 := by rw [hF0_eq]
      simpa [F, T, h] using (biGraph_adj_gen a b p3.2 F0).symm
  have hF01 : F0 ≠ F1 := fun h => hs0 (genOf_inj_on_point hsep F0 (by
    calc genOf a b p0.1 • F0 = T0 := rfl
      _ = genOf a b p0.2 • F1 := (smul_inv_smul _ T0).symm
      _ = genOf a b p0.2 • F0 := by rw [← h]))
  have hF12 : F1 ≠ F2 := fun h => hs1 (genOf_inj_on_point hsep F1 (by
    calc genOf a b p1.1 • F1 = T1 := rfl
      _ = genOf a b p1.2 • F2 := (smul_inv_smul _ T1).symm
      _ = genOf a b p1.2 • F1 := by rw [← h]))
  have hF23 : F2 ≠ F3 := fun h => hs2 (genOf_inj_on_point hsep F2 (by
    calc genOf a b p2.1 • F2 = T2 := rfl
      _ = genOf a b p2.2 • F3 := (smul_inv_smul _ T2).symm
      _ = genOf a b p2.2 • F2 := by rw [← h]))
  have hF30 : F3 ≠ F0 := fun h => hs3 (genOf_inj_on_point hsep F3 (by
    calc genOf a b p3.1 • F3 = T3 := rfl
      _ = genOf a b p3.2 • F0 := by
            calc T3 = genOf a b p3.2 • ((genOf a b p3.2)⁻¹ • T3) := (smul_inv_smul _ T3).symm
              _ = genOf a b p3.2 • F0 := by rw [hF0_eq]
      _ = genOf a b p3.2 • F3 := by rw [← h]))
  have hT01 : T0 ≠ T1 := fun h => hl0 (genOf_inj_on_point hsep F1 (by
    calc genOf a b p0.2 • F1 = T0 := smul_inv_smul _ T0
      _ = genOf a b p1.1 • F1 := h))
  have hT12 : T1 ≠ T2 := fun h => hl1 (genOf_inj_on_point hsep F2 (by
    calc genOf a b p1.2 • F2 = T1 := smul_inv_smul _ T1
      _ = genOf a b p2.1 • F2 := h))
  have hT23 : T2 ≠ T3 := fun h => hl2 (genOf_inj_on_point hsep F3 (by
    calc genOf a b p2.2 • F3 = T2 := smul_inv_smul _ T2
      _ = genOf a b p3.1 • F3 := h))
  have hT30 : T3 ≠ T0 := fun h => hl3 (genOf_inj_on_point hsep F0 (by
    calc genOf a b p3.2 • F0 = T3 := by
            calc genOf a b p3.2 • F0 = genOf a b p3.2 • ((genOf a b p3.2)⁻¹ • T3) := by rw [hF0_eq]
              _ = T3 := smul_inv_smul _ T3
      _ = genOf a b p0.1 • F0 := h))
  by_cases h02 : F0 = F2
  · left
    refine bipartite_cycle_copy (n := 2) (by omega) ![F0, F1] ![T0, T1] ?_ ?_ ?_ ?_
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · intro i; fin_cases i
      · exact hfwd 0
      · exact hfwd 1
    · intro i; fin_cases i
      · exact hbwd 0
      · simpa [F, T, h02] using hbwd 1
  by_cases h13 : F1 = F3
  · left
    refine bipartite_cycle_copy (n := 2) (by omega) ![F1, F2] ![T1, T2] ?_ ?_ ?_ ?_
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · intro i; fin_cases i
      · exact hfwd 1
      · exact hfwd 2
    · intro i; fin_cases i
      · exact hbwd 1
      · simpa [F, T, h13] using hbwd 2
  by_cases ht02 : T0 = T2
  · left
    refine bipartite_cycle_copy (n := 2) (by omega) ![F1, F2] ![T1, T2] ?_ ?_ ?_ ?_
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · intro i; fin_cases i
      · exact hfwd 1
      · exact hfwd 2
    · intro i; fin_cases i
      · exact hbwd 1
      · simpa [F, T, ← ht02] using hbwd 0
  by_cases ht13 : T1 = T3
  · left
    refine bipartite_cycle_copy (n := 2) (by omega) ![F2, F3] ![T2, T3] ?_ ?_ ?_ ?_
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    · intro i; fin_cases i
      · exact hfwd 2
      · exact hfwd 3
    · intro i; fin_cases i
      · exact hbwd 2
      · simpa [F, T, ← ht13] using hbwd 1
  right
  refine bipartite_cycle_copy (n := 4) (by omega) F T ?_ ?_ hfwd hbwd
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [F] at hij ⊢ <;> first
      | exact (hF01 hij).elim | exact (hF01 hij.symm).elim
      | exact (hF12 hij).elim | exact (hF12 hij.symm).elim
      | exact (hF23 hij).elim | exact (hF23 hij.symm).elim
      | exact (hF30 hij).elim | exact (hF30 hij.symm).elim
      | exact (h02 hij).elim | exact (h02 hij.symm).elim
      | exact (h13 hij).elim | exact (h13 hij.symm).elim
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [T] at hij ⊢ <;> first
      | exact (hT01 hij).elim | exact (hT01 hij.symm).elim
      | exact (hT12 hij).elim | exact (hT12 hij.symm).elim
      | exact (hT23 hij).elim | exact (hT23 hij.symm).elim
      | exact (hT30 hij).elim | exact (hT30 hij.symm).elim
      | exact (ht02 hij).elim | exact (ht02 hij.symm).elim
      | exact (ht13 hij).elim | exact (ht13 hij.symm).elim

/- ## Section 4: Computable certificate checker and soundness -/

inductive SepGen : Type
  | a | b | aib | ai | bi | bia
  deriving DecidableEq

def sepGenWord : SepGen → Word
  | .a => [.a]
  | .b => [.b]
  | .aib => [.ai, .b]
  | .ai => [.ai]
  | .bi => [.bi]
  | .bia => [.bi, .a]

inductive KillCert : Type
  | sep (g : SepGen) (s : Word) (prod : List (Bool × Nat))
  | comm (invFlag : Bool) (prod : List (Bool × Nat))
  | w4 (s : Word) (p0 p1 : Fin 3 × Fin 3) (prod : List (Bool × Nat))
  | w8 (s : Word) (p0 p1 p2 p3 : Fin 3 × Fin 3) (prod : List (Bool × Nat))

def evalProdWord (pool : List Word) : List (Bool × Nat) → Word
  | [] => []
  | (invFlag, idx) :: rest =>
    let w := pool.getD idx []
    (if invFlag then wordInv w else w) ++ evalProdWord pool rest

def commWord : Word := [.bi, .ai, .b, .a]

def nbPair (p : Fin 3 × Fin 3) : Bool := p.1 != p.2
def nbLink (p q : Fin 3 × Fin 3) : Bool := p.2 != q.1

def normEq (w₁ w₂ : Word) : Bool :=
  let n1 := normWord w₁
  n1.valid && (n1 == normWord w₂)

def checkKill (pool : List Word) (c : KillCert) : Bool :=
  match c with
  | .sep g s prod =>
    normEq (evalProdWord pool prod) (wordConj s (sepGenWord g))
  | .comm invFlag prod =>
    normEq (evalProdWord pool prod) (if invFlag then wordInv commWord else commWord)
  | .w4 s p0 p1 prod =>
    nbPair p0 && nbPair p1 && nbLink p0 p1 && nbLink p1 p0 &&
    normEq (evalProdWord pool prod) (wordConj s (walkWordList [p0, p1]))
  | .w8 s p0 p1 p2 p3 prod =>
    nbPair p0 && nbPair p1 && nbPair p2 && nbPair p3 &&
    nbLink p0 p1 && nbLink p1 p2 && nbLink p2 p3 && nbLink p3 p0 &&
    normEq (evalProdWord pool prod) (wordConj s (walkWordList [p0, p1, p2, p3]))

def dist34A : List (Bool × Fin 8 × Fin 8) :=
  [(false, 0, 3), (false, 0, 4), (false, 0, 5), (false, 1, 4), (false, 1, 5), (false, 1, 6)]

def dist34B : List (Bool × Fin 8 × Fin 8) :=
  [(false, 2, 5), (false, 2, 6), (false, 2, 7), (false, 3, 6), (false, 3, 7), (false, 4, 7)]

def dist34C : List (Bool × Fin 8 × Fin 8) :=
  [(true, 0, 3), (true, 0, 4), (true, 0, 5), (true, 1, 4), (true, 1, 5), (true, 1, 6)]

def dist34D : List (Bool × Fin 8 × Fin 8) :=
  [(true, 2, 5), (true, 2, 6), (true, 2, 7), (true, 3, 6), (true, 3, 7), (true, 4, 7)]

def dist34Pairs : List (Bool × Fin 8 × Fin 8) :=
  dist34A ++ dist34B ++ dist34C ++ dist34D

def collisionWord (seq : Fin 8 → Fin 3 × Fin 3) (side : Bool) (i j : Fin 8) : Word :=
  if side then wordInv (walkTWord seq i) ++ walkTWord seq j
  else wordInv (walkFWord seq i.val) ++ walkFWord seq j.val

def checkSeq16 (seq : Fin 8 → Fin 3 × Fin 3) : Bool :=
  ([0, 1, 2, 3, 4, 5, 6, 7] : List (Fin 8)).all fun i =>
    nbPair (seq i) && nbLink (seq i) (seq (i + 1))

def checkCycle16Pair (H : List Word) (seq : Fin 8 → Fin 3 × Fin 3)
    (certs : List (Bool × Fin 8 × Fin 8 × KillCert))
    (survs : List Word) (p : Bool × Fin 8 × Fin 8) : Bool :=
  let side := p.1
  let i := p.2.1
  let j := p.2.2
  let w := collisionWord seq side i j
  match certs.find? (fun e => e.1 == side && e.2.1 == i && e.2.2.1 == j) with
  | some (_, _, _, c) => checkKill (w :: H) c
  | none => survs.any (fun s => normEq w s || normEq w (wordInv s))

def checkCycle16 (H : List Word) (seq : Fin 8 → Fin 3 × Fin 3)
    (monoProd : List (Bool × Nat))
    (certs : List (Bool × Fin 8 × Fin 8 × KillCert))
    (survs : List Word) : Bool :=
  checkSeq16 seq &&
  normEq (walkFWord seq 8) (evalProdWord H monoProd) &&
  dist34Pairs.all (checkCycle16Pair H seq certs survs)

private lemma checkCycle16_of_parts (H : List Word) (seq : Fin 8 → Fin 3 × Fin 3)
    (monoProd : List (Bool × Nat))
    (certs : List (Bool × Fin 8 × Fin 8 × KillCert))
    (survs : List Word)
    (h1 : checkSeq16 seq = true)
    (h2 : normEq (walkFWord seq 8) (evalProdWord H monoProd) = true)
    (hA : dist34A.all (checkCycle16Pair H seq certs survs) = true)
    (hB : dist34B.all (checkCycle16Pair H seq certs survs) = true)
    (hC : dist34C.all (checkCycle16Pair H seq certs survs) = true)
    (hD : dist34D.all (checkCycle16Pair H seq certs survs) = true) :
    checkCycle16 H seq monoProd certs survs = true := by
  simp [checkCycle16, dist34Pairs, h1, h2, hA, hB, hC, hD]

section CertSoundness

variable {K X B : Type*} [Group K] [MulAction K X] [AddCommGroup B]

private lemma evalWord_eq_of_normEq (f : K →* Multiplicative B)
    (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (ha2 : a * a ∈ f.ker) {w₁ w₂ : Word} (h : normEq w₁ w₂ = true) :
    evalWord a b w₁ = evalWord a b w₂ := by
  simp only [normEq, Bool.and_eq_true, beq_iff_eq] at h
  exact evalWord_eq_of_norm f hker a b ha2 h.1 h.2

private lemma evalProdWord_fixes (a b : K) (y : X) {pool : List Word}
    (hpool : ∀ w ∈ pool, evalWord a b w • y = y) (prod : List (Bool × Nat)) :
    evalWord a b (evalProdWord pool prod) • y = y := by
  induction prod with
  | nil => simp [evalProdWord, evalWord]
  | cons hd tl ih =>
    rcases hd with ⟨invFlag, idx⟩
    simp only [evalProdWord, evalWord_append, mul_smul]
    rw [ih]
    have hget : evalWord a b (pool.getD idx []) • y = y := by
      by_cases hi : idx < pool.length
      · rw [List.getD_eq_getElem _ _ hi]
        exact hpool _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
        simp [evalWord]
    cases invFlag
    · simpa using hget
    · simp only [↓reduceIte, evalWord_inv]
      calc (evalWord a b (pool.getD idx []))⁻¹ • y
          = (evalWord a b (pool.getD idx []))⁻¹ • (evalWord a b (pool.getD idx []) • y) := by
            rw [hget]
        _ = y := inv_smul_smul _ _

private lemma sepGen_ne (a b : K) (hsep : ∀ z : X, a • z ≠ z ∧ b • z ≠ z ∧ a • z ≠ b • z)
    (g : SepGen) (z : X) : evalWord a b (sepGenWord g) • z ≠ z := by
  obtain ⟨ha, hb, hab⟩ := hsep z
  cases g with
  | a => simpa [sepGenWord, evalWord, evalLetter] using ha
  | b => simpa [sepGenWord, evalWord, evalLetter] using hb
  | aib =>
    intro h
    simp only [sepGenWord, evalWord, evalLetter, mul_one, mul_smul] at h
    have h1 := congrArg (a • ·) h
    rw [smul_inv_smul] at h1
    exact hab h1.symm
  | ai =>
    intro h
    simp only [sepGenWord, evalWord, evalLetter, mul_one] at h
    have h1 := congrArg (a • ·) h
    rw [smul_inv_smul] at h1
    exact ha h1.symm
  | bi =>
    intro h
    simp only [sepGenWord, evalWord, evalLetter, mul_one] at h
    have h1 := congrArg (b • ·) h
    rw [smul_inv_smul] at h1
    exact hb h1.symm
  | bia =>
    intro h
    simp only [sepGenWord, evalWord, evalLetter, mul_one, mul_smul] at h
    have h1 := congrArg (b • ·) h
    rw [smul_inv_smul] at h1
    exact hab h1

private lemma commWord_ne (a b : K) (y : X) (hnc : a • (b • y) ≠ b • (a • y))
    (invFlag : Bool) :
    evalWord a b (if invFlag then wordInv commWord else commWord) • y ≠ y := by
  have hcomm_ne : evalWord a b commWord • y ≠ y := by
    intro h
    simp only [commWord, evalWord, evalLetter, mul_one, mul_smul] at h
    apply hnc
    have h1 : b • (b⁻¹ • (a⁻¹ • (b • (a • y)))) = b • y := congrArg (b • ·) h
    rw [smul_inv_smul] at h1
    have h2 : a • (a⁻¹ • (b • (a • y))) = a • (b • y) := congrArg (a • ·) h1
    rw [smul_inv_smul] at h2
    exact h2.symm
  cases invFlag
  · simpa using hcomm_ne
  · intro h
    simp only [↓reduceIte, evalWord_inv] at h
    apply hcomm_ne
    have h1 := congrArg (evalWord a b commWord • ·) h
    simpa [smul_inv_smul] using h1.symm

private lemma kill_sound (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (ha2 : a * a ∈ f.ker)
    (hsep : ∀ z : X, a • z ≠ z ∧ b • z ≠ z ∧ a • z ≠ b • z)
    (y : X) (hnc : a • (b • y) ≠ b • (a • y))
    (hno4 : ¬ cycleGraph 4 ⊑ biGraph X a b)
    (hno8 : ¬ cycleGraph 8 ⊑ biGraph X a b)
    {pool : List Word}
    (hpool : ∀ w ∈ pool, evalWord a b w • y = y)
    {c : KillCert} (hok : checkKill pool c = true) : False := by
  cases c with
  | sep g s prod =>
    simp only [checkKill] at hok
    have heq := evalWord_eq_of_normEq f hker a b ha2 hok
    have hfix := evalProdWord_fixes a b y hpool prod
    rw [heq, evalWord_conj, mul_smul, mul_smul] at hfix
    have hz : evalWord a b (sepGenWord g) • (evalWord a b s • y) = evalWord a b s • y := by
      have h1 := congrArg (evalWord a b s • ·) hfix
      simpa [smul_inv_smul] using h1
    exact sepGen_ne a b hsep g (evalWord a b s • y) hz
  | comm invFlag prod =>
    simp only [checkKill] at hok
    have heq := evalWord_eq_of_normEq f hker a b ha2 hok
    have hfix := evalProdWord_fixes a b y hpool prod
    rw [heq] at hfix
    exact commWord_ne a b y hnc invFlag hfix
  | w4 s p0 p1 prod =>
    simp only [checkKill, nbPair, nbLink, Bool.and_eq_true, bne_iff_ne] at hok
    obtain ⟨⟨⟨⟨hs0, hs1⟩, hl0⟩, hl1⟩, hneq⟩ := hok
    have heq := evalWord_eq_of_normEq f hker a b ha2 hneq
    have hfix := evalProdWord_fixes a b y hpool prod
    rw [heq, evalWord_conj, mul_smul, mul_smul] at hfix
    have hz : evalWord a b (walkWordList [p0, p1]) • (evalWord a b s • y) =
        evalWord a b s • y := by
      have h1 := congrArg (evalWord a b s • ·) hfix
      simpa [smul_inv_smul] using h1
    exact hno4 (walk4_gives_C4 hsep p0 p1 hs0 hs1 hl0 hl1 (evalWord a b s • y) hz)
  | w8 s p0 p1 p2 p3 prod =>
    simp only [checkKill, nbPair, nbLink, Bool.and_eq_true, bne_iff_ne] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hs0, hs1⟩, hs2⟩, hs3⟩, hl0⟩, hl1⟩, hl2⟩, hl3⟩, hneq⟩ := hok
    have heq := evalWord_eq_of_normEq f hker a b ha2 hneq
    have hfix := evalProdWord_fixes a b y hpool prod
    rw [heq, evalWord_conj, mul_smul, mul_smul] at hfix
    have hz : evalWord a b (walkWordList [p0, p1, p2, p3]) • (evalWord a b s • y) =
        evalWord a b s • y := by
      have h1 := congrArg (evalWord a b s • ·) hfix
      simpa [smul_inv_smul] using h1
    rcases walk8_gives_C4_or_C8 hsep p0 p1 p2 p3 hs0 hs1 hs2 hs3 hl0 hl1 hl2 hl3
        (evalWord a b s • y) hz with h4 | h8
    · exact hno4 h4
    · exact hno8 h8

private lemma mem_dist34Pairs (side : Bool) (i j : Fin 8)
    (hij : i.val < j.val) (hlo : 3 ≤ j.val - i.val) (hhi : j.val - i.val ≤ 5) :
    (side, i, j) ∈ dist34Pairs := by
  have hdec : ∀ (s : Bool) (a b : Fin 8),
      (a.val < b.val ∧ 3 ≤ b.val - a.val ∧ b.val - a.val ≤ 5) →
      (s, a, b) ∈ dist34Pairs := by decide
  exact hdec side i j ⟨hij, hlo, hhi⟩

private lemma cycle16_sound (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (ha2 : a * a ∈ f.ker)
    (hsep : ∀ z : X, a • z ≠ z ∧ b • z ≠ z ∧ a • z ≠ b • z)
    (y : X) (hnc : a • (b • y) ≠ b • (a • y))
    (hno4 : ¬ cycleGraph 4 ⊑ biGraph X a b)
    (hno8 : ¬ cycleGraph 8 ⊑ biGraph X a b)
    (hno16 : ¬ cycleGraph 16 ⊑ biGraph X a b)
    {H : List Word}
    (hH : ∀ w ∈ H, evalWord a b w • y = y)
    {seq : Fin 8 → Fin 3 × Fin 3} {monoProd : List (Bool × Nat)}
    {certs : List (Bool × Fin 8 × Fin 8 × KillCert)} {survs : List Word}
    (hok : checkCycle16 H seq monoProd certs survs = true) :
    ∃ s ∈ survs, evalWord a b s • y = y := by
  simp only [checkCycle16, Bool.and_eq_true] at hok
  obtain ⟨⟨hseq_nb, hmono_eq⟩, hall⟩ := hok
  have hnb : ∀ i : Fin 8, (seq i).1 ≠ (seq i).2 ∧ (seq i).2 ≠ (seq (i + 1)).1 := by
    intro i
    have hi : i ∈ ([0, 1, 2, 3, 4, 5, 6, 7] : List (Fin 8)) := by fin_cases i <;> decide
    have h := List.all_eq_true.mp hseq_nb i hi
    simpa [nbPair, nbLink] using h
  have hclose : evalWord a b (walkFWord seq 8) • y = y := by
    rw [evalWord_eq_of_normEq f hker a b ha2 hmono_eq]
    exact evalProdWord_fixes a b y hH monoProd
  let F : Fin 8 → X := fun i => evalWord a b (walkFWord seq i.val) • y
  let T : Fin 8 → X := fun i => evalWord a b (walkTWord seq i) • y
  have hT_eq : ∀ i : Fin 8, T i = genOf a b (seq i).1 • F i := by
    intro i
    simp only [T, F, walkTWord, evalWord_append, evalWord_genWord, mul_smul]
  have hF_next : ∀ i : Fin 8, F (i + 1) = (genOf a b (seq i).2)⁻¹ • T i := by
    clear hall hseq_nb hmono_eq
    intro i
    by_cases h7 : i.val < 7
    · have hv : (i + 1 : Fin 8).val = i.val + 1 := by
        rw [Fin.val_add, show (1 : Fin 8).val = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hmod : (⟨i.val % 8, Nat.mod_lt _ (by omega)⟩ : Fin 8) = i :=
        Fin.ext (Nat.mod_eq_of_lt i.isLt)
      dsimp only [F]
      rw [hv, walkFWord, hmod, evalWord_append, evalWord_pairWord, mul_smul, mul_smul, ← hT_eq i]
    · have hi7 : i = 7 := Fin.ext (by omega)
      subst hi7
      have h71 : (7 + 1 : Fin 8) = 0 := rfl
      rw [h71]
      have hF0 : F 0 = y := by simp [F, walkFWord, evalWord]
      rw [hF0]
      have h8 : evalWord a b (walkFWord seq 8) • y = (genOf a b (seq 7).2)⁻¹ • T 7 := by
        change evalWord a b (pairWord (seq 7).1 (seq 7).2 ++ walkFWord seq 7) • y = _
        have hF7 : evalWord a b (walkFWord seq 7) • y = F 7 := rfl
        rw [evalWord_append, evalWord_pairWord, mul_smul, mul_smul, hF7, ← hT_eq 7]
      exact hclose.symm.trans h8
  have hfwd : ∀ i : Fin 8, (biGraph X a b).Adj (false, F i) (true, T i) := by
    intro i; rw [hT_eq i]; exact biGraph_adj_gen a b (seq i).1 (F i)
  have hbwd : ∀ i : Fin 8, (biGraph X a b).Adj (true, T i) (false, F (i + 1)) := by
    intro i
    have h : T i = genOf a b (seq i).2 • F (i + 1) := by
      rw [hF_next i, smul_inv_smul]
    rw [h]
    exact (biGraph_adj_gen a b (seq i).2 (F (i + 1))).symm
  have hF_adj_ne : ∀ i : Fin 8, F i ≠ F (i + 1) := by
    intro i heq
    have h1 : genOf a b (seq i).1 • F i = genOf a b (seq i).2 • F i := by
      calc genOf a b (seq i).1 • F i = T i := (hT_eq i).symm
        _ = genOf a b (seq i).2 • F (i + 1) := by rw [hF_next i, smul_inv_smul]
        _ = genOf a b (seq i).2 • F i := by rw [← heq]
    exact (hnb i).1 (genOf_inj_on_point hsep (F i) h1)
  have hT_adj_ne : ∀ i : Fin 8, T i ≠ T (i + 1) := by
    intro i heq
    have h1 : genOf a b (seq i).2 • F (i + 1) = genOf a b (seq (i + 1)).1 • F (i + 1) := by
      calc genOf a b (seq i).2 • F (i + 1) = T i := by rw [hF_next i, smul_inv_smul]
        _ = T (i + 1) := heq
        _ = genOf a b (seq (i + 1)).1 • F (i + 1) := hT_eq (i + 1)
    exact (hnb i).2 (genOf_inj_on_point hsep (F (i + 1)) h1)
  have hF_d2_ne : ∀ i : Fin 8, F i ≠ F (i + 2) := by
    clear hall hseq_nb hmono_eq
    intro i heq
    apply hno4
    refine bipartite_cycle_copy (n := 2) (by decide) ![F i, F (i + 1)] ![T i, T (i + 1)] ?_ ?_ ?_ ?_
    · intro u v huv
      have hne := hF_adj_ne i
      fin_cases u <;> fin_cases v
      · rfl
      · exact (hne huv).elim
      · exact (hne huv.symm).elim
      · rfl
    · intro u v huv
      have hne := hT_adj_ne i
      fin_cases u <;> fin_cases v
      · rfl
      · exact (hne huv).elim
      · exact (hne huv.symm).elim
      · rfl
    · intro u; fin_cases u
      · exact hfwd i
      · exact hfwd (i + 1)
    · intro u; fin_cases u
      · exact hbwd i
      · have h := hbwd (i + 1)
        have h2 : i + 1 + 1 = i + 2 := add_assoc i 1 1
        rw [h2, ← heq] at h
        exact h
  have hT_d2_ne : ∀ i : Fin 8, T i ≠ T (i + 2) := by
    clear hall hseq_nb hmono_eq
    intro i heq
    apply hno4
    refine bipartite_cycle_copy (n := 2) (by decide)
        ![F (i + 1), F (i + 2)] ![T (i + 1), T (i + 2)] ?_ ?_ ?_ ?_
    · intro u v huv
      have hne := hF_adj_ne (i + 1)
      have h2 : i + 1 + 1 = i + 2 := add_assoc i 1 1
      rw [h2] at hne
      fin_cases u <;> fin_cases v
      · rfl
      · exact (hne huv).elim
      · exact (hne huv.symm).elim
      · rfl
    · intro u v huv
      have hne := hT_adj_ne (i + 1)
      have h2 : i + 1 + 1 = i + 2 := add_assoc i 1 1
      rw [h2] at hne
      fin_cases u <;> fin_cases v
      · rfl
      · exact (hne huv).elim
      · exact (hne huv.symm).elim
      · rfl
    · intro u; fin_cases u
      · exact hfwd (i + 1)
      · exact hfwd (i + 2)
    · intro u; fin_cases u
      · have h := hbwd (i + 1)
        have h2 : i + 1 + 1 = i + 2 := add_assoc i 1 1
        rw [h2] at h
        exact h
      · have h := hbwd i
        rw [heq] at h
        exact h
  have hcoll : ∃ (side : Bool) (i j : Fin 8),
      i.val < j.val ∧ 3 ≤ j.val - i.val ∧ j.val - i.val ≤ 5 ∧
      evalWord a b (collisionWord seq side i j) • y = y := by
    clear hall hseq_nb hmono_eq
    have hnot : ¬ (Function.Injective F ∧ Function.Injective T) := by
      intro ⟨hFi, hTi⟩
      exact hno16 (bipartite_cycle_copy (n := 8) (by decide) F T hFi hTi hfwd hbwd)
    have hpair_lt : ∀ (arr : Fin 8 → X), ¬ Function.Injective arr →
        ∃ i j : Fin 8, i.val < j.val ∧ arr i = arr j := by
      intro arr hni
      rw [Function.Injective] at hni
      push Not at hni
      obtain ⟨i, j, hij, hne⟩ := hni
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · exact ⟨i, j, hlt, hij⟩
      · exact ⟨j, i, hgt, hij.symm⟩
    have hdist_ok : ∀ (arr : Fin 8 → X),
        (∀ k : Fin 8, arr k ≠ arr (k + 1)) →
        (∀ k : Fin 8, arr k ≠ arr (k + 2)) →
        ∀ i j : Fin 8, i.val < j.val → arr i = arr j →
        3 ≤ j.val - i.val ∧ j.val - i.val ≤ 5 := by
      intro arr ha1 ha2 i j hlt heq
      have hne1 : j.val - i.val ≠ 1 := by
        intro hd
        have hj : j = i + 1 := Fin.ext (by
          rw [Fin.val_add, show (1 : Fin 8).val = 1 from rfl, Nat.mod_eq_of_lt (by omega)]; omega)
        exact ha1 i (hj ▸ heq)
      have hne7 : j.val - i.val ≠ 7 := by
        intro hd
        have hi : i = j + 1 := Fin.ext (by
          rw [Fin.val_add, show (1 : Fin 8).val = 1 from rfl]; omega)
        exact ha1 j (hi ▸ heq.symm)
      have hne2 : j.val - i.val ≠ 2 := by
        intro hd
        have hj : j = i + 2 := Fin.ext (by
          rw [Fin.val_add, show (2 : Fin 8).val = 2 from rfl, Nat.mod_eq_of_lt (by omega)]; omega)
        exact ha2 i (hj ▸ heq)
      have hne6 : j.val - i.val ≠ 6 := by
        intro hd
        have hi : i = j + 2 := Fin.ext (by
          rw [Fin.val_add, show (2 : Fin 8).val = 2 from rfl]; omega)
        exact ha2 j (hi ▸ heq.symm)
      omega
    by_cases hFi : Function.Injective F
    · have hTni : ¬ Function.Injective T := fun hTi => hnot ⟨hFi, hTi⟩
      obtain ⟨i, j, hlt, heq⟩ := hpair_lt T hTni
      obtain ⟨hlo, hhi⟩ := hdist_ok T hT_adj_ne hT_d2_ne i j hlt heq
      refine ⟨true, i, j, hlt, hlo, hhi, ?_⟩
      simp only [collisionWord, ↓reduceIte, evalWord_append, evalWord_inv, mul_smul]
      change (evalWord a b (walkTWord seq i))⁻¹ • T j = y
      rw [← heq]
      exact inv_smul_smul _ y
    · obtain ⟨i, j, hlt, heq⟩ := hpair_lt F hFi
      obtain ⟨hlo, hhi⟩ := hdist_ok F hF_adj_ne hF_d2_ne i j hlt heq
      refine ⟨false, i, j, hlt, hlo, hhi, ?_⟩
      simp only [collisionWord, Bool.false_eq_true, ↓reduceIte, evalWord_append, evalWord_inv, mul_smul]
      change (evalWord a b (walkFWord seq i.val))⁻¹ • F j = y
      rw [← heq]
      exact inv_smul_smul _ y
  obtain ⟨side, i, j, hlt, hlo, hhi, hfix⟩ := hcoll
  have hmem := mem_dist34Pairs side i j hlt hlo hhi
  have hcheck := List.all_eq_true.mp hall (side, i, j) hmem
  dsimp only [checkCycle16Pair] at hcheck
  cases hfind : certs.find? (fun e => e.1 == side && e.2.1 == i && e.2.2.1 == j) with
  | some entry =>
    rcases entry with ⟨_, _, _, c⟩
    simp only [hfind] at hcheck
    have hpool : ∀ w ∈ collisionWord seq side i j :: H, evalWord a b w • y = y := by
      intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw'
      · exact hfix
      · exact hH w hw'
    exact (kill_sound f hker a b ha2 hsep y hnc hno4 hno8 hpool hcheck).elim
  | none =>
    simp only [hfind, List.any_eq_true, Bool.or_eq_true] at hcheck
    obtain ⟨s, hs_mem, hs_eq | hs_inv⟩ := hcheck
    · refine ⟨s, hs_mem, ?_⟩
      rw [← evalWord_eq_of_normEq f hker a b ha2 hs_eq]
      exact hfix
    · refine ⟨s, hs_mem, ?_⟩
      have heq := evalWord_eq_of_normEq f hker a b ha2 hs_inv
      rw [heq, evalWord_inv] at hfix
      have h1 := congrArg (evalWord a b s • ·) hfix
      simpa [smul_inv_smul] using h1.symm

end CertSoundness

/- ## Section 5: Canonical words, sequences, and verified certificates -/

def wA1 : Word := wordInv [.a, .a, .bi, .a, .b] ++ [.b]
def wB1 : Word := [.b, .a, .a]
def wD1 : Word := [.a, .bi, .a, .b]

def wA2 : Word := wordConj [.a] (substWord [.ai] [.ai, .b] wA1)
def wB2 : Word := wordConj [.a] (substWord [.ai] [.ai, .b] wB1)
def wD2 : Word := wordConj [.a] (substWord [.ai] [.ai, .b] wD1)

def wA3 : Word := wordConj [.a, .b] (substWord [.ai] [.bi] wA1)
def wB3 : Word := wordConj [.a, .b] (substWord [.ai] [.bi] wB1)
def wD3 : Word := wordConj [.a, .b] (substWord [.ai] [.bi] wD1)

def wD1b : Word := wordConj [.b] wD1
def wD3b : Word := wordConj [.b] wD3
def wCmb : Word := wordConj [.b] commWord
def wCmbi : Word := wordConj [.bi] commWord
def wC00 : Word := wordConj [.a, .bi] commWord

def seqW1 : Fin 8 → Fin 3 × Fin 3
  | 0 => (2, 0) | 1 => (1, 2) | 2 => (1, 0) | 3 => (1, 0)
  | 4 => (2, 1) | 5 => (0, 2) | 6 => (0, 1) | 7 => (0, 1)

def seqDih : Fin 8 → Fin 3 × Fin 3
  | 0 => (0, 1) | 1 => (0, 1) | 2 => (0, 1) | 3 => (2, 1)
  | 4 => (0, 1) | 5 => (2, 0) | 6 => (1, 2) | 7 => (0, 2)

def seqW3 : Fin 8 → Fin 3 × Fin 3
  | 0 => (0, 1) | 1 => (0, 2) | 2 => (1, 0) | 3 => (2, 0)
  | 4 => (1, 0) | 5 => (1, 2) | 6 => (0, 1) | 7 => (2, 1)

def seq1b : Fin 8 → Fin 3 × Fin 3
  | 0 => (0, 2) | 1 => (0, 1) | 2 => (0, 1) | 3 => (2, 0)
  | 4 => (2, 1) | 5 => (2, 1) | 6 => (0, 2) | 7 => (0, 2)

def certsW1 : List (Bool × Fin 8 × Fin 8 × KillCert) := [
  (false, 0, 4, .w8 [] (1, 0) (1, 0) (2, 0) (1, 2) [(false, 0)]),
  (false, 1, 5, .w4 [] (1, 0) (1, 0) [(false, 0)]),
  (false, 1, 6, .w4 [] (1, 0) (1, 2) [(false, 0)]),
  (false, 2, 5, .w4 [.a, .bi, .a, .b] (1, 0) (2, 0) [(false, 0)]),
  (false, 2, 6, .w8 [.b] (0, 2) (1, 0) (1, 0) (2, 1) [(false, 0)]),
  (false, 2, 7, .comm false [(false, 0)]),
  (false, 3, 6, .comm false [(false, 0)]),
  (false, 3, 7, .sep .ai [.b] [(false, 0)]),
  (true, 0, 4, .w8 [] (1, 0) (1, 0) (2, 0) (1, 2) [(false, 0)]),
  (true, 0, 5, .w4 [] (1, 0) (1, 0) [(false, 0)]),
  (true, 1, 4, .w4 [] (1, 0) (1, 0) [(false, 0)]),
  (true, 1, 5, .w8 [.b] (0, 2) (1, 0) (1, 0) (2, 1) [(false, 0)]),
  (true, 1, 6, .sep .bia [] [(false, 0)]),
  (true, 2, 5, .sep .b [.a, .a, .bi, .a, .b] [(false, 0)]),
  (true, 2, 6, .comm false [(false, 0)]),
  (true, 2, 7, .sep .ai [.b] [(false, 0)]),
  (true, 3, 6, .sep .ai [.b] [(false, 0)])
]

def certsDih : List (Bool × Fin 8 × Fin 8 × KillCert) := [
  (false, 0, 3, .w8 [] (0, 1) (0, 1) (2, 0) (1, 2) [(false, 0), (false, 1)]),
  (false, 0, 4, .w8 [] (0, 1) (0, 1) (0, 1) (2, 1) [(false, 0)]),
  (false, 0, 5, .w8 [.a, .bi] (0, 1) (2, 1) (2, 1) (0, 2) [(false, 0), (true, 2)]),
  (false, 1, 4, .sep .aib [.ai, .ai] [(false, 0), (false, 1)]),
  (false, 1, 5, .w8 [] (0, 1) (0, 1) (0, 1) (2, 1) [(false, 0)]),
  (false, 1, 6, .w8 [.ai, .ai] (0, 1) (2, 1) (0, 1) (2, 1) [(false, 0)]),
  (false, 2, 5, .sep .aib [.ai, .ai] [(false, 0), (false, 1)]),
  (false, 2, 6, .w4 [.bi, .ai, .ai] (2, 0) (2, 1) [(false, 0), (false, 1)]),
  (false, 2, 7, .w8 [.ai, .ai, .b, .ai, .ai, .ai] (2, 1) (0, 2) (0, 1) (2, 0) [(false, 0)]),
  (false, 3, 6, .w8 [.ai, .b, .ai, .ai, .ai] (0, 1) (0, 1) (2, 1) (2, 1) [(false, 0), (false, 4)]),
  (false, 3, 7, .sep .aib [.ai, .ai, .b, .ai, .ai, .ai] [(false, 0)]),
  (false, 4, 7, .w4 [.b, .b] (1, 0) (1, 0) [(false, 0), (false, 3)]),
  (true, 0, 3, .sep .aib [.ai, .ai] [(false, 0), (false, 1)]),
  (true, 0, 4, .w8 [] (0, 1) (0, 1) (0, 1) (2, 1) [(false, 0)]),
  (true, 0, 5, .w4 [.ai] (2, 0) (2, 1) [(false, 0), (false, 1), (true, 2)]),
  (true, 1, 4, .sep .aib [.ai, .ai] [(false, 0), (false, 1)]),
  (true, 1, 5, .w8 [.ai, .ai] (0, 1) (2, 1) (0, 1) (2, 1) [(false, 0)]),
  (true, 1, 6, .w4 [.bi, .ai, .ai] (2, 0) (2, 1) [(false, 0), (false, 1)]),
  (true, 2, 5, .w4 [.bi, .ai, .ai] (2, 0) (2, 1) [(false, 0), (false, 1)]),
  (true, 2, 6, .w8 [.ai, .b, .ai, .ai, .ai] (0, 1) (0, 1) (2, 1) (2, 1) [(false, 0), (false, 4)]),
  (true, 2, 7, .w8 [.ai, .ai, .b, .ai, .ai, .ai] (2, 1) (0, 2) (0, 1) (2, 0) [(false, 0)]),
  (true, 3, 6, .sep .aib [.ai, .ai, .b, .ai, .ai, .ai] [(false, 0)]),
  (true, 3, 7, .w8 [.b, .a] (0, 1) (0, 1) (2, 0) (1, 2) [(false, 0)]),
  (true, 4, 7, .w4 [.b, .b] (1, 0) (1, 0) [(false, 0), (false, 3)])
]

def certsW3 : List (Bool × Fin 8 × Fin 8 × KillCert) := [
  (false, 0, 3, .sep .bi [.ai] [(false, 0)]),
  (false, 0, 5, .sep .a [.bi, .a] [(false, 0)]),
  (false, 1, 4, .sep .a [.bi, .a] [(false, 0)]),
  (false, 1, 5, .w4 [.bi] (1, 0) (1, 0) [(false, 0), (false, 4)]),
  (false, 1, 6, .w8 [.ai, .b, .ai] (0, 2) (1, 2) (1, 0) (2, 1) [(false, 0), (true, 1)]),
  (false, 2, 5, .sep .b [.a, .b, .a, .bi, .ai] [(false, 0), (true, 1)]),
  (false, 2, 6, .w8 [.a] (1, 0) (1, 2) (1, 0) (2, 0) [(false, 0)]),
  (false, 2, 7, .w4 [] (1, 0) (1, 0) [(false, 0)]),
  (false, 3, 6, .w4 [] (1, 0) (1, 0) [(false, 0)]),
  (false, 3, 7, .w8 [.bi, .a] (0, 1) (2, 0) (1, 0) (1, 2) [(false, 0)]),
  (false, 4, 7, .sep .bia [.a, .bi, .a] [(false, 0)]),
  (true, 0, 4, .sep .a [.bi, .a] [(false, 0)]),
  (true, 0, 5, .w4 [.bi] (1, 0) (1, 0) [(false, 0), (false, 4)]),
  (true, 1, 4, .w4 [.bi] (1, 0) (1, 0) [(false, 0), (false, 4)]),
  (true, 1, 5, .w8 [.a] (1, 0) (1, 2) (1, 0) (2, 0) [(false, 0)]),
  (true, 1, 6, .w8 [.ai, .b, .ai] (0, 2) (1, 2) (1, 0) (2, 1) [(false, 0), (true, 1)]),
  (true, 2, 5, .sep .b [.a, .b, .a, .bi, .ai] [(false, 0), (true, 1)]),
  (true, 2, 6, .w4 [] (1, 0) (1, 0) [(false, 0)]),
  (true, 2, 7, .w4 [.b] (1, 0) (2, 0) [(false, 0)]),
  (true, 3, 6, .w4 [.a, .bi, .a] (1, 0) (1, 2) [(false, 0)]),
  (true, 3, 7, .w8 [.bi, .a] (0, 1) (2, 0) (1, 0) (1, 2) [(false, 0)])
]

def certs1b : List (Bool × Fin 8 × Fin 8 × KillCert) := [
  (false, 0, 3, .sep .bi [.a, .a, .bi, .a, .b] [(false, 0), (false, 1)]),
  (false, 0, 4, .w4 [.bi] (0, 1) (0, 1) [(false, 0)]),
  (false, 0, 5, .w8 [.ai, .bi, .a] (0, 1) (2, 1) (2, 0) (1, 2) [(false, 0), (false, 1)]),
  (false, 1, 4, .w4 [.ai, .bi] (0, 1) (2, 1) [(false, 0)]),
  (false, 1, 5, .w8 [.bi] (0, 1) (0, 1) (2, 0) (2, 1) [(false, 0)]),
  (false, 1, 6, .w8 [.bi] (0, 1) (2, 1) (2, 1) (2, 1) [(false, 0), (false, 4)]),
  (false, 2, 5, .w8 [.bi] (0, 1) (0, 1) (2, 1) (2, 1) [(false, 0), (true, 1)]),
  (false, 2, 6, .w8 [.ai, .bi] (0, 1) (2, 0) (2, 1) (2, 1) [(false, 0)]),
  (false, 2, 7, .w8 [.bi] (0, 1) (0, 1) (2, 0) (2, 1) [(false, 0), (true, 3)]),
  (false, 3, 6, .w8 [.ai, .ai, .bi] (2, 1) (2, 1) (0, 1) (2, 1) [(false, 0), (true, 1)]),
  (false, 3, 7, .w4 [.b, .ai, .ai, .bi] (2, 1) (2, 1) [(false, 0)]),
  (false, 4, 7, .w4 [.b, .b, .ai, .ai, .bi] (0, 1) (2, 1) [(false, 0)]),
  (true, 0, 3, .w4 [.bi] (0, 1) (0, 1) [(false, 0)]),
  (true, 0, 4, .w4 [.ai, .bi] (0, 1) (2, 1) [(false, 0)]),
  (true, 0, 5, .w8 [.bi] (0, 1) (0, 1) (2, 0) (2, 1) [(false, 0)]),
  (true, 1, 4, .w8 [.bi] (0, 1) (0, 1) (2, 1) (2, 1) [(false, 0), (true, 1)]),
  (true, 1, 5, .w8 [.ai, .bi] (0, 1) (2, 0) (2, 1) (2, 1) [(false, 0)]),
  (true, 1, 6, .w8 [.bi] (0, 1) (2, 1) (2, 1) (2, 1) [(false, 0), (false, 4)]),
  (true, 2, 5, .w8 [.ai, .ai, .bi] (2, 1) (2, 1) (0, 1) (2, 1) [(false, 0), (true, 1)]),
  (true, 2, 6, .w8 [.ai, .bi] (0, 1) (2, 0) (2, 1) (2, 1) [(false, 0)]),
  (true, 2, 7, .w8 [.bi] (0, 1) (0, 1) (2, 0) (2, 1) [(false, 0), (true, 3)]),
  (true, 3, 6, .w4 [.b, .ai, .ai, .bi] (2, 1) (2, 1) [(false, 0)]),
  (true, 3, 7, .w4 [.b, .b, .ai, .ai, .bi] (0, 1) (2, 1) [(false, 0)]),
  (true, 4, 7, .w4 [.b] (0, 1) (0, 1) [(false, 0), (true, 3)])
]

def certA1A3 : KillCert := .comm true [(true, 0), (true, 1)]
def certA1B3 : KillCert := .w4 [.bi, .a, .b] (2, 0) (2, 1) [(false, 0), (true, 1)]
def certA1D3 : KillCert := .w8 [.b] (0, 2) (1, 0) (2, 1) (2, 1) [(false, 0), (true, 1)]
def certB1B2 : KillCert := .w4 [.ai] (2, 0) (2, 1) [(false, 0), (false, 1)]
def certB1B3 : KillCert := .w8 [.ai, .ai, .b] (1, 0) (2, 0) (2, 0) (1, 2) [(true, 0), (true, 1), (true, 1)]
def certB1D3 : KillCert := .w8 [.ai, .b] (0, 2) (1, 0) (2, 0) (2, 1) [(false, 0), (false, 1)]
def certB1A2A3 : KillCert := .w8 [.ai, .b, .b] (0, 2) (0, 1) (2, 1) (2, 1) [(false, 0), (true, 1), (true, 2)]
def certD1A3 : KillCert := .w8 [.a, .bi, .a] (0, 1) (2, 1) (2, 0) (1, 2) [(false, 0), (true, 1)]
def certD1B3 : KillCert := .w8 [.ai, .b] (0, 2) (0, 2) (1, 0) (2, 1) [(false, 0), (false, 1)]

private theorem ok_D2_eq : normEq wD2 (wordInv wD1) = true := by decide
private theorem ok_A1A3 : checkKill [wA1, wA3] certA1A3 = true := by decide
private theorem ok_A1B3 : checkKill [wA1, wB3] certA1B3 = true := by decide
private theorem ok_A1D3 : checkKill [wA1, wD3] certA1D3 = true := by decide
private theorem ok_B1B2 : checkKill [wB1, wB2] certB1B2 = true := by decide
private theorem ok_B1B3 : checkKill [wB1, wB3] certB1B3 = true := by decide
private theorem ok_B1D3 : checkKill [wB1, wD3] certB1D3 = true := by decide
private theorem ok_B1A2A3 : checkKill [wB1, wA2, wA3] certB1A2A3 = true := by decide
private theorem ok_D1A3 : checkKill [wD1, wA3] certD1A3 = true := by decide
private theorem ok_D1B3 : checkKill [wD1, wB3] certD1B3 = true := by decide

set_option maxHeartbeats 400000 in
private theorem ok_W1 : checkCycle16 [] seqW1 [] certsW1 [wA1, wB1, wD1] = true :=
  checkCycle16_of_parts [] seqW1 [] certsW1 [wA1, wB1, wD1]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxHeartbeats 800000 in
private theorem ok_dih :
    checkCycle16 [wD1, wD3, wD1b, wD3b] seqDih
      [(false, 1), (true, 3), (true, 0), (true, 0)] certsDih [] = true :=
  checkCycle16_of_parts [wD1, wD3, wD1b, wD3b] seqDih
    [(false, 1), (true, 3), (true, 0), (true, 0)] certsDih []
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by
      simp only [dist34D, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
      exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩)

set_option maxHeartbeats 400000 in
private theorem ok_W3 :
    checkCycle16 [wD1, wD3, wCmb, wCmbi] seqW3 [] certsW3 [wC00] = true :=
  checkCycle16_of_parts [wD1, wD3, wCmb, wCmbi] seqW3 [] certsW3 [wC00]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxHeartbeats 400000 in
private theorem ok_1b :
    checkCycle16 [wD1, wD3, wCmb, wCmbi, wC00] seq1b
      [(false, 1), (true, 0), (false, 2), (true, 3), (true, 4)] certs1b [] = true :=
  checkCycle16_of_parts [wD1, wD3, wCmb, wCmbi, wC00] seq1b
    [(false, 1), (true, 0), (false, 2), (true, 3), (true, 4)] certs1b []
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/- ## Section 6: Graph-isomorphic views and main metabelian theorem -/

private def biGraph_iso_swapA {K : Type*} (X : Type*) [Group K] [MulAction K X] (a b : K) :
    biGraph X a⁻¹ (a⁻¹ * b) ≃g biGraph X a b := by
  let e : Bool × X ≃ Bool × X :=
    { toFun := fun u => if u.1 then (true, a • u.2) else (false, u.2)
      invFun := fun u => if u.1 then (true, a⁻¹ • u.2) else (false, u.2)
      left_inv := fun ⟨fl, x⟩ => by cases fl <;> simp
      right_inv := fun ⟨fl, x⟩ => by cases fl <;> simp }
  refine ⟨e, ?_⟩
  intro u v
  rcases u with ⟨bu, xu⟩
  rcases v with ⟨bv, xv⟩
  cases bu <;> cases bv <;> simp only [biGraph, SimpleGraph.fromRel_adj, e, Equiv.coe_fn_mk,
    Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, false_and, true_and, and_false,
    or_false, false_or, ne_eq, Prod.mk.injEq, not_false_eq_true]
  · constructor
    · rintro (h | h | h)
      · right; left
        have h' := congrArg (a⁻¹ • ·) h
        simpa [inv_smul_smul] using h'
      · left
        have h' := congrArg (a⁻¹ • ·) h
        simpa [inv_smul_smul] using h'
      · right; right
        have h' := congrArg (a⁻¹ • ·) h
        simpa [mul_smul, inv_smul_smul] using h'
    · rintro (h | h | h)
      · right; left; exact congrArg (a • ·) h
      · left; rw [h, smul_inv_smul]
      · right; right; rw [h, mul_smul, smul_inv_smul]
  · constructor
    · rintro (h | h | h)
      · right; left
        have h' := congrArg (a⁻¹ • ·) h
        simpa [inv_smul_smul] using h'
      · left
        have h' := congrArg (a⁻¹ • ·) h
        simpa [inv_smul_smul] using h'
      · right; right
        have h' := congrArg (a⁻¹ • ·) h
        simpa [mul_smul, inv_smul_smul] using h'
    · rintro (h | h | h)
      · right; left; exact congrArg (a • ·) h
      · left; rw [h, smul_inv_smul]
      · right; right; rw [h, mul_smul, smul_inv_smul]

private def biGraph_iso_flip {K : Type*} (X : Type*) [Group K] [MulAction K X] (a b : K) :
    biGraph X a⁻¹ b⁻¹ ≃g biGraph X a b := by
  let e : Bool × X ≃ Bool × X :=
    { toFun := fun u => (!u.1, u.2)
      invFun := fun u => (!u.1, u.2)
      left_inv := fun ⟨fl, x⟩ => by cases fl <;> rfl
      right_inv := fun ⟨fl, x⟩ => by cases fl <;> rfl }
  refine ⟨e, ?_⟩
  intro u v
  rcases u with ⟨bu, xu⟩
  rcases v with ⟨bv, xv⟩
  cases bu <;> cases bv <;> simp only [biGraph, SimpleGraph.fromRel_adj, e, Equiv.coe_fn_mk,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false,
    false_and, true_and, and_false, or_false, false_or,
    ne_eq, Prod.mk.injEq, not_false_eq_true]
  · constructor
    · rintro (h | h | h)
      · left; exact h.symm
      · right; left; rw [h, inv_smul_smul]
      · right; right; rw [h, inv_smul_smul]
    · rintro (h | h | h)
      · left; exact h.symm
      · right; left; rw [h, smul_inv_smul]
      · right; right; rw [h, smul_inv_smul]
  · constructor
    · rintro (h | h | h)
      · left; exact h.symm
      · right; left; rw [h, inv_smul_smul]
      · right; right; rw [h, inv_smul_smul]
    · rintro (h | h | h)
      · left; exact h.symm
      · right; left; rw [h, smul_inv_smul]
      · right; right; rw [h, smul_inv_smul]

private lemma copy_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (iso : G ≃g H) {n : ℕ} (h : cycleGraph n ⊑ G) : cycleGraph n ⊑ H := by
  obtain ⟨c⟩ := h
  exact ⟨iso.toEmbedding.toCopy.comp c⟩

private lemma view1_survivors {K X B : Type*} [Group K] [MulAction K X] [AddCommGroup B]
    (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (ha2 : a * a ∈ f.ker)
    (hsep : ∀ z : X, a • z ≠ z ∧ b • z ≠ z ∧ a • z ≠ b • z)
    (y : X) (hnc : a • (b • y) ≠ b • (a • y))
    (hno4 : ¬ cycleGraph 4 ⊑ biGraph X a b)
    (hno8 : ¬ cycleGraph 8 ⊑ biGraph X a b)
    (hno16 : ¬ cycleGraph 16 ⊑ biGraph X a b) :
    evalWord a b wA1 • y = y ∨ evalWord a b wB1 • y = y ∨ evalWord a b wD1 • y = y := by
  have h := cycle16_sound f hker a b ha2 hsep y hnc hno4 hno8 hno16
    (H := []) (by simp) ok_W1
  rcases h with ⟨s, hs, hfix⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact Or.inl hfix
  · exact Or.inr (Or.inl hfix)
  · exact Or.inr (Or.inr hfix)

private lemma D1_D3_of_noncomm {K X B : Type*} [Group K] [MulAction K X] [AddCommGroup B]
    (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (ha2 : a * a ∈ f.ker)
    (hsep : ∀ z : X, a • z ≠ z ∧ b • z ≠ z ∧ a • z ≠ b • z)
    (y : X) (hnc : a • (b • y) ≠ b • (a • y))
    (hno4 : ¬ cycleGraph 4 ⊑ biGraph X a b)
    (hno8 : ¬ cycleGraph 8 ⊑ biGraph X a b)
    (hno16 : ¬ cycleGraph 16 ⊑ biGraph X a b) :
    evalWord a b wD1 • y = y ∧ evalWord a b wD3 • y = y := by
  have hv1 := view1_survivors f hker a b ha2 hsep y hnc hno4 hno8 hno16
  have hai2 : a⁻¹ * a⁻¹ ∈ f.ker := by
    have h : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
    rw [h]; exact f.ker.inv_mem ha2
  have hsep2 : ∀ z : X, a⁻¹ • z ≠ z ∧ (a⁻¹ * b) • z ≠ z ∧ a⁻¹ • z ≠ (a⁻¹ * b) • z := by
    intro z
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have h' := congrArg (a • ·) h
      rw [smul_inv_smul] at h'
      exact (hsep z).1 h'.symm
    · intro h
      rw [mul_smul] at h
      have h' := congrArg (a • ·) h
      rw [smul_inv_smul] at h'
      exact (hsep z).2.2 h'.symm
    · intro h
      rw [mul_smul] at h
      exact (hsep z).2.1 (by
        have h' := congrArg (a • ·) h
        simpa [smul_inv_smul] using h'.symm)
  have hnc2 : a⁻¹ • ((a⁻¹ * b) • (a • y)) ≠ (a⁻¹ * b) • (a⁻¹ • (a • y)) := by
    intro h
    rw [inv_smul_smul, mul_smul, mul_smul] at h
    have h1 := congrArg (a • ·) h
    simp only [smul_inv_smul] at h1
    have h2 := congrArg (a • ·) h1
    simp only [smul_inv_smul] at h2
    exact hnc h2.symm
  have iso2 := biGraph_iso_swapA X a b
  have hv2_raw := view1_survivors f hker a⁻¹ (a⁻¹ * b) hai2 hsep2 (a • y) hnc2
    (fun h => hno4 (copy_of_iso iso2 h))
    (fun h => hno8 (copy_of_iso iso2 h))
    (fun h => hno16 (copy_of_iso iso2 h))
  have translate2 : ∀ w : Word,
      evalWord a⁻¹ (a⁻¹ * b) w • (a • y) = a • y →
      evalWord a b (wordConj [.a] (substWord [.ai] [.ai, .b] w)) • y = y := by
    intro w hw
    have hsub : evalWord a⁻¹ (a⁻¹ * b) w = evalWord a b (substWord [.ai] [.ai, .b] w) := by
      have ha_eq : evalWord a b [.ai] = a⁻¹ := by simp [evalWord, evalLetter]
      have hb_eq : evalWord a b [.ai, .b] = a⁻¹ * b := by simp [evalWord, evalLetter]
      simpa [ha_eq, hb_eq] using evalWord_subst a b [.ai] [.ai, .b] w
    rw [evalWord_conj, mul_smul, mul_smul, ← hsub]
    have hs : evalWord a b [.a] = a := by simp [evalWord, evalLetter]
    rw [hs, hw, inv_smul_smul]
  have hv2 : evalWord a b wA2 • y = y ∨ evalWord a b wB2 • y = y ∨ evalWord a b wD1 • y = y := by
    rcases hv2_raw with h | h | h
    · exact Or.inl (translate2 wA1 h)
    · exact Or.inr (Or.inl (translate2 wB1 h))
    · right; right
      have hd2 : evalWord a b wD2 • y = y := translate2 wD1 h
      have heq := evalWord_eq_of_normEq f hker a b ha2 ok_D2_eq
      rw [heq, evalWord_inv] at hd2
      have h1 := congrArg (evalWord a b wD1 • ·) hd2
      simpa [smul_inv_smul] using h1.symm
  have hsep3 : ∀ z : X, a⁻¹ • z ≠ z ∧ b⁻¹ • z ≠ z ∧ a⁻¹ • z ≠ b⁻¹ • z := by
    intro z
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have h' := congrArg (a • ·) h
      rw [smul_inv_smul] at h'
      exact (hsep z).1 h'.symm
    · intro h
      have h' := congrArg (b • ·) h
      rw [smul_inv_smul] at h'
      exact (hsep z).2.1 h'.symm
    · intro h
      let w := a⁻¹ • z
      have ha : a • w = z := smul_inv_smul _ z
      have hb : b • w = z := by change b • (a⁻¹ • z) = z; rw [h, smul_inv_smul]
      exact (hsep w).2.2 (ha.trans hb.symm)
  have hnc3 : a⁻¹ • (b⁻¹ • ((a * b) • y)) ≠ b⁻¹ • (a⁻¹ • ((a * b) • y)) := by
    intro h
    simp only [mul_smul, inv_smul_smul] at h
    have h1 := congrArg (a • ·) h
    rw [smul_inv_smul] at h1
    have h2 := congrArg (b • ·) h1
    rw [smul_inv_smul] at h2
    exact hnc h2
  let iso3 := biGraph_iso_flip X a b
  have hv3_raw := view1_survivors f hker a⁻¹ b⁻¹ hai2 hsep3 ((a * b) • y) hnc3
    (fun h => hno4 (copy_of_iso iso3 h))
    (fun h => hno8 (copy_of_iso iso3 h))
    (fun h => hno16 (copy_of_iso iso3 h))
  have translate3 : ∀ w : Word,
      evalWord a⁻¹ b⁻¹ w • ((a * b) • y) = (a * b) • y →
      evalWord a b (wordConj [.a, .b] (substWord [.ai] [.bi] w)) • y = y := by
    intro w hw
    have hsub : evalWord a⁻¹ b⁻¹ w = evalWord a b (substWord [.ai] [.bi] w) := by
      have ha_eq : evalWord a b [.ai] = a⁻¹ := by simp [evalWord, evalLetter]
      have hb_eq : evalWord a b [.bi] = b⁻¹ := by simp [evalWord, evalLetter]
      simpa [ha_eq, hb_eq] using evalWord_subst a b [.ai] [.bi] w
    rw [evalWord_conj, mul_smul, mul_smul, ← hsub]
    have hs : evalWord a b [.a, .b] = a * b := by simp [evalWord, evalLetter]
    rw [hs, hw, inv_smul_smul]
  have hv3 : evalWord a b wA3 • y = y ∨ evalWord a b wB3 • y = y ∨ evalWord a b wD3 • y = y := by
    rcases hv3_raw with h | h | h
    · exact Or.inl (translate3 wA1 h)
    · exact Or.inr (Or.inl (translate3 wB1 h))
    · exact Or.inr (Or.inr (translate3 wD1 h))
  have hkill2 : ∀ {w1 w2 : Word} {c : KillCert},
      evalWord a b w1 • y = y → evalWord a b w2 • y = y →
      checkKill [w1, w2] c = true → False := by
    intro w1 w2 c h1 h2 hc
    exact kill_sound f hker a b ha2 hsep y hnc hno4 hno8
      (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> assumption) hc
  have hkill3 : ∀ {w1 w2 w3 : Word} {c : KillCert},
      evalWord a b w1 • y = y → evalWord a b w2 • y = y → evalWord a b w3 • y = y →
      checkKill [w1, w2, w3] c = true → False := by
    intro w1 w2 w3 c h1 h2 h3 hc
    exact kill_sound f hker a b ha2 hsep y hnc hno4 hno8
      (by intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> assumption) hc
  rcases hv1 with hA1 | hB1 | hD1
  · rcases hv3 with hA3 | hB3 | hD3
    · exact (hkill2 hA1 hA3 ok_A1A3).elim
    · exact (hkill2 hA1 hB3 ok_A1B3).elim
    · exact (hkill2 hA1 hD3 ok_A1D3).elim
  · rcases hv3 with hA3 | hB3 | hD3
    · rcases hv2 with hA2 | hB2 | hD1
      · exact (hkill3 hB1 hA2 hA3 ok_B1A2A3).elim
      · exact (hkill2 hB1 hB2 ok_B1B2).elim
      · exact (hkill2 hD1 hA3 ok_D1A3).elim
    · exact (hkill2 hB1 hB3 ok_B1B3).elim
    · exact (hkill2 hB1 hD3 ok_B1D3).elim
  · rcases hv3 with hA3 | hB3 | hD3
    · exact (hkill2 hD1 hA3 ok_D1A3).elim
    · exact (hkill2 hD1 hB3 ok_D1B3).elim
    · exact ⟨hD1, hD3⟩

private theorem metabelian_involution_cycle {K X B : Type*} [Group K] [MulAction K X]
    [AddCommGroup B]
    (f : K →* Multiplicative B) (hker : ∀ i j : f.ker, i * j = j * i)
    (a b : K) (ha2 : a * a ∈ f.ker)
    (hsep : ∀ z : X, a • z ≠ z ∧ b • z ≠ z ∧ a • z ≠ b • z)
    (y : X) (hnc : a • (b • y) ≠ b • (a • y)) :
    cycleGraph 4 ⊑ biGraph X a b ∨ cycleGraph 8 ⊑ biGraph X a b ∨ cycleGraph 16 ⊑ biGraph X a b := by
  by_cases hno4 : cycleGraph 4 ⊑ biGraph X a b
  · exact Or.inl hno4
  by_cases hno8 : cycleGraph 8 ⊑ biGraph X a b
  · exact Or.inr (Or.inl hno8)
  by_cases hno16 : cycleGraph 16 ⊑ biGraph X a b
  · exact Or.inr (Or.inr hno16)
  exfalso
  have hconj_b : ∀ {w : Word} {z : X}, evalWord a b w • (b • z) = b • z →
      evalWord a b (wordConj [.b] w) • z = z := by
    intro w z hz
    rw [evalWord_conj, mul_smul, mul_smul]
    have hb : evalWord a b [.b] = b := by simp [evalWord, evalLetter]
    rw [hb, hz, inv_smul_smul]
  have hconj_bi : ∀ {w : Word} {z : X}, evalWord a b w • (b⁻¹ • z) = b⁻¹ • z →
      evalWord a b (wordConj [.bi] w) • z = z := by
    intro w z hz
    rw [evalWord_conj, mul_smul, mul_smul]
    have hbi : evalWord a b [.bi] = b⁻¹ := by simp [evalWord, evalLetter]
    rw [hbi, hz, inv_smul_smul]
  have hcomm_of_eq : ∀ {z : X}, a • (b • z) = b • (a • z) → evalWord a b commWord • z = z := by
    intro z hz
    simp only [commWord, evalWord, evalLetter, mul_one, mul_smul]
    rw [← hz, inv_smul_smul, inv_smul_smul]
  have kill_consec : ∀ z : X, a • (b • z) ≠ b • (a • z) →
      a • (b • (b • z)) ≠ b • (a • (b • z)) → False := by
    intro z hnc_z hnc_bz
    obtain ⟨hD1z, hD3z⟩ := D1_D3_of_noncomm f hker a b ha2 hsep z hnc_z hno4 hno8 hno16
    obtain ⟨hD1bz, hD3bz⟩ := D1_D3_of_noncomm f hker a b ha2 hsep (b • z) hnc_bz hno4 hno8 hno16
    have hH : ∀ w ∈ [wD1, wD3, wD1b, wD3b], evalWord a b w • z = z := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact hD1z
      · exact hD3z
      · exact hconj_b hD1bz
      · exact hconj_b hD3bz
    obtain ⟨s, hs, _⟩ := cycle16_sound f hker a b ha2 hsep z hnc_z hno4 hno8 hno16 hH ok_dih
    simp at hs
  by_cases hby : a • (b • (b • y)) = b • (a • (b • y))
  · by_cases hbiy : a • (b • (b⁻¹ • y)) = b • (a • (b⁻¹ • y))
    · obtain ⟨hD1, hD3⟩ := D1_D3_of_noncomm f hker a b ha2 hsep y hnc hno4 hno8 hno16
      have hCmb : evalWord a b wCmb • y = y := hconj_b (hcomm_of_eq hby)
      have hCmbi : evalWord a b wCmbi • y = y := hconj_bi (hcomm_of_eq hbiy)
      have hH3 : ∀ w ∈ [wD1, wD3, wCmb, wCmbi], evalWord a b w • y = y := by
        intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl <;> assumption
      obtain ⟨s, hs, hC00⟩ := cycle16_sound f hker a b ha2 hsep y hnc hno4 hno8 hno16 hH3 ok_W3
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs
      have hH1b : ∀ w ∈ [wD1, wD3, wCmb, wCmbi, wC00], evalWord a b w • y = y := by
        intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
      obtain ⟨s', hs', _⟩ := cycle16_sound f hker a b ha2 hsep y hnc hno4 hno8 hno16 hH1b ok_1b
      simp at hs'
    · have hnc_bi_next : a • (b • (b • (b⁻¹ • y))) ≠ b • (a • (b • (b⁻¹ • y))) := by
        simpa [smul_inv_smul] using hnc
      exact kill_consec (b⁻¹ • y) hbiy hnc_bi_next
  · exact kill_consec y hnc hby

/- ## Section 7: Connecting to the step statement `H2` -/

private def biGraph_iso_perm {X : Type*} (p q : Equiv.Perm X)
    (σ : Equiv.Perm (Fin 3)) :
    let K := Subgroup.closure ({p, q} : Set (Equiv.Perm X))
    let s : Fin 3 → K := ![1, ⟨p, Subgroup.subset_closure (by simp)⟩,
      ⟨q, Subgroup.subset_closure (by simp)⟩]
    let a : K := s (σ 1) * (s (σ 0))⁻¹
    let b : K := s (σ 2) * (s (σ 0))⁻¹
    biGraph X a b ≃g SimpleGraph.fromRel (fun u v : Bool × X =>
      u.1 = false ∧ v.1 = true ∧ (v.2 = u.2 ∨ v.2 = p u.2 ∨ v.2 = q u.2)) := by
  intro K s a b
  let s0 := s (σ 0)
  let e : Bool × X ≃ Bool × X :=
    { toFun := fun u => if u.1 then (true, u.2) else (false, s0⁻¹ • u.2)
      invFun := fun u => if u.1 then (true, u.2) else (false, s0 • u.2)
      left_inv := fun ⟨fl, x⟩ => by cases fl <;> simp
      right_inv := fun ⟨fl, x⟩ => by cases fl <;> simp }
  have hmem_iff : ∀ x y : X,
      (y = s0 • x ∨ y = s (σ 1) • x ∨ y = s (σ 2) • x) ↔
      (y = x ∨ y = p x ∨ y = q x) := by
    intro x y
    have h1 : (y = s0 • x ∨ y = s (σ 1) • x ∨ y = s (σ 2) • x) ↔
        ∃ i : Fin 3, y = s (σ i) • x := by
      constructor
      · rintro (h | h | h)
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
        · exact ⟨2, h⟩
      · rintro ⟨i, hi⟩
        fin_cases i
        · exact Or.inl hi
        · exact Or.inr (Or.inl hi)
        · exact Or.inr (Or.inr hi)
    have h2 : (y = x ∨ y = p x ∨ y = q x) ↔ ∃ j : Fin 3, y = s j • x := by
      constructor
      · rintro (h | h | h)
        · exact ⟨0, by simpa [s] using h⟩
        · exact ⟨1, by simpa [s] using h⟩
        · exact ⟨2, by simpa [s] using h⟩
      · rintro ⟨j, hj⟩
        fin_cases j
        · exact Or.inl (by simpa [s] using hj)
        · exact Or.inr (Or.inl (by simpa [s] using hj))
        · exact Or.inr (Or.inr (by simpa [s] using hj))
    rw [h1, h2]
    exact ⟨fun ⟨i, hi⟩ => ⟨σ i, hi⟩, fun ⟨j, hj⟩ => ⟨σ.symm j, by simpa using hj⟩⟩
  have hrel : ∀ x y : X,
      (y = x ∨ y = a • x ∨ y = b • x) ↔
      (y = s0⁻¹ • x ∨ y = p (s0⁻¹ • x) ∨ y = q (s0⁻¹ • x)) := by
    intro x y
    rw [← hmem_iff (s0⁻¹ • x) y]
    have h0 : s0 • (s0⁻¹ • x) = x := smul_inv_smul s0 x
    have h1 : s (σ 1) • (s0⁻¹ • x) = a • x := by simp [a, s0, mul_smul]
    have h2 : s (σ 2) • (s0⁻¹ • x) = b • x := by simp [b, s0, mul_smul]
    rw [h0, h1, h2]
  refine ⟨e, ?_⟩
  intro u v
  rcases u with ⟨bu, xu⟩
  rcases v with ⟨bv, xv⟩
  cases bu <;> cases bv <;> simp only [biGraph, SimpleGraph.fromRel_adj, e, Equiv.coe_fn_mk,
    Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, false_and, true_and, and_false,
    or_false, false_or, ne_eq, Prod.mk.injEq, not_false_eq_true]
  · exact (hrel xu xv).symm
  · exact (hrel xv xu).symm

private lemma not_commute_ab {X : Type*} (p q : Equiv.Perm X) (σ : Equiv.Perm (Fin 3))
    (hnc : p * q ≠ q * p) :
    let K := Subgroup.closure ({p, q} : Set (Equiv.Perm X))
    let s : Fin 3 → K := ![1, ⟨p, Subgroup.subset_closure (by simp)⟩,
      ⟨q, Subgroup.subset_closure (by simp)⟩]
    let a : K := s (σ 1) * (s (σ 0))⁻¹
    let b : K := s (σ 2) * (s (σ 0))⁻¹
    a * b ≠ b * a := by
  intro K s a b hcomm
  have hval : (a : Equiv.Perm X) * (b : Equiv.Perm X) =
      (b : Equiv.Perm X) * (a : Equiv.Perm X) := congrArg Subtype.val hcomm
  have h01 : σ 0 ≠ σ 1 := fun h => by have := σ.injective h; omega
  have h02 : σ 0 ≠ σ 2 := fun h => by have := σ.injective h; omega
  have h12 : σ 1 ≠ σ 2 := fun h => by have := σ.injective h; omega
  have hpq : p * q = q * p := by
    have ha : (a : Equiv.Perm X) = (s (σ 1) : Equiv.Perm X) * (s (σ 0) : Equiv.Perm X)⁻¹ := rfl
    have hb : (b : Equiv.Perm X) = (s (σ 2) : Equiv.Perm X) * (s (σ 0) : Equiv.Perm X)⁻¹ := rfl
    rw [ha, hb] at hval
    generalize hσ0 : σ 0 = i0 at h01 h02 hval
    generalize hσ1 : σ 1 = i1 at h01 h12 hval
    generalize hσ2 : σ 2 = i2 at h02 h12 hval
    fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;>
      simp [s] at hval <;>
      first
      | exact (h01 rfl).elim
      | exact (h02 rfl).elim
      | exact (h12 rfl).elim
      | exact hval
      | exact hval.symm
      | (have h1 : p⁻¹ * q = q * p⁻¹ := mul_right_cancel (by simpa [mul_assoc] using hval)
         calc p * q = p * (q * p⁻¹) * p := by group
           _ = p * (p⁻¹ * q) * p := by rw [← h1]
           _ = q * p := by group)
      | (have h1 : q * p⁻¹ = p⁻¹ * q := mul_right_cancel (by simpa [mul_assoc] using hval)
         calc p * q = p * (q * p⁻¹) * p := by group
           _ = p * (p⁻¹ * q) * p := by rw [h1]
           _ = q * p := by group)
      | (have h1 : q⁻¹ * p = p * q⁻¹ := mul_right_cancel (by simpa [mul_assoc] using hval)
         calc p * q = q * (q⁻¹ * p) * q := by group
           _ = q * (p * q⁻¹) * q := by rw [h1]
           _ = q * p := by group)
      | (have h1 : p * q⁻¹ = q⁻¹ * p := mul_right_cancel (by simpa [mul_assoc] using hval)
         calc p * q = q * (q⁻¹ * p) * q := by group
           _ = q * (p * q⁻¹) * q := by rw [← h1]
           _ = q * p := by group)
  exact hnc hpq

end MetabelianInvolutionProof

theorem OMA.solution : OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H2_R1.H2 := by
  intro X _ _ p q hsep hdens _ _ K s B _ f _ hker σ h _ hinv _ _
  classical
  let a : K := s (σ 1) * (s (σ 0))⁻¹
  let b : K := s (σ 2) * (s (σ 0))⁻¹
  have ha2 : a * a ∈ f.ker := by
    change f (a * a) = 1
    apply Multiplicative.toAdd.injective
    have hfa : (f a).toAdd = h := by
      simp only [a, h, map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
    simpa [map_mul, toAdd_mul, hfa] using hinv
  have hsep_ab : ∀ z : X, a • z ≠ z ∧ b • z ≠ z ∧ a • z ≠ b • z := by
    intro z
    let w := (s (σ 0))⁻¹ • z
    have hs_inj : ∀ i j : Fin 3, s i • w = s j • w → i = j := by
      intro i j hij
      obtain ⟨hp, hq, hpq⟩ := hsep w
      fin_cases i <;> fin_cases j <;> simp [s] at hij ⊢
      · exact (hp hij.symm).elim
      · exact (hq hij.symm).elim
      · exact (hp hij).elim
      · exact (hpq hij).elim
      · exact (hq hij).elim
      · exact (hpq hij.symm).elim
    have h0 : s (σ 0) • w = z := smul_inv_smul _ z
    have h1 : s (σ 1) • w = a • z := by simp [a, w, mul_smul]
    have h2 : s (σ 2) • w = b • z := by simp [b, w, mul_smul]
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have h01 := σ.injective (hs_inj (σ 1) (σ 0) (by rw [h1, h0, h]))
      omega
    · intro h
      have h02 := σ.injective (hs_inj (σ 2) (σ 0) (by rw [h2, h0, h]))
      omega
    · intro h
      have h12 := σ.injective (hs_inj (σ 1) (σ 2) (by rw [h1, h2, h]))
      omega
  have hpq_ne : p * q ≠ q * p := by
    have hpos : 0 < ({x : X | p (q x) ≠ q (p x)} : Set X).ncard := by
      have hcard : 0 < Fintype.card X := Fintype.card_pos
      omega
    obtain ⟨x₀, hx₀⟩ := Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt hpos)
    intro heq
    apply hx₀
    exact DFunLike.congr_fun heq x₀
  have hab_ne : a * b ≠ b * a := MetabelianInvolutionProof.not_commute_ab p q σ hpq_ne
  have hval_ne : ((a * b : K) : Equiv.Perm X) ≠ ((b * a : K) : Equiv.Perm X) :=
    fun h => hab_ne (Subtype.ext h)
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp hval_ne
  have hnc : a • (b • y) ≠ b • (a • y) := by
    simpa [Subgroup.coe_mul, Equiv.Perm.mul_apply, Subgroup.smul_def, Equiv.Perm.smul_def] using hy
  let hiso := MetabelianInvolutionProof.biGraph_iso_perm p q σ
  rcases MetabelianInvolutionProof.metabelian_involution_cycle f hker a b ha2 hsep_ab y hnc with
    h4 | h8 | h16
  · exact ⟨2, by decide, MetabelianInvolutionProof.copy_of_iso hiso h4⟩
  · exact ⟨3, by decide, MetabelianInvolutionProof.copy_of_iso hiso h8⟩
  · exact ⟨4, by decide, MetabelianInvolutionProof.copy_of_iso hiso h16⟩
