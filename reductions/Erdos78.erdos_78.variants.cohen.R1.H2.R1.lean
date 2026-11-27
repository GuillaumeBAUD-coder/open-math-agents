import OMAReductions.R_Erdos78_erdos_78_variants_cohen_R1

/-!
# The encoding step for Cohen's Ramsey graph

A unary dimension and two binary labels are supplied to the graph oracle.
The first hypothesis asks for a machine on raw strings that converts this
input to three binary numbers, with the two labels in increasing order.
The second asks for composition of decision machines when the intermediate
string has at most twice the original length. The length estimate below
accounts for the delimiters in the canonical encodings.
-/

open BitstringEncoding Computability ComplexityTheory Turing

namespace OMA.R_Erdos78_erdos_78_variants_cohen_R1_H2_R1

/-- A single raw bitstring transducer, including a fixed result on malformed inputs. -/
def H1 : Prop :=
  let t : List Bool → List Bool := fun raw =>
    match bitDecode (α := List Bool × ℕ × ℕ) raw with
    | some p => bitEncode (p.1.length, min p.2.1 p.2.2, max p.2.1 p.2.2)
    | none => []
  Nonempty (TM2ComputableInPolyTime id id t)

/-- Compose a preprocessing machine with a Boolean decision machine when
the size of the intermediate string is bounded linearly on valid inputs. -/
def H2 : Prop :=
  ∀ (A B : Type) (ea : A → List Bool) (eb : B → List Bool)
    (h : A → B) (f : B → Bool),
    Nonempty (TM2ComputableInPolyTime ea eb h) →
    Nonempty (TM2ComputableInPolyTime eb bitEncode f) →
    (∀ a, (eb (h a)).length ≤ 2 * (ea a).length) →
    Nonempty (TM2ComputableInPolyTime ea bitEncode (f ∘ h))

private lemma positiveBits (p : PosNum) : (encodePosNum p).length ≤ (p : ℕ) := by
  induction p with
  | one => decide
  | bit0 p ih =>
    simp only [encodePosNum, List.length_cons, PosNum.cast_bit0]
    have hp := PosNum.to_nat_pos p
    omega
  | bit1 p ih =>
    simp only [encodePosNum, List.length_cons, PosNum.cast_bit1]
    omega

private lemma natBits (n : ℕ) : (bitEncode n).length ≤ n := by
  change (encodeNum (n : Num)).length ≤ n
  calc
    _ ≤ ((n : Num) : ℕ) := by
      generalize (n : Num) = b
      cases b with
      | zero => decide
      | pos p => exact positiveBits p
    _ = n := Num.to_of_nat n

private lemma pairBits {A B : Type} [BitstringEncoding A] [BitstringEncoding B]
    (a : A) (b : B) :
    (bitEncode (a, b)).length = 2 * (bitEncode a).length + 1 + (bitEncode b).length := by
  change (delimit (bitEncode a) ++ bitEncode b).length = _
  rw [List.length_append, length_delimit]

private lemma listBits (s : List Bool) : (bitEncode s).length = 3 * s.length := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    change (bitEncode s).length + 3 = 3 * (s.length + 1)
    omega

private lemma intermediate_length (s : List Bool) (u v : ℕ) :
    (bitEncode (s.length, min u v, max u v)).length ≤ 2 * (bitEncode (s, u, v)).length := by
  simp only [pairBits, listBits]
  have hs := natBits s.length
  rcases le_total u v with h | h
  · rw [min_eq_left h, max_eq_right h]
    omega
  · rw [min_eq_right h, max_eq_left h]
    omega

theorem main : H1 → H2 → OMA.R_Erdos78_erdos_78_variants_cohen_R1.H2 := by
  intro raw compose f hf
  let h : List Bool × ℕ × ℕ → ℕ × ℕ × ℕ := fun p =>
    (p.1.length, min p.2.1 p.2.2, max p.2.1 p.2.2)
  let t : List Bool → List Bool := fun b =>
    match bitDecode (α := List Bool × ℕ × ℕ) b with
    | some p => bitEncode (h p)
    | none => []
  change Nonempty (TM2ComputableInPolyTime id id t) at raw
  obtain ⟨machine⟩ := raw
  have adapted : Nonempty (TM2ComputableInPolyTime bitEncode bitEncode h) := by
    refine ⟨⟨machine.toTM2ComputableAux, machine.time, ?_⟩⟩
    intro x
    have out := machine.outputsFun (bitEncode x)
    simpa only [id_eq, t, bitDecode_bitEncode] using out
  refine ⟨f ∘ h, ?_, fun _ _ _ => rfl⟩
  exact compose _ _ bitEncode bitEncode h f adapted hf
    (fun x => intermediate_length x.1 x.2.1 x.2.2)

end OMA.R_Erdos78_erdos_78_variants_cohen_R1_H2_R1
