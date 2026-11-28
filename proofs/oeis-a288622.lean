import OMAStatements.S_oeis_a288622

open OMA.S_oeis_a288622

namespace MSLWord
inductive B
  | a | b | c
def block : B → List Bool
  | .a => [true]
  | .b => [false,true]
  | .c => [false,false,true]
def image : B → List B
  | .a => [.b]
  | .b => [.c]
  | .c => [.b,.a,.c]
def enc : List B → List Bool
  | [] => []
  | b::bs => block b ++ enc bs
def step : List B → List B
  | [] => []
  | b::bs => image b ++ step bs
theorem enc_append (u v : List B) : enc (u++v) = enc u ++ enc v := by
  induction u with
  | nil => rfl
  | cons b bs ih => simp [enc, ih, List.append_assoc]
theorem step_append (u v : List B) : step (u++v) = step u ++ step v := by
  induction u with
  | nil => rfl
  | cons b bs ih => simp [step, ih, List.append_assoc]
theorem scan_enc (u : List B) : scan (enc u ++ [false]) = enc (step u) ++ [false] := by
  induction u with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp only [enc, step, block, image, enc_append, List.cons_append, List.nil_append, List.append_assoc, scan, ih]
def blocks : ℕ → List B
  | 0 => [.b,.a]
  | n+1 => step (blocks n)
theorem word_blocks (n : ℕ) : word (n+1) = enc (blocks n) ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change scan (word (n+1)) = enc (step (blocks n)) ++ [false]
    rw [ih, scan_enc]
theorem recurrence (u : List B) :
    (enc (step (step (step (step u))))).length + (enc u).length =
      2 * (enc (step (step (step u)))).length := by
  induction u with
  | nil => decide
  | cons b bs ih =>
    have hb : (enc (step (step (step (step [b]))))).length + (enc [b]).length =
      2 * (enc (step (step (step [b])))).length := by cases b <;> decide
    change (enc (step (step (step (step ([b] ++ bs)))))).length + (enc ([b] ++ bs)).length =
      2 * (enc (step (step (step ([b] ++ bs))))).length
    simp only [step_append, enc_append, List.length_append]
    omega
theorem lenrec (n : ℕ) : (word (n+4)).length + (word n).length =
    2 * (word (n+3)).length := by
  cases n with
  | zero => decide
  | succ n =>
    rw [show n+1+4 = (n+4)+1 by omega, show n+1+3 = (n+3)+1 by omega]
    rw [word_blocks (n+4), word_blocks n, word_blocks (n+3)]
    simp only [List.length_append, List.length_cons, List.length_nil]
    change (enc (step (step (step (step (blocks n)))))).length + 1 +
      ((enc (blocks n)).length + 1) = 2 * ((enc (step (step (step (blocks n))))).length + 1)
    have h := recurrence (blocks n)
    omega
end MSLWord
theorem OMA.solution : type_of% @OMA.S_oeis_a288622.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 4
    · interval_cases n <;> decide
    · let k := n-4
      have hk : n = k+4 := by dsimp [k]; omega
      rw [hk]
      have h0 := ih k (by omega)
      have h3 := ih (k+3) (by omega)
      have h := MSLWord.lenrec k
      rw [a288465]
      omega
