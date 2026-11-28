import OMAStatements.S_oeis_a097602
import Mathlib

/-! Each block of nine steps has two squares. The first three increments and
the following six increments are each constant. -/
namespace Deldor14.SquareSteps
open Finset OMA.S_oeis_a097602
private noncomputable def hits (a : ℕ → ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((Icc 1 n).filter fun i => IsSquare (a i)).card

private lemma hits_succ (a : ℕ → ℕ) (n : ℕ) :
    hits a (n+1)=hits a n + if IsSquare (a (n+1)) then 1 else 0 := by
  classical
  have er : Icc 1 (n+1) = insert (n+1) (Icc 1 n) := by
    ext i; simp only [mem_Icc,mem_insert];omega
  have out : n+1 ∉ (Icc 1 n).filter (fun i => IsSquare (a i)) := by simp
  simp only [hits,er,filter_insert]
  split_ifs <;> simp [out]
private lemma gap {z x : ℕ} (low : x^2<z) (high : z<(x+1)^2) : ¬IsSquare z := by
  rintro ⟨y,rfl⟩
  rcases le_or_gt y x with h | h
  · nlinarith [Nat.mul_self_le_mul_self h]
  · nlinarith [Nat.mul_self_le_mul_self (show x+1≤y by omega)]
private def value (k t : ℕ) : ℕ :=
  if t≤3 then (3*k+1)^2+t*(2*k+1) else (3*k+2)^2+(t-3)*(2*k+2)
private lemma square_test (k t : ℕ) (ht : t≤9) :
    IsSquare (value k t) ↔ t=0 ∨ t=3 ∨ t=9 := by
  interval_cases t
  · simp only [value]; norm_num; exact ⟨3*k+1,by ring⟩
  · simp only [value]; norm_num; apply gap (x:=3*k+1) <;> nlinarith
  · simp only [value]; norm_num; apply gap (x:=3*k+1) <;> nlinarith
  · simp only [value]; norm_num; exact ⟨3*k+2,by ring⟩
  · simp only [value]; norm_num; apply gap (x:=3*k+2) <;> nlinarith
  · simp only [value]; norm_num; apply gap (x:=3*k+2) <;> nlinarith
  · simp only [value]; norm_num; apply gap (x:=3*k+3) <;> nlinarith
  · simp only [value]; norm_num; apply gap (x:=3*k+3) <;> nlinarith
  · simp only [value]; norm_num; apply gap (x:=3*k+3) <;> nlinarith
  · simp only [value]; norm_num; exact ⟨3*k+4,by ring⟩

private lemma inside (a : ℕ → ℕ) (ha : IsA097602 a) (k : ℕ)
    (start : a (9*k+1)=value k 0 ∧ hits a (9*k+1)=2*k+1)
    (t : ℕ) (ht : t≤9) :
    a (9*k+1+t)=value k t ∧ hits a (9*k+1+t)=
      (if t<3 then 2*k+1 else if t<9 then 2*k+2 else 2*k+3) := by
  induction t with
  | zero => simpa using start
  | succ t ih =>
    have prev := ih (by omega)
    have va := ha.2 (9*k+1+t) (by omega)
    change a (9*k+1+t+1)=a (9*k+1+t)+hits a (9*k+1+t) at va
    have v : a (9*k+1+(t+1)) = value k (t+1) := by
      rw [← Nat.add_assoc,va,prev.1,prev.2]
      have : t≤8 := by omega
      interval_cases t <;> norm_num [value] <;> ring
    refine ⟨v,?_⟩
    rw [←Nat.add_assoc,hits_succ,prev.2]
    change _+ (if IsSquare (a (9*k+1+(t+1))) then 1 else 0)=_
    rw [v]
    simp only [square_test k (t+1) ht]
    have bound : t≤8 := by omega
    interval_cases t <;> norm_num
private lemma start_blocks (a : ℕ → ℕ) (ha : IsA097602 a) (k : ℕ) :
    a (9*k+1)=value k 0 ∧ hits a (9*k+1)=2*k+1 := by
  induction k with
  | zero =>
    have h : IsSquare (a 1) := by rw [ha.1];exact ⟨1,rfl⟩
    have hs := hits_succ a 0
    simp only [zero_add,if_pos h] at hs
    have e : hits a 0 = 0 := by simp [hits]
    simp [value,ha.1,hs,e]
  | succ k ih =>
    have p := inside a ha k ih 9 (by decide)
    rw [show 9*(k+1)+1=9*k+1+9 by omega]
    constructor
    · rw [p.1];norm_num [value];ring
    · rw [p.2];norm_num;omega
theorem full : type_of% @OMA.S_oeis_a097602.main := by
  intro a ha m
  constructor
  · rintro ⟨n,hn,he⟩
    let k := (n-1)/9
    let t := (n-1)%9
    have ht : t<9 := Nat.mod_lt _ (by decide)
    have en : n=9*k+1+t := by dsimp [k,t];omega
    have p := (inside a ha k (start_blocks a ha k) t (by omega)).1
    rw [en,p] at he
    have hs : IsSquare (value k t) := ⟨m,by simpa [pow_two] using he⟩
    rcases (square_test k t (by omega)).mp hs with h | h | h
    · rw [h] at he
      have : m=3*k+1 := by norm_num [value] at he; nlinarith
      omega
    · rw [h] at he
      have : m=3*k+2 := by norm_num [value] at he; nlinarith
      omega
    · omega
  · intro hm
    let k:=m/3
    have hm' : m=3*k+1 ∨ m=3*k+2 := by dsimp [k];omega
    rcases hm' with h | h
    · refine ⟨9*k+1,by omega,?_⟩
      rw [(start_blocks a ha k).1,h];simp [value]
    · refine ⟨9*k+1+3,by omega,?_⟩
      rw [(inside a ha k (start_blocks a ha k) 3 (by decide)).1,h]
      norm_num [value];ring
end Deldor14.SquareSteps
theorem OMA.solution : type_of% @OMA.S_oeis_a097602.main := Deldor14.SquareSteps.full
