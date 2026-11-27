import OMAReductions.R_BealConjecture_beal_conjecture_R1
import Mathlib.Data.Nat.Prime.Basic

-- Credit: @Hennyrick

namespace OMA.R_BealConjecture_beal_conjecture_R1_H1_R1

/-- Remaining odd-prime signatures, after ordering the exponents on the left.
The designated (5,p,3) family has odd second base prime to 15 and 3 ∤ c. -/
def H1 : Prop :=
  ∀ {a b c x y z : Nat}, 0 < a → 0 < b → 0 < c → a.Coprime b →
    2 < x → 2 < y → 2 < z → x.Prime → y.Prime → z.Prime → x ≤ y →
    (x ≠ 5 ∨ y ≤ 109 ∨ z ≠ 3 ∨ b % 2 ≠ 1 ∨ ¬b.Coprime 15 ∨ 3 ∣ c) →
    a^x + b^y ≠ c^z

/-- The modular input for the mixed signature. At an auxiliary prime inert
in the CM field the residual trace vanishes. The Frobenius norm is specified
by the two finite point counts. Chart 0 is the interior, 1 is at zero and 2
at infinity. At t = 1 the multiplicative reduction gives ±(l+1).
This input includes passage from the Diophantine equation to the CM forms. -/
def H2 : Prop :=
  let traceNorm (l chart t : Nat) : Int :=
    let mask := if l=11 then 570 else if l=19 then 199410 else 332473074
    let chi (r : Nat) : Int := if r=0 then 0 else if mask.testBit r then 1 else -1
    let val (a b : Nat) :=
      let m := a*a
      let n := b*b
      let u := a*(m+6*n)
      let v := b*(3*m+2*n)
      let s := if chart=1 then 0 else 5
      let f := if chart=2 then 0 else l-12%l
      let g := if chart=1 then 0 else 10*t
      ((s*(u*u+2*v*v)+f*a*(m*m+20*m*n+20*n*n)+g*u+t*t)%l,
       (s*2*u*v+f*b*(5*m*m+20*m*n+4*n*n)+g*v)%l)
    let e : Int := if chart=1 then 0 else 1
    let xs := List.range l
    let ys := xs.map (fun a => (val a 0).1)
    let tr := -e - (ys.map chi).sum
    let s2 := (ys.filter (· != 0)).length + 2 * ((List.range (l/2)).map fun j =>
      (xs.map fun a => let v := val a (j+1); chi ((v.1*v.1+(l-2)*v.2*v.2)%l)).sum).sum
    (tr*tr+e+s2)/2-2*(l:Int)
  let fits (a b c p l : Nat) := if l ∣ b then p ∣ l+1 else
    ∃ t : Fin l, (if l ∣ a ∨ l ∣ c then 0 else 1) < t.val ∧
      (p:Int) ∣ traceNorm l (if l ∣ a then 1 else if l ∣ c then 2 else 0) t.val
  ∀ {a b c p : Nat}, 0 < a → 0 < b → 0 < c → a.Coprime b → p.Prime →
    109 < p → b%2 = 1 → b.Coprime 15 → ¬3 ∣ c → a^5+b^p=c^3 →
    (fits a b c p 11 ∨ fits a b c p 19) ∧ fits a b c p 29

/-- The surviving congruences restrict genuinely global primitive solutions. -/
def H3 : Prop :=
  ∀ {a b c p : Nat}, 0 < a → 0 < b → 0 < c → a.Coprime b → p.Prime →
    109 < p → b%2 = 1 → b.Coprime 15 → ¬3 ∣ c → 29 ∣ a*c →
    (11 ∣ c ∨ 19 ∣ a) → a^5+b^p ≠ c^3

/-- The set bits encode precisely the nonzero quadratic residues at the
three auxiliary primes. In each quadratic extension the coordinate s has
s² = 2; conjugate points a+bs, a−bs contribute the same character. -/
theorem quadratic_residue_masks :
    (∀ r : Fin 11, (570 : Nat).testBit r.val = true ↔
      r.val ≠ 0 ∧ ∃ x : Fin 11, x.val*x.val%11 = r.val) ∧
    (∀ r : Fin 19, (199410 : Nat).testBit r.val = true ↔
      r.val ≠ 0 ∧ ∃ x : Fin 19, x.val*x.val%19 = r.val) ∧
    (∀ r : Fin 29, (332473074 : Nat).testBit r.val = true ↔
      r.val ≠ 0 ∧ ∃ x : Fin 29, x.val*x.val%29 = r.val) := by decide

section

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Counts over the prime field and its quadratic extension give simultaneous
divisibility conditions for the original bases, for every p > 109. -/
theorem local_trace_restriction :
  let traceNorm (l chart t : Nat) : Int :=
    let mask := if l=11 then 570 else if l=19 then 199410 else 332473074
    let chi (r : Nat) : Int := if r=0 then 0 else if mask.testBit r then 1 else -1
    let val (a b : Nat) :=
      let m := a*a
      let n := b*b
      let u := a*(m+6*n)
      let v := b*(3*m+2*n)
      let s := if chart=1 then 0 else 5
      let f := if chart=2 then 0 else l-12%l
      let g := if chart=1 then 0 else 10*t
      ((s*(u*u+2*v*v)+f*a*(m*m+20*m*n+20*n*n)+g*u+t*t)%l,
       (s*2*u*v+f*b*(5*m*m+20*m*n+4*n*n)+g*v)%l)
    let e : Int := if chart=1 then 0 else 1
    let xs := List.range l
    let ys := xs.map (fun a => (val a 0).1)
    let tr := -e - (ys.map chi).sum
    let s2 := (ys.filter (· != 0)).length + 2 * ((List.range (l/2)).map fun j =>
      (xs.map fun a => let v := val a (j+1); chi ((v.1*v.1+(l-2)*v.2*v.2)%l)).sum).sum
    (tr*tr+e+s2)/2-2*(l:Int)
  let fits (a b c p l : Nat) := if l ∣ b then p ∣ l+1 else
    ∃ t : Fin l, (if l ∣ a ∨ l ∣ c then 0 else 1) < t.val ∧
      (p:Int) ∣ traceNorm l (if l ∣ a then 1 else if l ∣ c then 2 else 0) t.val
  ∀ a b c p : Nat, 109 < p →
    (fits a b c p 11 ∨ fits a b c p 19) ∧ fits a b c p 29 →
    29 ∣ a*c ∧ (11 ∣ c ∨ 19 ∣ a) := by
  intro traceNorm fits
  have bound11 : ∀ t : Fin 11,
      (1 < t.val → 0 < (traceNorm 11 0 t.val).natAbs ∧ (traceNorm 11 0 t.val).natAbs < 110) ∧
      (0 < t.val → 0 < (traceNorm 11 1 t.val).natAbs ∧ (traceNorm 11 1 t.val).natAbs < 110) := by
    dsimp only [traceNorm]
    decide +kernel
  have bound19 : ∀ t : Fin 19,
      (1 < t.val → 0 < (traceNorm 19 0 t.val).natAbs ∧ (traceNorm 19 0 t.val).natAbs < 110) ∧
      (0 < t.val → 0 < (traceNorm 19 2 t.val).natAbs ∧ (traceNorm 19 2 t.val).natAbs < 110) := by
    dsimp only [traceNorm]
    decide +kernel
  have bound29 : ∀ t : Fin 29,
      1 < t.val → 0 < (traceNorm 29 0 t.val).natAbs ∧ (traceNorm 29 0 t.val).natAbs < 110 := by
    dsimp only [traceNorm]
    decide +kernel
  intro a b c p hp ⟨h1,h2⟩
  have bad {n : Int} (hd : (p:Int) ∣ n) (h : 0 < n.natAbs ∧ n.natAbs < 110) : False := by
    have hz : p ∣ n.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hd
    have := Nat.le_of_dvd h.1 hz
    omega
  have small {n : Nat} (hn : 0 < n) (hlt : n < p) : ¬ p ∣ n := by
    intro hd
    have := Nat.le_of_dvd hn hd
    omega
  constructor
  · by_contra! h
    have ha : ¬29 ∣ a := fun d => h (Nat.dvd_mul_right_of_dvd d c)
    have hc : ¬29 ∣ c := fun d => h (Nat.dvd_mul_left_of_dvd d a)
    by_cases hb : 29 ∣ b
    · simp [fits, hb, small (n:=30) (by decide) (by omega)] at h2
    · obtain ⟨t, ht, hd⟩ := (show ∃ t : Fin 29, 1 < t.val ∧ (p:Int) ∣ traceNorm 29 0 t.val by simpa [fits, ha, hb, hc] using h2)
      exact bad hd (bound29 t ht)
  · rcases h1 with h | h
    · left
      by_contra! hc
      by_cases hb : 11 ∣ b
      · simp [fits, hb, small (n:=12) (by decide) (by omega)] at h
      · by_cases ha : 11 ∣ a
        · obtain ⟨t, ht, hd⟩ := (show ∃ t : Fin 11, 0 < t.val ∧ (p:Int) ∣ traceNorm 11 1 t.val by simpa [fits, ha, hb, hc] using h)
          exact bad hd ((bound11 t).2 ht)
        · obtain ⟨t, ht, hd⟩ := (show ∃ t : Fin 11, 1 < t.val ∧ (p:Int) ∣ traceNorm 11 0 t.val by simpa [fits, ha, hb, hc] using h)
          exact bad hd ((bound11 t).1 ht)
    · right
      by_contra! ha
      by_cases hb : 19 ∣ b
      · simp [fits, hb, small (n:=20) (by decide) (by omega)] at h
      · by_cases hc : 19 ∣ c
        · obtain ⟨t, ht, hd⟩ := (show ∃ t : Fin 19, 0 < t.val ∧ (p:Int) ∣ traceNorm 19 2 t.val by simpa [fits, ha, hb, hc] using h)
          exact bad hd ((bound19 t).2 ht)
        · obtain ⟨t, ht, hd⟩ := (show ∃ t : Fin 19, 1 < t.val ∧ (p:Int) ∣ traceNorm 19 0 t.val by simpa [fits, ha, hb, hc] using h)
          exact bad hd ((bound19 t).1 ht)

end

theorem ordered (other : H1) (geometry : H2) (remaining : H3)
    {a b c x y z : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a.Coprime b)
    (hx : 2 < x) (hy : 2 < y) (hz : 2 < z) (hxp : x.Prime) (hyp : y.Prime) (hzp : z.Prime)
    (hxy : x ≤ y) (eq : a^x+b^y=c^z) : False := by
  by_cases h : x ≠ 5 ∨ y ≤ 109 ∨ z ≠ 3 ∨ b % 2 ≠ 1 ∨ ¬b.Coprime 15 ∨ 3 ∣ c
  · exact other ha hb hc hab hx hy hz hxp hyp hzp hxy h eq
  have xx : x = 5 := by tauto
  have zz : z = 3 := by tauto
  subst x
  subst z
  have hp : 109 < y := by omega
  have hodd : b % 2 = 1 := by tauto
  have h15 : b.Coprime 15 := by tauto
  have h3 : ¬3 ∣ c := by tauto
  obtain ⟨u,v⟩ := local_trace_restriction a b c y hp (geometry ha hb hc hab hyp hp hodd h15 h3 eq)
  exact remaining ha hb hc hab hyp hp hodd h15 h3 u v eq

theorem main : H1 → H2 → H3 → OMA.R_BealConjecture_beal_conjecture_R1.H1 := by
  intro other geometry remaining a b c x y z ha hb hc hx hy hz eq
  by_cases hab : a.Coprime b
  · exfalso
    rcases Nat.le_total x y with h | h
    · exact ordered other geometry remaining (by omega) (by omega) (by omega) hab hx.1 hy.1 hz.1 hx.2 hy.2 hz.2 h eq
    · exact ordered other geometry remaining (by omega) (by omega) (by omega) hab.symm hy.1 hx.1 hz.1 hy.2 hx.2 hz.2 h ((Nat.add_comm _ _).trans eq)
  · obtain ⟨q, hq, qa, qb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hab
    have ax : a ∣ a^x := by simpa only [Nat.pow_one] using Nat.pow_dvd_pow a (by omega : 1 ≤ x)
    have by' : b ∣ b^y := by simpa only [Nat.pow_one] using Nat.pow_dvd_pow b (by omega : 1 ≤ y)
    exact ⟨q, hq, qa, qb, hq.dvd_of_dvd_pow (eq ▸ Nat.dvd_add (qa.trans ax) (qb.trans by'))⟩

end OMA.R_BealConjecture_beal_conjecture_R1_H1_R1
