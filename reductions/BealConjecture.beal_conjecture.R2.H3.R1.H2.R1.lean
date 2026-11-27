import OMAReductions.R_BealConjecture_beal_conjecture_R2_H3_R1

-- Credit: @Hennyrick

namespace OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1

/-- Positive-difference specialization of Bruin's classification of primitive
solutions to the equation with signature (3,3,5). -/
def H1 : Prop :=
  ∀ {u v w : Nat}, u ≠ 0 → v ≠ 0 → w ≠ 0 → u.Coprime v →
    u ^ 3 ≠ v ^ 3 + w ^ 5

/-- Positive-difference specialization of Poonen's classification of primitive
solutions to the equation with signature (5,5,3). -/
def H2 : Prop :=
  ∀ {u v w : Nat}, u ≠ 0 → v ≠ 0 → w ≠ 0 → u.Coprime v →
    u ^ 5 ≠ v ^ 5 + w ^ 3

/-- Consequence of D. Brown's classification of primitive integer solutions
to X² + Y³ = Z¹⁰, Theorem 1.1. -/
def H3 : Prop :=
  ∀ {X Y Z : Int}, X.natAbs.Coprime Y.natAbs →
    X ^ 2 + Y ^ 3 = Z ^ 10 → X.natAbs ≤ 3

/-- Cubic-field descent in the integral basis (1, α, α²) with α³ = 2.
The five unit representatives are the powers of α−1 from zero to four. -/
def H4 : Prop :=
  let mul (x y : (Int × Int × Int)) : (Int × Int × Int) :=
    ⟨x.1*y.1+2*(x.2.1*y.2.2+x.2.2*y.2.1), x.1*y.2.1+x.2.1*y.1+2*x.2.2*y.2.2,
     x.1*y.2.2+x.2.1*y.2.1+x.2.2*y.1⟩

  let quint (x : (Int × Int × Int)) : (Int × Int × Int) :=
    let sq := mul x x
    mul x (mul sq sq)

  let unit (i : Fin 5) : (Int × Int × Int) :=
    [(1,0,0),(-1,1,0),(1,-2,1),(1,3,-3),(-7,-2,6)][i.val]'(by exact i.isLt)

  let coeff (i : Fin 5) (x : (Int × Int × Int)) : (Int × Int × Int) := mul (unit i) (quint x)
  ∀ {a b q : Nat}, a % 2 = 1 → b % 2 = 1 → a.Coprime b →
    a ^ 3 + b ^ 5 = 2 ^ (3 * q + 2) →
    ∃ i : Fin 5, ∃ x : Int × Int × Int, coeff i x = (-(a:Int), 0, 2^q)

theorem coprime_two_pow {a : Nat} (ha : a % 2 = 1) (m : Nat) :
    (2 ^ m).Coprime a := by
  apply Nat.Coprime.pow_left
  change Nat.gcd 2 a = 1
  rw [Nat.gcd_rec 2 a, ha, Nat.gcd_one_left]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/-- For α³ = 2, suppose (α−1)^i times an integral fifth power has
zero linear coefficient and quadratic coefficient 2^q in the basis (1, α, α²).
The tests modulo 25 and 31 force q ≡ 1 modulo 5. -/
theorem fifth_power_coefficient :
  let mul (x y : (Int × Int × Int)) : (Int × Int × Int) :=
    ⟨x.1*y.1+2*(x.2.1*y.2.2+x.2.2*y.2.1), x.1*y.2.1+x.2.1*y.1+2*x.2.2*y.2.2,
     x.1*y.2.2+x.2.1*y.2.1+x.2.2*y.1⟩

  let quint (x : (Int × Int × Int)) : (Int × Int × Int) :=
    let sq := mul x x
    mul x (mul sq sq)

  let unit (i : Fin 5) : (Int × Int × Int) :=
    [(1,0,0),(-1,1,0),(1,-2,1),(1,3,-3),(-7,-2,6)][i.val]'(by exact i.isLt)

  let coeff (i : Fin 5) (x : (Int × Int × Int)) : (Int × Int × Int) := mul (unit i) (quint x)
  ∀ (i : Fin 5) (x : Int × Int × Int) (q : Nat),
    (coeff i x).2.1 = 0 → (coeff i x).2.2 = 2 ^ q → q % 5 = 1 := by
  intro mul quint unit coeff
  let Congr (m : Int) (x y : (Int × Int × Int)) : Prop :=
    x.1 % m = y.1 % m ∧ x.2.1 % m = y.2.1 % m ∧ x.2.2 % m = y.2.2 % m

  have cmul {a b c d m : Int} (h : a % m = b % m) (k : c % m = d % m) :
      (a * c) % m = (b * d) % m := by rw [Int.mul_emod a c m, Int.mul_emod b d m, h, k]

  have cadd {a b c d m : Int} (h : a % m = b % m) (k : c % m = d % m) :
      (a + c) % m = (b + d) % m := by rw [Int.add_emod a c m, Int.add_emod b d m, h, k]

  have congr_mul {m : Int} {x x' y y' : (Int × Int × Int)}
      (hx : Congr m x x') (hy : Congr m y y') : Congr m (mul x y) (mul x' y') := by
    obtain ⟨ha,hb,hc⟩ := hx
    obtain ⟨hd,he,hf⟩ := hy
    refine ⟨?_, ?_, ?_⟩
    · exact cadd (cmul ha hd) (cmul rfl (cadd (cmul hb hf) (cmul hc he)))
    · exact cadd (cadd (cmul ha he) (cmul hb hd)) (cmul (cmul rfl hc) hf)
    · exact cadd (cadd (cmul ha hf) (cmul hb he)) (cmul hc hd)

  have congr_coeff {m : Int} (i : Fin 5) {x y : (Int × Int × Int)} (h : Congr m x y) :
      Congr m (coeff i x) (coeff i y) := by
    have h2 := congr_mul h h
    exact congr_mul ⟨rfl,rfl,rfl⟩ (congr_mul h (congr_mul h2 h2))

  let residue (x : Int) (m : Nat) (hm : 0 < m) : Fin m :=
    ⟨(x % (m:Int)).toNat, by
      have := Int.emod_lt_of_pos x (show 0 < (m:Int) by omega)
      omega⟩

  let ofFin {m : Nat} (a b c : Fin m) : (Int × Int × Int) := ⟨a.val,b.val,c.val⟩

  let reduce (x : (Int × Int × Int)) (m : Nat) (hm : 0 < m) : (Int × Int × Int) :=
    ofFin (residue x.1 m hm) (residue x.2.1 m hm) (residue x.2.2 m hm)

  have residue_cast (x : Int) (m : Nat) (hm : 0 < m) :
      ((residue x m hm).val : Int) = x % (m:Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

  let plus (x y : (Int × Int × Int)) : (Int × Int × Int) := ⟨x.1+y.1, x.2.1+y.2.1, x.2.2+y.2.2⟩
  let scale (t : Int) (x : (Int × Int × Int)) : (Int × Int × Int) := ⟨t*x.1,t*x.2.1,t*x.2.2⟩

  have quint_five (x y : (Int × Int × Int)) :
      ∃ z : (Int × Int × Int), quint (plus x (scale 5 y)) = plus (quint x) (scale 25 z) := by
    let x2 := mul x x
    let y2 := mul y y
    let u1 := mul (mul x2 x2) y
    let u2 := mul (mul x2 x) y2
    let u3 := mul x2 (mul y2 y)
    let u4 := mul x (mul y2 y2)
    refine ⟨plus u1 (plus (scale 10 u2) (plus (scale 50 u3)
      (plus (scale 125 u4) (scale 125 (quint y))))), ?_⟩
    rcases x with ⟨xa,xb,xc⟩
    rcases y with ⟨ya,yb,yc⟩
    dsimp [u1,u2,u3,u4,x2,y2,quint,mul,plus,scale]
    apply Prod.ext
    · grind
    · apply Prod.ext <;> grind

  have coeff_reduce25 (i : Fin 5) (x : (Int × Int × Int)) :
      Congr 25 (coeff i x) (coeff i (reduce x 5 (by decide))) := by
    let r := reduce x 5 (by decide)
    let z : (Int × Int × Int) := ⟨x.1 / 5, x.2.1 / 5, x.2.2 / 5⟩
    have h : x = plus r (scale 5 z) := by
      rcases x with ⟨xa,xb,xc⟩
      dsimp [r,plus,scale,z,reduce,ofFin]
      simp only [residue_cast]
      apply Prod.ext
      · omega
      · apply Prod.ext <;> (dsimp only; omega)
    obtain ⟨w,hw⟩ := quint_five r z
    have hh : Congr 25 (quint x) (quint r) := by
      rw [h,hw]
      simp [Congr,plus,scale,Int.add_mul_emod_self_left]
    exact congr_mul ⟨rfl,rfl,rfl⟩ hh

  let atRoot (z : Int) (x : (Int × Int × Int)) : Int := x.1 + z * x.2.1 + z^2 * x.2.2

  have atRoot_mul {z : Int} (hz : 31 ∣ z^3-2) (x y : (Int × Int × Int)) :
      atRoot z (mul x y) % 31 = (atRoot z x * atRoot z y) % 31 := by
    have h : atRoot z x * atRoot z y =
        atRoot z (mul x y) + (x.2.1*y.2.2+x.2.2*y.2.1+z*x.2.2*y.2.2)*(z^3-2) := by
      simp only [atRoot, mul]
      grind
    obtain ⟨l, hl⟩ := hz
    rw [h, hl, Int.mul_comm 31 l, ← Int.mul_assoc, Int.add_mul_emod_self_right]

  have atRoot_quint {z : Int} (hz : 31 ∣ z^3-2) (x : (Int × Int × Int)) :
      atRoot z (quint x) % 31 = (atRoot z x)^5 % 31 := by
    have h2 := atRoot_mul hz x x
    have h4 := (atRoot_mul hz (mul x x) (mul x x)).trans (cmul h2 h2)
    have h5 := (atRoot_mul hz x (mul (mul x x) (mul x x))).trans (cmul rfl h4)
    apply h5.trans
    grind

  let root (j : Fin 3) : Int := [4,7,20][j.val]'(by exact j.isLt)

  have cube_root : ∀ j : Fin 3, 31 ∣ (root j)^3-2 := by dsimp only [root]; decide

  let images31 (i : Fin 5) (j : Fin 3) : List Int :=
    (List.range 31).map fun (n : Nat) => (atRoot (root j) (unit i) * (n:Int)^5) % 31

  have eval_member (i : Fin 5) (j : Fin 3) (x : (Int × Int × Int)) :
      atRoot (root j) (coeff i x) % 31 ∈ images31 i j := by
    let z := root j
    let n := residue (atRoot z x) 31 (by decide)
    refine List.mem_map.mpr ⟨n.val, List.mem_range.mpr n.isLt, ?_⟩
    have hq := atRoot_quint (cube_root j) x
    have hh := (atRoot_mul (cube_root j) (unit i) (quint x)).trans (cmul rfl hq)
    change _ = atRoot z (mul (unit i) (quint x)) % 31
    rw [hh]
    apply cmul rfl
    have hpow (k : Nat) : (n.val:Int)^k % 31 = (atRoot z x)^k % 31 := by
      induction k with
      | zero => simp
      | succ k ih =>
        simp only [Int.pow_succ]
        apply cmul ih
        change ((residue (atRoot z x) 31 (by decide)).val:Int) % 31 = _
        rw [residue_cast _ 31 (by decide)]; exact Int.emod_emod _ 31
    exact hpow 5

  let fits31 (i : Fin 5) (q : Nat) : Prop :=
    ∃ a : Fin 31, ∀ j : Fin 3,
      ((a.val:Int) + (root j)^2*2^q) % 31 ∈ images31 i j

  have two_period (m : Int) (hp : (2:Int)^20 % m = 1 % m) (q : Nat) :
      (2:Int)^q % m = (2:Int)^(q%20) % m := by
    have hpow (k : Nat) : ((2:Int)^20)^k % m = 1 % m := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Int.pow_succ, Int.mul_emod, ih, hp, ← Int.mul_emod, Int.mul_one]
    calc
      _ = (2:Int)^(q%20+20*(q/20)) % m := by rw [Nat.mod_add_div]
      _ = _ := by
        rw [Int.pow_add, Int.pow_mul, Int.mul_emod, hpow, ← Int.mul_emod, Int.mul_one]

  have fits31_of_rep (i : Fin 5) (x : (Int × Int × Int)) (q : Nat)
      (hb : (coeff i x).2.1 = 0)
      (hc : (coeff i x).2.2 = 2^q) : fits31 i (q%20) := by
    refine ⟨residue (coeff i x).1 31 (by decide), ?_⟩
    intro j
    have h := eval_member i j x
    have he : atRoot (root j) (coeff i x) =
        (coeff i x).1 + (root j)^2*2^q := by
      dsimp only [atRoot]
      rw [hb,hc]
      simp
    rw [he] at h
    have ha : ((residue (coeff i x).1 31 (by decide)).val:Int) % 31 = (coeff i x).1 % 31 := by
      rw [residue_cast _ 31 (by decide)]; exact Int.emod_emod _ 31
    rw [cadd ha (cmul rfl (two_period 31 (by decide) q).symm)]
    exact h

  let image25 (i : Fin 5) : List Int :=
    match i.val with
    | 0 => [0, 1, 2, 7, 11, 14, 18, 23, 24]
    | 1 => [0, 2, 5, 10, 11, 14, 15, 20, 23]
    | 2 => [0, 5, 10, 15, 20]
    | 3 => [0, 3, 4, 5, 10, 15, 20, 21, 22]
    | _ => [0, 2, 5, 10, 11, 14, 15, 20, 23]

  have images25_correct : ∀ (i a b c : Fin 5), (coeff i (ofFin a b c)).2.1 % 25 = 0 →
      (coeff i (ofFin a b c)).2.2 % 25 ∈ image25 i := by
    dsimp only [ofFin,coeff,unit,quint,mul,image25]
    decide +kernel

  have joint_table : ∀ (i : Fin 5) (q : Fin 20),
      (2:Int)^q.val % 25 ∈ image25 i → fits31 i q.val → q.val % 5 = 1 := by
    dsimp only [image25,fits31,images31,root,atRoot,unit]
    decide +kernel

  have quadratic_coefficient {i : Fin 5} {x : (Int × Int × Int)} {q : Nat}
      (hb : (coeff i x).2.1 = 0) (hc : (coeff i x).2.2 = 2^q) : q % 5 = 1 := by
    have hh := coeff_reduce25 i x
    have hz := hh.2.1
    rw [hb] at hz
    have hin := images25_correct i (residue x.1 5 (by decide))
      (residue x.2.1 5 (by decide)) (residue x.2.2 5 (by decide)) hz.symm
    change (coeff i (reduce x 5 (by decide))).2.2 % 25 ∈ image25 i at hin
    rw [← hh.2.2, hc, two_period 25 (by decide) q] at hin
    have h31 := fits31_of_rep i x q hb hc
    have h := joint_table i ⟨q%20, Nat.mod_lt _ (by decide)⟩ hin h31
    change q % 20 % 5 = 1 at h
    omega
  exact fun i x q hz ht => quadratic_coefficient (i := i) (x := x) (q := q) hz ht

theorem descent_divisibility (descent : H4) {a b q : Nat}
    (ha : a % 2 = 1) (hb : b % 2 = 1) (hcop : a.Coprime b)
    (he : a ^ 3 + b ^ 5 = 2 ^ (3 * q + 2)) : 5 ∣ 3 * q + 2 := by
  obtain ⟨i, x, hrep⟩ := descent ha hb hcop he
  have h := fifth_power_coefficient i x q (by rw [hrep]) (by rw [hrep])
  omega

theorem coprime_from_sum {a b k : Nat} (ha : a % 2 = 1)
    (eq : a ^ 3 + b ^ 5 = 2 ^ k) : a.Coprime b := by
  apply Nat.gcd_eq_one_iff.mpr
  intro d da db
  have da3 : d ∣ a ^ 3 := Nat.dvd_mul_left_of_dvd da (a ^ 2)
  have db5 : d ∣ b ^ 5 := Nat.dvd_mul_left_of_dvd db (b ^ 4)
  have d2 := Nat.dvd_add da3 db5
  rw [eq] at d2
  exact Nat.gcd_eq_one_iff.mp (coprime_two_pow ha k) d d2 da

theorem case_brown (brown : H3) {a b k : Nat}
    (ha : a % 2 = 1) (hk : 2 < k) (hr : k % 3 = 1)
    (eq : a ^ 3 + b ^ 5 = 2 ^ k) : False := by
  let n := (k + 2) / 3
  have hn : 3 * n = k + 2 := by dsimp [n]; omega
  let X := 2 ^ k + a ^ 3
  let T := 2 ^ n * a
  have hxa : X.Coprime a := by
    change Nat.gcd (2 ^ k + a ^ 2 * a) a = 1
    rw [Nat.gcd_add_mul_right_left]
    exact coprime_two_pow ha k
  have hodd : X % 2 = 1 := by
    change (2 ^ k + a ^ 3) % 2 = 1
    rw [Nat.add_mod, Nat.pow_mod 2, Nat.pow_mod a, ha]
    simp [Nat.zero_pow (show 0 < k by omega)]
  have hprim : X.Coprime T := (coprime_two_pow hodd n).symm.mul_right hxa
  have hi := congrArg (fun v : Nat => (v : Int)) eq
  simp only [Int.natCast_add, Int.natCast_pow] at hi
  change (a : Int)^3 + (b : Int)^5 = (2 : Int)^k at hi
  have hpow : ((2:Int)^n)^3 = (2:Int)^k * 4 := by
    rw [← Int.pow_mul, Nat.mul_comm, hn, Int.pow_add]
    rfl
  have hx : (X : Int) = (2 : Int) ^ k + (a : Int) ^ 3 := by
    simp only [X, Int.natCast_add, Int.natCast_pow]
    rfl
  have ht : (T : Int) = (2 : Int) ^ n * (a : Int) := by
    simp only [T, Int.natCast_mul, Int.natCast_pow]
    rfl
  have he : (X : Int)^2 + (-(T : Int))^3 = (b : Int)^10 := by
    rw [hx, ht]
    grind
  have hsmall := brown (X := (X : Int)) (Y := -(T : Int)) (Z := (b : Int))
    (by simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hprim) he
  rw [Int.natAbs_natCast] at hsmall
  have hlarge : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  dsimp [X] at hsmall
  omega

/-- All positive odd cubes and fifth powers. The four named hypotheses expose
the three published classifications and the ideal factorization used here.
The two coefficient tests use moduli 25 and 31. -/
theorem no_three_five (bruin : H1) (brown : H3)
    (poonen : H2) (descent : H4)
    {a b k : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) (hk : 2 < k) :
    a ^ 3 + b ^ 5 ≠ 2 ^ k := by
  intro eq
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h | h | h
  · let q := k / 3
    have he : k = q * 3 := by dsimp [q]; omega
    have hh := bruin (u := 2 ^ q) (v := a) (w := b)
      (Nat.ne_of_gt (Nat.two_pow_pos q)) (by omega) (by omega) (coprime_two_pow ha q)
    apply hh
    rw [← Nat.pow_mul, ← he, eq]
  · exact case_brown brown ha hk h eq
  · let q := k / 3
    have he : k = 3 * q + 2 := by dsimp [q]; omega
    have hr := eq
    rw [he] at hr
    have hdiv : 5 ∣ k := by
      rw [he]
      exact descent_divisibility descent ha hb (coprime_from_sum ha eq) hr
    obtain ⟨j, hj⟩ := hdiv
    have hj' : j * 5 = k := by omega
    apply poonen (u := 2 ^ j) (v := b) (w := a)
      (Nat.ne_of_gt (Nat.two_pow_pos j)) (by omega) (by omega) (coprime_two_pow hb j)
    rw [← Nat.pow_mul, hj', ← eq, Nat.add_comm]

theorem main : H1 → H2 → H3 → H4 → OMA.R_BealConjecture_beal_conjecture_R2_H3_R1.H2 := by
  intro bruin poonen brown descent a b k _ _ ha hb _ _ hk _
  exact no_three_five bruin brown poonen descent ha hb hk

end OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1
