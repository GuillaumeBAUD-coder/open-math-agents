import OMAReductions.R_BealConjecture_beal_conjecture_R2_H3_R1

-- Credit: @Hennyrick
-- Chen–Siksek, Perfect powers expressible as sums of two cubes, Theorem 1(I).
-- Darmon–Merel, Winding quotients and some variants of Fermat's Last Theorem,
-- Main Theorem 3, with modularity of elliptic curves over the rationals.
-- Poonen–Schaefer–Stoll, Twists of X(7) and primitive solutions, Theorem 1.1.

namespace OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H3_R1

/-- Remaining ordered prime exponent pairs after the cube/seventh case. -/
def H1 : Prop :=
  ∀ {a b p q k : Nat}, 1 < a → 1 < b → a % 2 = 1 → b % 2 = 1 →
    Nat.gcd a b = 1 → a % 8 + b % 8 = 8 →
    2 < p → p < q → Nat.Prime p → Nat.Prime q → 2 < k → (p ≠ 3 ∨ q ≠ 5) →
    (p ≠ 3 ∨ q ≠ 7) → a ^ p + b ^ q ≠ 2 ^ k

/-- The positive difference specializations of Chen–Siksek (3,3,7) and
Darmon–Merel (7,7,3). -/
def H2 : Prop :=
  ∀ {n m u v w : Nat}, ((n = 3 ∧ m = 7) ∨ (n = 7 ∧ m = 3)) →
    u ≠ 0 → v ≠ 0 → w ≠ 0 → u.Coprime v → u ^ n ≠ v ^ n + w ^ m

/-- Consequence of the list of primitive triples in the Poonen–Schaefer–Stoll
classification for X²+Y³=Z⁷, retaining the Y bound at Z=1. -/
def H3 : Prop :=
  ∀ {X Y Z : Int}, X.natAbs.Coprime Y.natAbs → X^2 + Y^3 = Z^7 →
    Z = -1 ∨ Z = 0 ∨ (Z = 1 ∧ Y.natAbs ≤ 2) ∨
    Z = 2 ∨ Z = 17 ∨ Z = 65 ∨ Z = 113

/-- The cubic descent and its two coefficient tests modulo 43 and 49 force
the exponent residue in the quadratic-coefficient branch. -/
def H4 : Prop :=
  ∀ {a b q : Nat}, a.Coprime b → a^3+b^7=2^(3*q+2) → q%7=4

lemma coprime_two_pow {a : Nat} (ha : a % 2 = 1) (m : Nat) :
    (2 ^ m).Coprime a := by
  apply Nat.Coprime.pow_left
  change Nat.gcd 2 a = 1
  rw [Nat.gcd_rec 2 a, ha, Nat.gcd_one_left]

lemma case_pss (pss : H3) {a b k : Nat}
    (ha : a % 2 = 1) (hb : b % 2 = 1) (hk : 2 < k) (hr : k % 3 = 1)
    (eq : a ^ 3 + b ^ 7 = 2 ^ k) : False := by
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
  change (a : Int)^3 + (b : Int)^7 = (2 : Int)^k at hi
  have hpow : ((2:Int)^n)^3 = (2:Int)^k * 4 := by
    rw [← Int.pow_mul, Nat.mul_comm, hn, Int.pow_add]
    rfl
  have hx : (X : Int) = (2 : Int) ^ k + (a : Int) ^ 3 := by
    simp only [X, Int.natCast_add, Int.natCast_pow]
    rfl
  have ht : (T : Int) = (2 : Int) ^ n * (a : Int) := by
    simp only [T, Int.natCast_mul, Int.natCast_pow]
    rfl
  have he : (X : Int)^2 + (-(T : Int))^3 = ((b : Int)^2)^7 := by
    rw [hx, ht]
    grind
  have hcases := pss (X := (X : Int)) (Y := -(T : Int)) (Z := (b : Int)^2)
    (by simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hprim) he
  have hmod : (b:Int)^2%3 = 0 ∨ (b:Int)^2%3 = 1 := by
    have table : ∀ t : Fin 3, ((t.val:Int)^2 % 3 = 0 ∨ (t.val:Int)^2 % 3 = 1) := by decide
    have h := table ⟨b%3,Nat.mod_lt _ (by decide)⟩
    have hcast : ((b%3 : Nat):Int) = (b:Int)%3 := by omega
    change ((b%3 : Nat):Int)^2%3 = 0 ∨ ((b%3 : Nat):Int)^2%3 = 1 at h
    rw [hcast] at h
    have hl : ((b:Int)%3)^2%3 = (b:Int)^2%3 := by
      simpa only [Int.pow_succ,Int.pow_zero,Int.one_mul] using (Int.mul_emod (b:Int) b 3).symm
    rwa [hl] at h
  have hb0 : (b:Int)^2 ≠ 0 := by
    rw [← Int.natCast_pow]
    have hpos := Nat.pow_pos (n:=2) (show 0 < b by omega)
    omega
  have hsmall : (-(T:Int)).natAbs ≤ 2 := by omega
  rw [Int.natAbs_neg,Int.natAbs_natCast] at hsmall
  have h2n : 2 ≤ n := by dsimp [n]; omega
  have hp : 2^2 ≤ (2:Nat)^n := Nat.pow_le_pow_right (by decide) h2n
  have hlarge := Nat.mul_le_mul_left (2^n) (show 1 ≤ a by omega)
  dsimp [T] at hsmall
  omega

lemma no_three_seven (same : H2) (pss : H3) (sieve : H4)
    {a b k : Nat} (ha : a%2=1) (hb : b%2=1) (hk : 2<k) (hc : a.Coprime b) :
    a^3+b^7 ≠ 2^k := by
  intro eq
  rcases (show k%3=0 ∨ k%3=1 ∨ k%3=2 by omega) with h | h | h
  · let q := k/3
    have he : k=q*3 := by dsimp [q]; omega
    apply same (n:=3) (m:=7) (u:=2^q) (v:=a) (w:=b) (Or.inl ⟨rfl,rfl⟩) (Nat.ne_of_gt (Nat.two_pow_pos q))
      (by omega) (by omega) (coprime_two_pow ha q)
    rw [← Nat.pow_mul, ← he, eq]
  · exact case_pss pss ha hb hk h eq
  · let q := k/3
    have he : k=3*q+2 := by dsimp [q]; omega
    have hr := eq
    rw [he] at hr
    have hq := sieve hc hr
    have hj : (k/7)*7=k := by omega
    apply same (n:=7) (m:=3) (u:=2^(k/7)) (v:=b) (w:=a) (Or.inr ⟨rfl,rfl⟩) (Nat.ne_of_gt (Nat.two_pow_pos _))
      (by omega) (by omega) (coprime_two_pow hb _)
    rw [← Nat.pow_mul, hj, ← eq, Nat.add_comm]

theorem main : H1 → H2 → H3 → H4 → OMA.R_BealConjecture_beal_conjecture_R2_H3_R1.H3 := by
  intro remaining same pss sieve a b p q k ha hb hoa hob hc hab hp hpq hpp hqp hk h35
  by_cases h37 : p = 3 ∧ q = 7
  · obtain ⟨rfl, rfl⟩ := h37
    exact no_three_seven same pss sieve hoa hob hk hc
  · exact remaining ha hb hoa hob hc hab hp hpq hpp hqp hk h35 (by omega)

end OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H3_R1
