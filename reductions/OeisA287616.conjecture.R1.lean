import FormalConjectures.OEIS.«287616»

/-! Following Cao, Guo, Qiu, Feng and Gao, arXiv:2606.26035, Sections 2–7.
Normalize the diagonal coordinates by absolute value. The scalar rank encodes
the three components of the descent potential for a fixed represented integer. -/
namespace OMA.R_OeisA287616_conjecture_R1

-- Primitive representation by a class in the two-class genus.
def H1 : Prop := ∀ n : ℕ,
  (∃ u v w : ℕ, 15*u^2 + 5*v^2 + 3*w^2 = 120*n+23 ∧ u.gcd (v.gcd w) = 1) ∨ (∃ x y z : ℤ, 2*x^2 - 2*x*y + 8*y^2 + 15*z^2 = 120*(n : ℤ)+23 ∧ x.natAbs.gcd (y.natAbs.gcd z.natAbs) = 1)

-- Escape the bad residue class of a representation by the genus mate.
def H2 : Prop := ∀ n : ℕ, (∃ x y z : ℤ, 2*x^2 - 2*x*y + 8*y^2 + 15*z^2 = 120*(n : ℤ)+23 ∧ x.natAbs.gcd (y.natAbs.gcd z.natAbs) = 1) →
  (∃ x y z : ℤ, 2*x^2 - 2*x*y + 8*y^2 + 15*z^2 = 120*(n : ℤ)+23 ∧ x.natAbs.gcd (y.natAbs.gcd z.natAbs) = 1 ∧ (¬ 3 ∣ y ∨ ¬ 3 ∣ z))

-- Integral transfer from a usable mate representation to the diagonal form.
def H3 : Prop := ∀ n : ℕ, (∃ x y z : ℤ, 2*x^2 - 2*x*y + 8*y^2 + 15*z^2 = 120*(n : ℤ)+23 ∧ x.natAbs.gcd (y.natAbs.gcd z.natAbs) = 1 ∧ (¬ 3 ∣ y ∨ ¬ 3 ∣ z)) →
  (∃ u v w : ℕ, 15*u^2 + 5*v^2 + 3*w^2 = 120*n+23 ∧ u.gcd (v.gcd w) = 1)

-- Every primitive diagonal representation outside the desired classes descends.
def H4 : Prop := ∀ n : ℕ,
    let rank (u v w : ℕ) :=
      let odd := u%2=1 ∧ v%2=1 ∧ w%2=1
      let bv : ℕ := if odd ∧ v%6=1 then 0 else 1
      let bw : ℕ := if odd ∧ w%10=1 then 0 else 1
      let d := (if odd ∧ u%4≠v%4 then 0 else bv) +
        (if (u+w)%3=0 then 0 else bw) + (if odd then 0 else 2)
      ((bv+bw)*5 + d)*(120*n+24) + u+v+w
    ∀ u v w : ℕ, 15*u^2 + 5*v^2 + 3*w^2 = 120*n+23 → u.gcd (v.gcd w) = 1 →
      ¬ (u % 2 = 1 ∧ v % 6 = 1 ∧ w % 10 = 1) →
      ∃ i j k : ℕ, 15*i^2 + 5*j^2 + 3*k^2 = 120*n+23 ∧ i.gcd (j.gcd k) = 1 ∧
        rank i j k < rank u v w

private lemma triangular_even (t : ℕ) (b : ℕ) (hb : b%2=1) :
    2*(t*(b*t+1)/2) = t*(b*t+1) := by
  have h : t*(b*t+1)%2 = 0 := by
    rw [Nat.mul_mod, Nat.add_mod, Nat.mul_mod b, hb]
    rcases Nat.mod_two_eq_zero_or_one t with ht | ht <;> simp [ht]
  omega

theorem main : H1 → H2 → H3 → H4 → type_of% @OeisA287616.conjecture := by
  intro genus escape transfer descent n
  have seed : ∃ u v w : ℕ, 15*u^2 + 5*v^2 + 3*w^2 = 120*n+23 ∧ u.gcd (v.gcd w) = 1 :=
    (genus n).elim id (fun h => transfer n (escape n h))
  let rank (u v w : ℕ) :=
      let odd := u%2=1 ∧ v%2=1 ∧ w%2=1
      let bv : ℕ := if odd ∧ v%6=1 then 0 else 1
      let bw : ℕ := if odd ∧ w%10=1 then 0 else 1
      let d := (if odd ∧ u%4≠v%4 then 0 else bv) +
        (if (u+w)%3=0 then 0 else bw) + (if odd then 0 else 2)
      ((bv+bw)*5 + d)*(120*n+24) + u+v+w
  let S (r : ℕ) := ∃ u v w : ℕ, 15*u^2 + 5*v^2 + 3*w^2 = 120*n+23 ∧ u.gcd (v.gcd w) = 1 ∧ rank u v w = r
  have hS : ∃ r, S r := by
    obtain ⟨u,v,w,hq,hp⟩ := seed
    exact ⟨_,u,v,w,hq,hp,rfl⟩
  classical
  obtain ⟨u,v,w,hq,hp,hr⟩ := Nat.find_spec hS
  have hg : u % 2 = 1 ∧ v % 6 = 1 ∧ w % 10 = 1 := by
    by_contra hb
    obtain ⟨i,j,k,hq',hp',hlt⟩ := descent n u v w hq hp hb
    have hle := Nat.find_min' hS (show S (rank i j k) from ⟨i,j,k,hq',hp',rfl⟩)
    change rank i j k < rank u v w at hlt
    omega
  obtain ⟨hu,hv,hw⟩ := hg
  let x := u/2
  let y := v/6
  let z := w/10
  have hux : u = 2*x+1 := by dsimp [x]; omega
  have hvy : v = 6*y+1 := by dsimp [y]; omega
  have hwz : w = 10*z+1 := by dsimp [z]; omega
  refine ⟨x,y,z,?_⟩
  rw [hux,hvy,hwz] at hq
  have hx := triangular_even x 1 (by decide)
  simp only [one_mul] at hx
  have hy := triangular_even y 3 (by decide)
  have hz := triangular_even z 5 (by decide)
  nlinarith

end OMA.R_OeisA287616_conjecture_R1
