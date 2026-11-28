import OMAStatements.S_oeis_a386316

namespace OMA.Brownie

lemma square_obstruction {c d k j w : ℕ} (hd : d^2 < c) (he : c < (d+1)^2)
    (hk : c^2 ∣ k) (hw : w^2 = c + 4*k*j) : False := by
  obtain ⟨q, rfl⟩ := hk
  have hc : Nat.Coprime c (c * (4*q*j) + 1) := by simp
  have hu : IsUnit (gcd c (c * (4*q*j) + 1)) := by
    change IsUnit (Nat.gcd _ _)
    rw [hc.gcd_eq_one]
    exact isUnit_one
  obtain ⟨v,hv⟩ := exists_eq_pow_of_mul_eq_pow hu
    (show c * (c * (4*q*j) + 1) = w^2 by rw [hw]; ring)
  by_cases h : v ≤ d
  · have := Nat.pow_le_pow_left h 2
    omega
  · have := Nat.pow_le_pow_left (show d+1 ≤ v by omega) 2
    omega

lemma discr {x y w k j m r d : ℕ} (hdiff : w+x = y)
    (hs : x+y = 2*k+j) (hr : x*y+r = m) (hm : m+d^2 = k^2) :
    w^2 = 4*d^2+j^2+4*r+4*k*j := by
  subst y
  nlinarith only [congrArg (fun t : ℕ => t^2) hs,hr,hm]

lemma lower_cost {L d k m x y : ℕ} (hm : m + d^2 = k^2)
    (hk : d^2+L+1 < k) (hd : L^2+4*L < 4*d)
    (hdiv : ∀ c : ℕ, 0 < c → c ≤ 4*d^2+L^2+4*L → c^2 ∣ k)
    (harea : m ≤ x*y+L) : m + 4*k + 4 ≤ (x+2)*(y+2) := by
  by_contra! hcheap
  have hs : 2*k ≤ x+y := by
    by_contra! hsmall
    have hb : x+y ≤ 2*k-1 := by omega
    have hp := Nat.pow_le_pow_left hb 2
    have ht : 2*k-1+1 = 2*k := by omega
    have ht' := congrArg (fun t : ℕ => t^2) ht
    nlinarith [sq_nonneg ((x:ℤ)-y)]
  let j := x+y-2*k
  have hj : x+y = 2*k+j := by dsimp [j]; omega
  have hprod : x*y < m := by nlinarith
  let r := m-x*y
  have hr : x*y+r = m := by dsimp [r]; omega
  have hrpos : 0 < r := by omega
  have hrle : r ≤ L := by omega
  have hjle : j ≤ L := by nlinarith
  let c := 4*d^2+j^2+4*r
  have hclo : (2*d)^2 < c := by dsimp [c]; nlinarith
  have hcbd : c ≤ 4*d^2+L^2+4*L := by
    dsimp [c]; nlinarith [Nat.pow_le_pow_left hjle 2]
  have hchi : c < (2*d+1)^2 := by nlinarith
  by_cases hxy : x ≤ y
  · have he : y-x+x = y := by omega
    exact square_obstruction hclo hchi (hdiv c (by omega) hcbd) (discr he hj hr hm)
  · have he : x-y+y = x := by omega
    rw [add_comm x y] at hj
    rw [mul_comm x y] at hr
    exact square_obstruction hclo hchi (hdiv c (by omega) hcbd) (discr he hj hr hm)

end OMA.Brownie

open OMA.S_oeis_a386316 OMA.Brownie

theorem OMA.solution : type_of% @OMA.S_oeis_a386316.main := by
  intro L
  let d := L^2+4*L+1
  let B := 5*d^2+L^2+5*L+10
  let k := B.factorial^2
  have hd : 0 < d := by dsimp [d]; omega
  have hB : d^2+L+1 < B := by dsimp [B]; omega
  have hfact := Nat.self_le_factorial B
  have hfacpos := Nat.factorial_pos B
  have hk : d^2+L+1 < k := by dsimp [k]; nlinarith
  have hdk : d ≤ k := by nlinarith
  let m := k^2-d^2
  have hm : m+d^2 = k^2 := Nat.sub_add_cancel (Nat.pow_le_pow_left hdk 2)
  have hmL : L ≤ m := by nlinarith
  have hkdiff : k-d+d = k := by omega
  have hrect : (k-d)*(k+d) = m := by
    nlinarith [congrArg (fun t : ℕ => t*k) hkdiff, congrArg (fun t : ℕ => t*d) hkdiff]
  let n := m-L
  have hn : n+L = m := Nat.sub_add_cancel hmL
  have hcon : ∀ i : ℕ, i ≤ L → a (n+i) = m+4*k+4 := by
    intro i hi
    apply le_antisymm
    · apply Nat.sInf_le
      refine ⟨k-d,k+d,by omega,?_⟩
      nlinarith
    · apply le_csInf
      · refine ⟨(k-d+2)*(k+d+2), k-d,k+d, by omega,rfl⟩
      · rintro v ⟨x,y,hxy,rfl⟩
        apply lower_cost hm hk (by dsimp [d]; omega) _ (by omega)
        intro c hc hb
        exact pow_dvd_pow_of_dvd (Nat.dvd_factorial hc (by dsimp [B]; omega)) 2
  refine ⟨n,fun i hi => ?_⟩
  rw [hcon i hi.le, ← hcon 0 (Nat.zero_le L), Nat.add_zero]
