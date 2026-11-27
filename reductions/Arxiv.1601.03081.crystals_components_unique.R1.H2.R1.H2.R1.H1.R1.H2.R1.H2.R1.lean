import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1

/-! The common multiple of the two component sums has an odd least-common-multiple
cofactor. Accounting for that cofactor and the linear term of the product gives
a stronger quotient bound in both remaining cases. -/

namespace OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1_H2_R1

private theorem first_component_bound {g y z : ℕ}
    (hg : 2 ≤ g) (ho : g*y ≤ z) (hdiv : g+y*z ∣ g*y*z+1) :
    y^2+1 < g := by
  have hmul : g+y*z ∣ g*(g+y*z) := dvd_mul_left _ _
  have hsub := Nat.dvd_sub hmul hdiv
  have hdiff : g*(g+y*z)-(g*y*z+1)=g^2-1 := by
    have heq : g*(g+y*z)=g*y*z+g^2 := by ring
    omega
  rw [hdiff] at hsub
  have hsq : 1 < g^2 := by nlinarith
  have hs : g+y*z ≤ g^2-1 := Nat.le_of_dvd (by omega) hsub
  have hs' : g+y*z < g^2 := by omega
  have hb := Nat.mul_le_mul_left y ho
  have hgY : g*(y^2+1) ≤ g+y*z := by nlinarith only [hb]
  by_contra! h
  have hmul' := Nat.mul_le_mul_left g h
  nlinarith only [hs',hgY,hmul']

private theorem scaled_bounds {g y z q k D : ℕ}
    (hg : 2 ≤ g) (hy : 2 ≤ y) (ho : g*y ≤ z)
    (hgY : y^2+1 < g) (hD : D ≤ y^2-1) (hk : 0 < k)
    (heq : k*((g+y*z)*(g*y+z))=D*(g*y*z+1))
    (hq : 0 < q) (hquot : (g*y+z)^2=q*((g*y+1)*(z+1))) :
    k*(z+g*y) < g*D ∧ k*y*q < D+2*k*y := by
  have hyp : 0 < y := by omega
  have hgp : 0 < g := by omega
  have hzp : 0 < z := lt_of_lt_of_le (Nat.mul_pos hgp hyp) ho
  have hgz : g ≤ k*(g*z) := by
    calc
      g ≤ g*z := by
        simpa using Nat.mul_le_mul_left g (show 1 ≤ z by omega)
      _ ≤ k*(g*z) := by
        simpa using Nat.mul_le_mul_right (g*z) (show 1 ≤ k by omega)
  have hsmall : D < k*(g*z) := by omega
  have hprod : k*(y*z)*(z+g*y)+k*(g*z)+k*g^2*y =
      D*(g*y*z)+D := by nlinarith only [heq]
  have hless : k*(z+g*y) < g*D := by
    by_contra! h
    have hh := Nat.mul_le_mul_left (y*z) h
    nlinarith only [hh,hprod,hsmall,Nat.zero_le (k*g^2*y)]
  refine ⟨hless, ?_⟩
  have hleft := Nat.mul_lt_mul_of_pos_left hless (Nat.mul_pos hyp hzp)
  have hright := Nat.mul_le_mul_left (k*g*y^2) (show g*y+z ≤ 2*z by omega)
  have hden : g*y*z < (g*y+1)*(z+1) := by nlinarith
  have hqgyz := Nat.mul_lt_mul_of_pos_left hden hq
  rw [← hquot] at hqgyz
  have hscaled := Nat.mul_lt_mul_of_pos_left hqgyz (Nat.mul_pos hk hyp)
  have hout : (k*y*q)*(g*y*z)<(D+2*k*y)*(g*y*z) := by
    nlinarith only [hleft,hright,hscaled]
  exact Nat.lt_of_mul_lt_mul_right hout

private theorem scaled_quotient_lower {g y z q k D r : ℕ}
    (hg : 2 ≤ g) (hy : 2 ≤ y) (hz : 0 < z) (hk : 0 < k)
    (hDpos : 0 < D) (hD : D ≤ y^2-1)
    (hp : k*((g+y*z)*(g*y+z)) = D*(g*y*z+1))
    (hr : (g*y+z)*r = g*y*z+1)
    (hq : (g*y+z)^2 = q*((g*y+1)*(z+1))) : D < k*y*q := by
  have hsum : 0 < g*y+z := by positivity
  have hden : (g*y+1)*(z+1) = (g*y+z)*(r+1) := by
    nlinarith only [hr]
  have hq' : g*y+z = q*(r+1) := by
    apply Nat.eq_of_mul_eq_mul_left hsum
    rw [hden] at hq
    nlinarith only [hq]
  have hr' : k*(g+y*z)=D*r := by
    apply Nat.eq_of_mul_eq_mul_left hsum
    nlinarith only [hp, congrArg (D*·) hr]
  have hmatch : q*(k*(g+y*z)+D)=D*(g*y+z) := by
    rw [hr']
    nlinarith only [congrArg (D*·) hq']
  have hbase : 0 < y^2-1 := by
    have : 1 < y^2 := by nlinarith
    omega
  have hfactor : 1 < k*g := by
    have hh : g ≤ k*g := by
      simpa only [one_mul] using Nat.mul_le_mul_right g (show 1 ≤ k by omega)
    exact lt_of_lt_of_le (by omega) hh
  have hn : D < k*g*(y^2-1) :=
    hD.trans_lt (by simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hfactor hbase)
  have hsplit : (y^2-1)+1=y^2 := Nat.sub_add_cancel (by nlinarith)
  have hcross : D*(k*(g+y*z)+D) < (k*y*q)*(k*(g+y*z)+D) := by
    have hm := Nat.mul_lt_mul_of_pos_left hn hDpos
    have hadd := congrArg (fun n => D*k*g*n) hsplit
    have hqscale := congrArg (fun n => k*y*n) hmatch
    nlinarith only [hm,hadd,hqscale]
  exact Nat.lt_of_mul_lt_mul_right hcross

/-- The product plus one is the least common multiple of the two sums. -/
def H1 : Prop :=
  ∀ g y z d q : ℕ,
    1 < g → 33 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →
    (g+1)*(y*z+1) ∣ (g+y*z)^2 →
    0 < d → d < 2*(y-1) → d % 2 = 0 →
    (g+1 ∣ ((y+1)*(d+(y-1)*y*(1+2*y)))^2) →
    (g*y+1 ∣ ((y+1)*(d+(y-1)*(y+2)))^2) →
    5 ≤ q → (g*y+z)^2 = q*((g*y+1)*(z+1)) →
    g.Coprime y → g.Coprime z → y.Coprime z →
    (g+y*z ∣ g*y*z+1) → (g*y+z ∣ g*y*z+1) →
    let D := Nat.gcd (g+y*z) (g*y+z)
    D ∣ y^2-1 → D < y^2-1 →
    (g+y*z).lcm (g*y+z) = g*y*z+1 →
    z+g*y < g*D → D < y*q → y*q < D+2*y → 2*q ≤ y+3 → False

/-- The product plus one is an odd multiple of the least common multiple,
with cofactor at least three. -/
def H2 : Prop :=
  ∀ g y z d q k : ℕ,
    1 < g → 33 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →
    (g+1)*(y*z+1) ∣ (g+y*z)^2 →
    0 < d → d < 2*(y-1) → d % 2 = 0 →
    (g+1 ∣ ((y+1)*(d+(y-1)*y*(1+2*y)))^2) →
    (g*y+1 ∣ ((y+1)*(d+(y-1)*(y+2)))^2) →
    5 ≤ q → (g*y+z)^2 = q*((g*y+1)*(z+1)) →
    g.Coprime y → g.Coprime z → y.Coprime z →
    (g+y*z ∣ g*y*z+1) → (g*y+z ∣ g*y*z+1) →
    let D := Nat.gcd (g+y*z) (g*y+z)
    D ∣ y^2-1 → D < y^2-1 →
    Odd k → 3 ≤ k → (g+y*z).lcm (g*y+z)*k = g*y*z+1 →
    k*(z+g*y) < g*D → D < k*y*q → k*y*q < D+2*k*y → 3*k*y < D →
    6*q ≤ y+11 → False

theorem main : H1 → H2 → OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1.H2 := by
  intro hOne hMany g y z d q hg hy hgo hyo hzo ho hcr hd hdb hde hdc hdc'
    hq hquot hgy hgz hyz hfirst hsecond
  let D := Nat.gcd (g+y*z) (g*y+z)
  change D ∣ y^2-1 → D < y^2-1 → z < g*D → y*q < D+3*y → 2*q ≤ y+5 → False
  intro hDd hDl _ _ _
  have hg2 : 2 ≤ g := hg
  have hy2 : 2 ≤ y := by omega
  have hgy2 : 1 < g*y := by nlinarith
  have hz2 : 1 < z := by omega
  obtain ⟨k,hk⟩ := Nat.lcm_dvd hfirst hsecond
  have hkpos : 0 < k := by
    by_contra! hk0
    have he : k=0 := by omega
    simp [he] at hk
  obtain ⟨r,hr,he,_⟩ := CrystalVieta.odd_crystal_factor (hgo.mul hyo) hzo
    hgy2 hz2 (by omega) hquot
  have hkodd : Odd k := by
    obtain ⟨u,hu⟩ := Nat.dvd_lcm_right (g+y*z) (g*y+z)
    have hcancel : (g*y+z)*r=(g*y+z)*(u*k) := by
      calc
        (g*y+z)*r = g*y*z+1 := he
        _ = ((g+y*z).lcm (g*y+z))*k := hk
        _ = (g*y+z)*(u*k) := by rw [hu, mul_assoc]
    have hrk : r=u*k := Nat.eq_of_mul_eq_mul_left (by omega) hcancel
    exact hr.of_dvd_nat ⟨u, by simpa [Nat.mul_comm] using hrk⟩
  have hp : k*((g+y*z)*(g*y+z))=D*(g*y*z+1) := by
    calc
      k*((g+y*z)*(g*y+z))=k*(D*((g+y*z).lcm (g*y+z))) := by
        rw [Nat.gcd_mul_lcm]
      _ = D*((g+y*z).lcm (g*y+z)*k) := by ring
      _ = D*(g*y*z+1) := by rw [← hk]
  obtain ⟨hzB,hqB⟩ := scaled_bounds hg2 hy2 ho
    (first_component_bound hg2 ho hfirst) hDl.le hkpos hp (by omega) hquot
  obtain ⟨m,hm⟩ := hDd
  have hDpos : 0 < D := Nat.gcd_pos_of_pos_left _ (by positivity)
  have hqLower := scaled_quotient_lower hg2 hy2 (by omega) hkpos hDpos hDl.le hp he hquot
  have hm2 : 2 ≤ m := by
    by_contra! h
    interval_cases m <;> simp_all
  have hy2sq : 2*D < y^2 := by
    have hm' := Nat.mul_le_mul_left D hm2
    have hsub : y^2-1 < y^2 := by
      have : 1 ≤ y^2 := by nlinarith
      omega
    nlinarith only [hm',hm,hsub]
  by_cases hko : k=1
  · subst k
    simp only [mul_one,one_mul] at hk hzB hqB hqLower
    have hqB' : 2*q ≤ y+3 := by
      by_contra! h
      have hh := Nat.mul_le_mul_left y (show y+4 ≤ 2*q by omega)
      nlinarith only [hh,hy2sq,hqB]
    exact hOne g y z d q hg hy hgo hyo hzo ho hcr hd hdb hde hdc hdc'
      hq hquot hgy hgz hyz hfirst hsecond ⟨m,hm⟩ hDl hk.symm hzB hqLower hqB hqB'
  · have hThree : 3 ≤ k := by
      obtain ⟨j,hj⟩ := hkodd
      omega
    have hqB' : 6*q ≤ y+11 := by
      by_contra! h
      have hh := Nat.mul_le_mul_left y (show y+12 ≤ 6*q by omega)
      have hmul := Nat.mul_le_mul_left (y*(q-2)) hThree
      have hqsub : q-2+2=q := by omega
      have e3 : 3*y*(q-2)+6*y=3*y*q := by
        calc
          _ = 3*y*(q-2+2) := by ring
          _ = _ := by rw [hqsub]
      have ek : k*y*(q-2)+2*k*y=k*y*q := by
        calc
          _ = k*y*(q-2+2) := by ring
          _ = _ := by rw [hqsub]
      nlinarith only [hh,hmul,hy2sq,hqB,e3,ek]
    have hDlarge : 3*k*y < D := by
      have hh := Nat.mul_le_mul_left (k*y) hq
      nlinarith only [hh,hqB]
    exact hMany g y z d q k hg hy hgo hyo hzo ho hcr hd hdb hde hdc hdc'
      hq hquot hgy hgz hyz hfirst hsecond ⟨m,hm⟩ hDl hkodd hThree hk.symm hzB hqLower hqB hDlarge hqB'

end OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1_H2_R1
