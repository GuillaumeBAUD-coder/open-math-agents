import OMAStatements.S_mo_302130
import Mathlib

open Matrix Finset OMA.S_mo_302130

namespace ShiftedPowerDeterminant

private theorem square_zero_expansion {R : Type*} [CommRing R] (x d : R) (hd : d^2=0) (k : ℕ) :
    (x+d)^(k+1) = x^(k+1) + (k+1 : ℕ) * x^k * d := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ (x+d), ih]
    calc
      _ = x^(k+1+1) + (k+1+1 : ℕ) * x^(k+1) * d + (k+1 : ℕ)*x^k*d^2 := by
        simp only [Nat.cast_add, Nat.cast_one, pow_succ x]
        ring
      _ = _ := by rw [hd, mul_zero, add_zero]

private theorem shift_pow {R : Type*} [CommRing R] (x d : R) (hd : d^2=0) (n : ℕ)
    (hn : (n:R)*d=0) : (x+d)^n=x^n := by
  obtain (_ | k) := n
  · simp
  rw [square_zero_expansion x d hd k]
  rw [show ((k+1 : ℕ) : R)*x^k*d = ((k+1 : ℕ) : R)*d*x^k by ring, hn,
    zero_mul, add_zero]

private theorem step_dvd (n d : ℕ) (h : d ∣ n) (z : ℤ) :
    (d:ℤ)^2 ∣ (z+(d:ℤ))^n-z^n := by
  let R := ZMod (d^2)
  have hd : (d:R)^2=0 := by rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  have hn : (n:R)*(d:R)=0 := by
    obtain ⟨k,hk⟩ := h
    rw [hk, Nat.cast_mul]
    calc
      _ = (d:R)^2*(k:R) := by ring
      _ = _ := by rw [hd, zero_mul]
  have hs := shift_pow (z:R) (d:R) hd n hn
  have hc : (((z+(d:ℤ))^n-z^n : ℤ) : R) = 0 := by
    push_cast
    rw [hs, sub_self]
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc

private theorem det_sub_column {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℤ)
    {p q : I} (h : p ≠ q) :
    (M.updateCol p (fun i => M i p-M i q)).det = M.det := by
  simpa [sub_eq_add_neg] using M.det_updateCol_add_smul_self h (-1)

private theorem factor_column {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℤ)
    (p : I) (d : ℤ) (hd : ∀ i, d ∣ M i p) :
    ∃ u : I → ℤ, M.det = d*(M.updateCol p u).det := by
  choose u hu using hd
  refine ⟨u, ?_⟩
  have hs : d • u = fun i => M i p := by
    funext i
    exact (hu i).symm
  rw [← det_updateCol_smul, hs, updateCol_eq_self]

private theorem two_factors {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℤ)
    {p q : I} (hpq : p ≠ q) (d e : ℤ)
    (hd : ∀ i, d ∣ M i p) (he : ∀ i, e ∣ M i q) : d*e ∣ M.det := by
  obtain ⟨u,hu⟩ := factor_column M p d hd
  obtain ⟨v,hv⟩ := factor_column (M.updateCol p u) q e (fun i => by
    simpa [Matrix.updateCol_ne hpq.symm] using he i)
  refine ⟨((M.updateCol p u).updateCol q v).det, ?_⟩
  rw [hu,hv]
  ring

private def powerMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => ((i:ℤ)+j)^n

-- The two column shifts contribute the factors m² and 2².
private theorem even_case (m : ℕ) (hm : 2 ≤ m) : ((2*m : ℕ) : ℤ)^2 ∣ a (2*m) := by
  let M := powerMatrix (2*m)
  let p : Fin (2*m) := ⟨m, by omega⟩
  let q : Fin (2*m) := ⟨m+1, by omega⟩
  let r : Fin (2*m) := ⟨0, by omega⟩
  let s : Fin (2*m) := ⟨m-1, by omega⟩
  have hpr : p ≠ r := by intro h; have := congrArg Fin.val h; simp [p,r] at this; omega
  have hpq : p ≠ q := by intro h; have := congrArg Fin.val h; simp [p,q] at this
  have hsp : s ≠ p := by intro h; have := congrArg Fin.val h; dsimp [s,p] at this; omega
  have hqs : q ≠ s := by intro h; have := congrArg Fin.val h; dsimp [q,s] at this; omega
  let N := M.updateCol p (fun i => M i p-M i r)
  let P := N.updateCol q (fun i => N i q-N i s)
  have hdetN : N.det=M.det := det_sub_column M hpr
  have hdetP : P.det=N.det := det_sub_column N hqs
  have hd (i : Fin (2*m)) : (m:ℤ)^2 ∣ P i p := by
    change (m:ℤ)^2 ∣ (N.updateCol q _) i p
    rw [updateCol_ne hpq]
    change (m:ℤ)^2 ∣ (M.updateCol p _) i p
    rw [updateCol_self]
    change (m:ℤ)^2 ∣ ((i:ℤ)+m)^(2*m)-((i:ℤ)+0)^(2*m)
    simp only [add_zero]
    exact step_dvd (2*m) m (dvd_mul_left _ _) i
  have he (i : Fin (2*m)) : (2:ℤ)^2 ∣ P i q := by
    change (2:ℤ)^2 ∣ (N.updateCol q _) i q
    rw [updateCol_self]
    change (2:ℤ)^2 ∣ ((M.updateCol p _) i q-(M.updateCol p _) i s)
    rw [updateCol_ne hpq.symm, updateCol_ne hsp]
    have hs : ((m-1 : ℕ):ℤ)+2 = ((m+1 : ℕ):ℤ) := by omega
    change (2:ℤ)^2 ∣ ((i:ℤ)+((m+1 : ℕ):ℤ))^(2*m)-((i:ℤ)+((m-1 : ℕ):ℤ))^(2*m)
    rw [← hs, ← add_assoc]
    exact step_dvd (2*m) 2 (dvd_mul_right _ _) ((i:ℤ)+((m-1 : ℕ):ℤ))
  have h := two_factors P hpq _ _ hd he
  rw [hdetP, hdetN] at h
  change ((2*m:ℕ):ℤ)^2 ∣ M.det
  convert h using 1
  push_cast
  ring

private theorem shift_sum {R : Type*} [AddCommGroup R] (g : ℕ → R) (n : ℕ)
    (hp : ∀ x, g (x+n)=g x) (k : ℕ) :
    (∑ j∈range n, g (k+j)) = ∑ j∈range n, g j := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ = ∑ j∈range n, g (k+(j+1)) := by
        apply sum_congr rfl
        intro j _
        congr 1
        omega
      _ = (∑ j∈range (n+1), g (k+j)) - g k := by
        rw [Finset.sum_range_succ']
        simp
      _ = _ := by rw [Finset.sum_range_succ, hp, add_sub_cancel_right, ih]

-- Pair opposite residues to make the column sum vanish modulo n².
private theorem odd_case (n : ℕ) (hn : Odd n) (hpos : 0 < n) :
    (n:ℤ)^2 ∣ a n := by
  let R := ZMod (n^2)
  let g (j : ℕ) : R := (j:R)^n
  have hnz : (n:R)^2=0 := by rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  have hnz' : (n:R)*(n:R)=0 := by simpa [pow_two] using hnz
  have hperiod (j : ℕ) : g (j+n)=g j := by
    simp only [g, Nat.cast_add]
    exact shift_pow (j:R) (n:R) hnz n hnz'
  have hzero : g 0=0 := by simp [g, hpos.ne']
  obtain ⟨m,hm⟩ := hn
  have hpair (j : ℕ) (hj : j < m) : g ((m+1)+(m-1-j)) = -g (j+1) := by
    have he : (((m+1)+(m-1-j) : ℕ):R)+((j+1:ℕ):R)=(n:R) := by
      rw [← Nat.cast_add]
      congr 1
      omega
    have hc : (((m+1)+(m-1-j) : ℕ):R) = -((j+1:ℕ):R)+(n:R) := by
      linear_combination he
    change ((((m+1)+(m-1-j) : ℕ):R)^n) = -(((j+1:ℕ):R)^n)
    rw [hc, shift_pow _ _ hnz n hnz', Odd.neg_pow ⟨m,hm⟩]
  have hsum : (∑ j∈range n,g j)=0 := by
    have hrev : (∑ j∈range m,g ((m+1)+j)) = -(∑ j∈range m,g (j+1)) := by
      rw [← Finset.sum_range_reflect (fun j => g ((m+1)+j)) m, ← sum_neg_distrib]
      exact sum_congr rfl (fun j hj => hpair j (mem_range.mp hj))
    have hnm : n=(m+1)+m := by omega
    calc
      _ = ∑ j∈range ((m+1)+m), g j := congrArg (fun t => ∑ j∈range t, g j) hnm
      _ = 0 := by
        rw [sum_range_add, Finset.sum_range_succ', hrev, hzero]
        simp
  let Z := (powerMatrix n).map (Int.castRingHom R)
  have hrow (i : Fin n) : ∑ j, Z i j=0 := by
    change ∑ j : Fin n, ((((i:ℤ)+(j:ℤ))^n : ℤ):R)=0
    simp only [Int.cast_pow, Int.cast_add, Int.cast_natCast]
    have hs : (∑ j : Fin n, g (i.val+j.val))=0 := by
      exact (Fin.sum_univ_eq_sum_range (fun j => g (i.val+j)) n).trans
        ((shift_sum g n hperiod i.val).trans hsum)
    simpa only [g,Nat.cast_add] using hs
  let i : Fin n := ⟨0,hpos⟩
  have hdet := Matrix.det_updateCol_sum Z i (fun _ => (1:R))
  simp only [one_smul, hrow] at hdet
  have hh : (Z.updateCol i (fun _ => 0)).det=0 := by
    have hzv : (fun _ : Fin n => (0:R)) = 0 := by
      funext j
      simp
    rw [hzv]
    simpa only [zero_smul, zero_mul] using (Matrix.det_updateCol_smul Z i (0:R) (0 : Fin n → R))
  rw [hh] at hdet
  have hcast : ((a n : ℤ):R)=0 := by
    change (Int.castRingHom R) (powerMatrix n).det=0
    rw [RingHom.map_det]
    exact hdet.symm
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast

theorem result (n : ℕ) (hn : 3 ≤ n) : (n:ℤ)^2 ∣ a n := by
  rcases Nat.even_or_odd n with ⟨m,hm⟩ | h
  · have he : n=2*m := by omega
    rw [he]
    exact even_case m (by omega)
  · exact odd_case n h (by omega)

end ShiftedPowerDeterminant

theorem OMA.solution : ∀ n : ℕ, 3 ≤ n → (n : ℤ)^2 ∣ a n :=
  ShiftedPowerDeterminant.result