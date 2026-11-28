import OMAStatements.S_oeis_a088862

namespace OMA.PrefixPowers

open Finset OMA.S_oeis_a088862

lemma cube_le_exp (J : ℕ) (hJ : 10 ≤ J) : J^3 ≤ 2^J := by
  induction J, hJ using Nat.le_induction with
  | base => decide
  | succ J hJ ih =>
    rw [pow_succ 2 J]
    apply le_trans _ (Nat.mul_le_mul_right 2 ih)
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hJ
    ring_nf
    omega

-- At X = 2^J, the two elementary Chebyshev bounds give
-- 2^J ≤ J π(2^J) + J + 1.
lemma growth (n J : ℕ) (hJ : J = (n+1)^2+16) :
    (n+1)*(J*n+1) < (2^J).primeCounting := by
  have h0 := Chebyshev.psi_ge (2^J)
  have h1 := Chebyshev.psi_le_primeCounting_mul_log (2^J)
  have h2 : (2:ℝ)^J+1 ≤ 2^(J+1) := by
    rw [pow_succ]
    have : (1:ℝ) ≤ 2^J := one_le_pow₀ (by norm_num)
    linarith
  have h3 := Real.log_le_log (by positivity : 0 < (2:ℝ)^J+1) h2
  push_cast at h0 h1
  rw [Real.log_pow] at h1 h3
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : (2:ℝ)^J ≤ (((2^J).primeCounting : ℕ):ℝ)*J + (J+1) := by
    apply le_of_mul_le_mul_right _ hl
    push_cast at h3
    nlinarith [h0.trans h1]
  have hnat : 2^J ≤ (2^J).primeCounting*J+(J+1) := by exact_mod_cast he
  have hcube := cube_le_exp J (by omega)
  by_contra! h
  have hmul := Nat.mul_le_mul_right J h
  have hJbig : 0 < J := by omega
  have hr : (n+1)*(J*n+1)*J+(J+1) < J^3 := by
    subst J
    ring_nf
    omega
  omega

-- An exceptional pair of exponents determines at most one possible prime,
-- the least integer whose d-th power reaches 2^t.
noncomputable def rootAt (dt : ℕ × ℕ) : ℕ := sInf {s : ℕ | 2 ^ dt.2 ≤ s ^ dt.1}

lemma root_eq (d t p : ℕ) (lo : (p-1)^d < 2^t) (hi : 2^t ≤ p^d) :
    rootAt (d,t) = p := by
  apply IsLeast.csInf_eq
  refine ⟨hi, ?_⟩
  intro q hq
  change 2^t ≤ q^d at hq
  by_contra! h
  exact (not_lt_of_ge hq) ((Nat.pow_le_pow_left (by omega : q ≤ p-1) d).trans_lt lo)

lemma good_prime (n : ℕ) : ∃ p : ℕ, p.Prime ∧
    ∀ d ≤ n, ∀ t, 2^t ≤ p^d → ¬ (p-1)^d < 2^t := by
  classical
  let J := (n+1)^2+16
  let codes := (range (n+1)) ×ˢ (range (J*n+1))
  have hg := growth n J rfl
  have hc : (codes.image rootAt).card < (2^J).primesLE.card := by
    rw [Nat.primesLE_card_eq_primeCounting]
    exact (Finset.card_image_le.trans (le_of_eq (by simp [codes]))).trans_lt hg
  obtain ⟨p,hp,hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  obtain ⟨hbound,hprime⟩ := Nat.mem_primesLE.mp hp
  refine ⟨p,hprime,?_⟩
  intro d hd t hi lo
  have hdt : t ≤ J*n := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    calc 2^t ≤ p^d := hi
         _ ≤ (2^J)^d := Nat.pow_le_pow_left hbound d
         _ = 2^(J*d) := (pow_mul 2 J d).symm
         _ ≤ 2^(J*n) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left J hd)
  apply hnot
  exact Finset.mem_image.mpr ⟨(d,t), by simp [codes,hd,hdt], root_eq d t p lo hi⟩

-- This single-bin gap separates consecutive possible carriers of the same prefix.
lemma gap_bound (p i d : ℕ) (hp : 1 < p) (hi : 0 < i) (hd : 0 < d) :
    (p^i+1)*(p-1)^d ≤ p^i*p^d := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  have hpi : p ≤ p^i := by
    simpa using (Nat.pow_le_pow_right (by omega : 0 < p) (show 1 ≤ i by omega))
  have h₀ : (p^i+1)*(p-1) ≤ p^i*p := by
    have hp' : p-1+1=p := by omega
    nlinarith [congrArg (fun t => t*p^i) hp']
  calc
    (p^i+1)*(p-1)^(e+1) = ((p^i+1)*(p-1))*(p-1)^e := by ring
    _ ≤ (p^i*p)*p^e := Nat.mul_le_mul h₀ (Nat.pow_le_pow_left (by omega) e)
    _ = _ := by rw [pow_succ]; ring

lemma eligible_power (n p : ℕ) (hp : p.Prime)
    (hgap : ∀ d ≤ n, ∀ t, 2^t ≤ p^d → ¬ (p-1)^d < 2^t) : eligible n (p^n) := by
  refine ⟨pow_pos hp.pos _, by simp [hp.primeFactorsList_pow], ?_⟩
  intro a ha ha' b hb hb' t hab
  obtain ⟨i,hi,rfl⟩ := (Nat.dvd_prime_pow hp).mp ha
  obtain ⟨j,hj,rfl⟩ := (Nat.dvd_prime_pow hp).mp hb
  have hij : i ≤ j := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hab ▸ Nat.div_le_self _ _)
  by_contra hne
  have hij' : i < j := by
    by_contra! nh
    exact hne (congrArg (p^·) (by omega))
  obtain ⟨d,hdj⟩ := Nat.exists_eq_add_of_le hij
  have hd : 0 < d := by omega
  have hi' : 0 < i := by
    by_contra! h
    simp [show i=0 by omega] at ha'
  have hpos : 0 < 2^t := by positivity
  have hlo := (Nat.le_div_iff_mul_le hpos).mp hab.ge
  have hup := (Nat.div_lt_iff_lt_mul hpos).mp (Nat.lt_succ_of_le hab.le)
  rw [hdj,pow_add] at hlo hup
  have hi₀ := (Nat.le_of_mul_le_mul_left hlo (pow_pos hp.pos i))
  apply hgap d (by omega) t hi₀
  by_contra! hge
  exact (not_lt_of_ge ((Nat.mul_le_mul_left (p^i+1) hge).trans (gap_bound p i d hp.one_lt hi' hd))) hup

end OMA.PrefixPowers

theorem OMA.solution : type_of% @OMA.S_oeis_a088862.main := by
  classical
  intro n
  obtain ⟨p,hp,h⟩ := OMA.PrefixPowers.good_prime n
  have hex : ∃ m, OMA.S_oeis_a088862.eligible n m := ⟨p^n,OMA.PrefixPowers.eligible_power n p hp h⟩
  exact ⟨Nat.find hex,Nat.find_spec hex,fun _ hm => Nat.find_min' hex hm⟩
