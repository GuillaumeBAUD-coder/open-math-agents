import FormalConjectures.ErdosProblems.«604»

/-!
Deleting the richest pin gives a lower bound for the sum of all pinned distance counts.
At half scale this shows equivalence of the average and best-pin square-root-log bounds.
For a potential counterexample the largest perpendicular bisector must have intermediate
occupancy: Cauchy–Schwarz handles small occupancy, and two circles meet in at most
two points, which handles large occupancy. The two remaining cases split at √n.
-/

-- Credit: @zarnab222-dev
open Finset Erdos604 Filter
open scoped EuclideanGeometry Classical
namespace E604Rank

theorem mono {A B : Finset ℝ²} (sub : A ⊆ B) (x : ℝ²) :
    distinctDistancesFrom A x ≤ distinctDistancesFrom B x := by
  classical
  unfold distinctDistancesFrom
  apply card_le_card
  apply image_subset_image
  exact @Finset.erase_subset_erase _ (fun a b : ℝ² => Classical.propDecidable (a=b)) x _ _ sub

theorem scarcity (A : Finset ℝ²) (m : ℕ) (hm : 0 < m) :
    (A.filter fun x => distinctDistancesFrom A x < pinnedDistinctDistances m).card < m := by
  classical
  by_contra! enough
  obtain ⟨T,sub,size⟩ := exists_subset_card_eq enough
  have inside : T ⊆ A := sub.trans (filter_subset _ _)
  have min : pinnedDistinctDistances m ≤ T.sup (distinctDistancesFrom T) :=
    Nat.sInf_le ⟨T,size,rfl⟩
  obtain ⟨x,hx,attained⟩ := exists_mem_eq_sup T (by rw [← card_pos,size]; exact hm) (distinctDistancesFrom T)
  have less := (mem_filter.mp (sub hx)).2
  rw [attained] at min
  exact (not_lt_of_ge (min.trans (mono inside x))) less

theorem many (A : Finset ℝ²) (m : ℕ) (hm : 0 < m) :
    A.card+1-m ≤ (A.filter fun x => pinnedDistinctDistances m ≤ distinctDistancesFrom A x).card := by
  have low := scarcity A m hm
  have tally := A.card_filter_add_card_filter_not (fun x => distinctDistancesFrom A x < pinnedDistinctDistances m)
  simp only [not_lt] at tally
  omega

theorem sum_bound (A : Finset ℝ²) (m : ℕ) (hm : 0 < m) :
    (A.card+1-m)*pinnedDistinctDistances m ≤ ∑ x ∈ A, distinctDistancesFrom A x := by
  let S := A.filter fun x => pinnedDistinctDistances m ≤ distinctDistancesFrom A x
  have lo : ∑ _ ∈ S, pinnedDistinctDistances m ≤ ∑ x ∈ S, distinctDistancesFrom A x :=
    sum_le_sum (fun x hx => (mem_filter.mp hx).2)
  have small := sum_le_sum_of_subset_of_nonneg (filter_subset (fun x => pinnedDistinctDistances m ≤ distinctDistancesFrom A x) A)
    (fun x _ _ => Nat.zero_le (distinctDistancesFrom A x))
  simp only [sum_const,smul_eq_mul] at lo
  exact (Nat.mul_le_mul_right _ (many A m hm)).trans (lo.trans small)

theorem sum_all (A : Finset ℝ²) :
    ∑ i ∈ range A.card, pinnedDistinctDistances (i+1) ≤ ∑ x ∈ A, distinctDistancesFrom A x := by
  classical
  induction A using Finset.strongInductionOn
  case _ A ih =>
    by_cases empty : A = ∅
    · simp [empty]
    have someA := nonempty_iff_ne_empty.mpr empty
    obtain ⟨x,hx,peak⟩ := exists_mem_eq_sup A someA (distinctDistancesFrom A)
    have minimal : pinnedDistinctDistances A.card ≤ A.sup (distinctDistancesFrom A) :=
      Nat.sInf_le ⟨A,rfl,rfl⟩
    have card : (A.erase x).card+1 = A.card := card_erase_add_one hx
    have previous := ih (A.erase x) (erase_ssubset hx)
    have lower := sum_le_sum (s := A.erase x) (fun y _ => mono (erase_subset x A) y)
    have now : pinnedDistinctDistances A.card ≤ distinctDistancesFrom A x := peak ▸ minimal
    rw [← card, sum_range_succ,card,← sum_erase_add _ _ hx]
    exact Nat.add_le_add (previous.trans lower) now

open Asymptotics

theorem one_pin_to_average (pins : type_of% @Erdos604.erdos_604.variants.sqrt_log) :
    type_of% @Erdos604.erdos_604.variants.average := by
  obtain ⟨K,posK,hK⟩ := isBigO_iff'.mp pins
  obtain ⟨N,start⟩ := eventually_atTop.mp hK
  refine ⟨1/(4*K),by positivity,eventually_atTop.mpr ⟨2*(N+2),?_⟩⟩
  intro n hn A hA
  let m := (n+1)/2
  have mN : N ≤ m := by dsimp [m]; omega
  have two : 2 ≤ m := by dsimp [m]; omega
  have mn : m ≤ n := by dsimp [m]; omega
  have npos : (1:ℝ) < n := by exact_mod_cast (by omega : 1<n)
  have mpos : (1:ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have Lm : 0 < Real.sqrt (Real.log m) := Real.sqrt_pos.mpr (Real.log_pos mpos)
  have Ln : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.mpr (Real.log_pos npos)
  have logle : (Real.log m).sqrt ≤ (Real.log n).sqrt := Real.sqrt_le_sqrt (Real.log_le_log (lt_trans zero_lt_one mpos) (by exact_mod_cast mn))
  have base := start m mN
  change ‖(m:ℝ)/(Real.log m).sqrt‖ ≤ K*‖(pinnedDistinctDistances m : ℝ)‖ at base
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)] at base
  have h1 := (div_le_iff₀ Lm).mp base
  have mf : (m:ℝ) ≤ K * (pinnedDistinctDistances m : ℝ) * (Real.log n).sqrt :=
    h1.trans (mul_le_mul_of_nonneg_left logle (by positivity))
  let r := n+1-m
  have rank := sum_bound A m (by omega)
  rw [hA] at rank
  have bound : (r:ℝ)*(pinnedDistinctDistances m : ℝ) ≤ (∑ x ∈ A, distinctDistancesFrom A x : ℕ) := by exact_mod_cast rank
  have n1 : (n:ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast (show n ≤ 2*m by dsimp [m]; omega)
  have n2 : (n:ℝ) ≤ 2*(r:ℝ) := by exact_mod_cast (show n ≤ 2*r by dsimp [r,m]; omega)
  have square := mul_le_mul n1 n2 (by positivity) (by positivity)
  have prod := mul_le_mul_of_nonneg_left mf (show (0:ℝ) ≤ r by positivity)
  have mult := mul_le_mul_of_nonneg_left bound (show 0 ≤ K*(Real.log n).sqrt by positivity)
  apply (div_le_iff₀ Ln).mpr
  rw [one_div,inv_mul_eq_div]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

theorem average_to_one_pin (avg : type_of% @Erdos604.erdos_604.variants.average) :
    type_of% @Erdos604.erdos_604.variants.sqrt_log := by
  obtain ⟨C,pos,all⟩ := avg
  apply isBigO_iff.mpr
  refine ⟨1/C,?_⟩
  filter_upwards [all,eventually_gt_atTop (1:ℕ)] with n hn gt
  obtain ⟨B,hb⟩ := Infinite.exists_subset_card_eq ℝ² n
  have nonempty : Set.Nonempty {m : ℕ | ∃ A : Finset ℝ², A.card=n ∧ A.sup (distinctDistancesFrom A)=m} :=
    ⟨_,B,hb,rfl⟩
  obtain ⟨A,size,peak⟩ := Nat.sInf_mem nonempty
  have sum_bound := sum_le_sum (s := A) (fun x hx => le_sup (f := distinctDistancesFrom A) hx)
  rw [sum_const,smul_eq_mul,size,peak] at sum_bound
  have lb := hn A size
  let f := pinnedDistinctDistances n
  have ub : ((∑ x ∈ A, distinctDistancesFrom A x : ℕ):ℝ) ≤ (n:ℝ)*f := by exact_mod_cast sum_bound
  have npos : (0:ℝ) < n := by positivity
  have L : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.mpr (Real.log_pos (by exact_mod_cast gt))
  change ‖(n:ℝ)/(Real.log n).sqrt‖ ≤ (1/C)*‖(f:ℝ)‖
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity),one_div,inv_mul_eq_div,div_le_div_iff₀ L pos]
  have e := (div_le_iff₀ L).mp (lb.trans ub)
  apply le_of_mul_le_mul_left (a := (n:ℝ)) _ npos
  nlinarith

end E604Rank


/- Count equal-distance triples once by pin and once by perpendicular bisector. -/
open Finset Erdos604
open scoped Classical EuclideanGeometry
namespace E604Energy

theorem fiber_count {α β : Type*} (A : Finset α) (f : α → β) :
    A.card^2 ≤ (A.image f).card * ∑ u ∈ A, ∑ v ∈ A, if f v = f u then 1 else 0 := by
  classical
  let R := A.image f
  let c (r : β) := (A.filter fun x => f x = r).card
  have mass : A.card = ∑ r ∈ R, c r := card_eq_sum_card_image f A
  have cs := sum_mul_sq_le_sq_mul_sq R (fun _ => (1:ℕ)) c
  simp only [one_mul,one_pow,sum_const,smul_eq_mul,mul_one,← mass] at cs
  have index : (A : Set α).MapsTo f (R : Set β) := fun _ h => mem_image_of_mem _ h
  have energy : ∑ u ∈ A, c (f u) = ∑ r ∈ R, c r ^ 2 := by
    rw [← sum_fiberwise_of_maps_to index (fun u => c (f u))]
    apply sum_congr rfl
    intro r hr
    calc
      _ = ∑ _ ∈ A.filter (fun u => f u = r), c r := by
        apply sum_congr rfl
        intro u hu
        rw [(mem_filter.mp hu).2]
      _ = _ := by simp only [sum_const,smul_eq_mul,pow_two,c]
  rw [← energy] at cs
  simpa only [c,card_filter,R] using cs

theorem no_heavy_bisector {n M : ℕ} (A : Finset ℝ²) (size : A.card=n) (hn : 0<n)
    (thin : ∀ u ∈ A, ∀ v ∈ A, u ≠ v →
      (A.filter fun x => dist v x = dist u x).card ≤ M) :
    n ≤ (A.sup (distinctDistancesFrom A)+1)*(M+1) := by
  classical
  let N := A.sup (distinctDistancesFrom A)
  let e (x u v : ℝ²) : ℕ := if dist v x = dist u x then 1 else 0
  have pin (x : ℝ²) (hx : x ∈ A) : n^2 ≤ (N+1)*(∑ u ∈ A, ∑ v ∈ A, e x u v) := by
    have earlier := fiber_count A (fun v => dist v x)
    have image : (A.image fun v => dist v x) ⊆ insert 0 ((A.erase x).image fun v => dist v x) := by
      rintro _ h
      obtain ⟨v,hv,rfl⟩ := mem_image.mp h
      by_cases vx : v=x
      · simp [vx]
      · exact mem_insert_of_mem (mem_image_of_mem _ (mem_erase.mpr ⟨vx,hv⟩))
    have cnt := (card_le_card image).trans (card_insert_le ..)
    have rays : ((A.erase x).image fun v => dist v x).card = distinctDistancesFrom A x := by
      unfold distinctDistancesFrom
      congr! 5
    have lim := le_sup (f := distinctDistancesFrom A) hx
    rw [rays] at cnt
    rw [size] at earlier
    exact earlier.trans (Nat.mul_le_mul_right _ (by dsimp [N]; omega))
  have each (u : ℝ²) (hu : u ∈ A) : (∑ v ∈ A, ∑ x ∈ A, e x u v) ≤ n + n*M := by
    rw [← sum_erase_add _ _ hu]
    have other : (∑ v ∈ A.erase u, ∑ x ∈ A, e x u v) ≤ (A.erase u).card*M := by
      calc _ ≤ ∑ _ ∈ A.erase u, M := by
              apply sum_le_sum
              intro v hv
              simpa only [card_filter,e] using thin u hu v (mem_erase.mp hv).2 (mem_erase.mp hv).1.symm
           _ = _ := by simp
    have self : ∑ x ∈ A, e x u u = n := by simp [e,size]
    rw [self]
    have card : (A.erase u).card ≤ n := size ▸ card_le_card (erase_subset u A)
    have le := Nat.mul_le_mul_right M card
    omega
  have total := sum_le_sum pin
  simp only [sum_const,size,smul_eq_mul,←mul_sum] at total
  have swap : (∑ x ∈ A, ∑ u ∈ A, ∑ v ∈ A, e x u v) = ∑ u ∈ A, ∑ v ∈ A, ∑ x ∈ A, e x u v := by
    rw [sum_comm]
    exact sum_congr rfl (fun _ _ => sum_comm)
  rw [swap] at total
  have limit := sum_le_sum each
  simp only [sum_const,smul_eq_mul,size] at limit
  have chain := total.trans (Nat.mul_le_mul_left (N+1) limit)
  have quot : (n*n)*n ≤ (n*n)*((N+1)*(M+1)) := by nlinarith only [chain]
  exact Nat.le_of_mul_le_mul_left quot (Nat.mul_pos hn hn)


theorem rich (A : Finset ℝ²) {u v : ℝ²} (hu : u ∈ A) (hv : u ≠ v) :
    (A.filter fun x => dist v x = dist u x).card ≤ 2*A.sup (distinctDistancesFrom A) := by
  classical
  let B := A.filter fun x => dist v x = dist u x
  let R := (A.erase u).image fun x => dist x u
  have maps : (B : Set ℝ²).MapsTo (fun x => dist x u) (R : Set ℝ) := by
    intro x hx
    obtain ⟨inA,eq⟩ := mem_filter.mp hx
    have xu : x ≠ u := by
      intro xu
      subst x
      exact hv (dist_eq_zero.mp (eq.trans (dist_self u))).symm
    exact mem_image_of_mem _ (mem_erase.mpr ⟨xu,inA⟩)
  have bound (r : ℝ) : (B.filter fun x => dist x u = r).card ≤ 2 := by
    let S := B.filter fun x => dist x u = r
    by_contra! big
    obtain ⟨a,ha,b,hb,ab⟩ := one_lt_card.mp (show 1 < S.card by dsimp [S]; omega)
    have both {x : ℝ²} (h : x ∈ S) : dist x u=r ∧ dist x v=r := by
      obtain ⟨hB,hr⟩ := mem_filter.mp h
      have e := (mem_filter.mp hB).2
      exact ⟨hr,by simpa only [dist_comm v x,dist_comm u x] using e.trans (by simpa [dist_comm] using hr)⟩
    have sub : S ⊆ {a,b} := by
      intro x hx
      have h := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two (V := ℝ²)
        (by simp) hv ab (both ha).1 (both hb).1 (both hx).1 (both ha).2 (both hb).2 (both hx).2
      simpa using h
    have sz := card_le_card sub
    simp [ab] at sz
    exact (not_lt_of_ge sz) big
  have cnt := card_eq_sum_card_fiberwise maps
  have upper := sum_le_sum (s := R) (fun r _ => bound r)
  rw [← cnt] at upper
  have fix : R.card = distinctDistancesFrom A u := by
    unfold R distinctDistancesFrom
    congr! 5
  simpa [fix,mul_comm] using upper.trans (show (∑ _ ∈ R, 2) ≤ 2*A.sup (distinctDistancesFrom A) by
    simpa [fix,mul_comm] using Nat.mul_le_mul_left 2 (le_sup (f := distinctDistancesFrom A) hu))


theorem bounds {n : ℕ} (A : Finset ℝ²) (size : A.card=n) (hn : 0<n) :
    let M := A.offDiag.sup fun p => (A.filter fun x => dist p.2 x = dist p.1 x).card
    n ≤ (A.sup (distinctDistancesFrom A)+1)*(M+1) ∧
    M ≤ 2*A.sup (distinctDistancesFrom A) := by
  dsimp only
  constructor
  · apply no_heavy_bisector A size hn
    intro u hu v hv ne
    exact le_sup (s := A.offDiag) (b := (u,v)) (f := fun p : ℝ² × ℝ² => (A.filter fun x => dist p.2 x = dist p.1 x).card)
      (mem_offDiag.mpr ⟨hu,hv,ne⟩)
  · apply Finset.sup_le_iff.mpr
    intro p hp
    obtain ⟨hu,_,ne⟩ := mem_offDiag.mp hp
    exact rich A hu ne

end E604Energy

open Filter Finset Erdos604 E604Energy Asymptotics
open scoped Classical EuclideanGeometry
namespace OMA.R_Erdos604_erdos_604_variants_average_R1

def H1 : Prop := ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², A.card=n →
  let M := A.offDiag.sup fun p => (A.filter fun x => dist p.2 x = dist p.1 x).card
  (Real.log n).sqrt < (M : ℝ)+1 → M^2 ≤ n →
  (n:ℝ) ≤ K * (Real.log n).sqrt * ((A.sup (distinctDistancesFrom A) : ℕ) : ℝ)

def H2 : Prop := ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², A.card=n →
  let M := A.offDiag.sup fun p => (A.filter fun x => dist p.2 x = dist p.1 x).card
  n < M^2 → (M : ℝ)*(Real.log n).sqrt < n →
  (n:ℝ) ≤ K * (Real.log n).sqrt * ((A.sup (distinctDistancesFrom A) : ℕ) : ℝ)

theorem main : H1 → H2 → type_of% @Erdos604.erdos_604.variants.average := by
  rintro ⟨K,hK,small⟩ ⟨J,hJ,large⟩
  apply E604Rank.one_pin_to_average
  apply isBigO_iff.mpr
  let C := max 2 (max K J)
  refine ⟨C,?_⟩
  filter_upwards [small,large,eventually_gt_atTop (1:ℕ)] with n hs hl hn
  obtain ⟨B,hB⟩ := Infinite.exists_subset_card_eq ℝ² n
  have nonempty : Set.Nonempty {d : ℕ | ∃ A : Finset ℝ², A.card=n ∧ A.sup (distinctDistancesFrom A)=d} :=
    ⟨_,B,hB,rfl⟩
  obtain ⟨A,size,peak⟩ := Nat.sInf_mem nonempty
  let D := A.sup (distinctDistancesFrom A)
  let M := A.offDiag.sup fun p => (A.filter fun x => dist p.2 x = dist p.1 x).card
  let L := (Real.log n).sqrt
  have lpos : 0 < L := Real.sqrt_pos.mpr (Real.log_pos (by exact_mod_cast hn))
  obtain ⟨count,rich⟩ := bounds A size (by omega)
  change n ≤ (D+1)*(M+1) at count
  change M ≤ 2*D at rich
  have dpos : 0 < D := by
    by_contra! h
    have zero : D=0 := by omega
    have mzero : M=0 := by omega
    simp [zero,mzero] at count
    omega
  have dp : (1:ℝ) ≤ D := by exact_mod_cast dpos
  have e : (n:ℝ) ≤ ((D:ℝ)+1)*((M:ℝ)+1) := by exact_mod_cast count
  have b : (M:ℝ) ≤ 2*(D:ℝ) := by exact_mod_cast rich
  have two : (2:ℝ) ≤ C := le_max_left _ _
  have ck : K ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have cj : J ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have out : (n:ℝ) ≤ C*L*(D:ℝ) := by
    by_cases sparse : (M:ℝ)+1 ≤ L
    · calc (n:ℝ) ≤ ((D:ℝ)+1)*((M:ℝ)+1) := e
           _ ≤ (2*(D:ℝ))*L := mul_le_mul (by linarith) sparse (by positivity) (by positivity)
           _ = 2*L*(D:ℝ) := by ring
           _ ≤ _ := by gcongr
    by_cases dense : (n:ℝ) ≤ (M:ℝ)*L
    · calc (n:ℝ) ≤ (M:ℝ)*L := dense
           _ ≤ (2*(D:ℝ))*L := by gcongr
           _ = 2*L*(D:ℝ) := by ring
           _ ≤ _ := by gcongr
    by_cases side : M^2 ≤ n
    · exact (hs A size (lt_of_not_ge sparse) side).trans (by change K*L*(D:ℝ) ≤ _; gcongr)
    · exact (hl A size (lt_of_not_ge side) (lt_of_not_ge dense)).trans (by change J*L*(D:ℝ) ≤ _; gcongr)
  have eq : D = pinnedDistinctDistances n := peak
  change ‖(n:ℝ)/L‖ ≤ C*‖(pinnedDistinctDistances n : ℝ)‖
  rw [← eq,Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)]
  exact (div_le_iff₀ lpos).mpr (by nlinarith only [out])

end OMA.R_Erdos604_erdos_604_variants_average_R1
