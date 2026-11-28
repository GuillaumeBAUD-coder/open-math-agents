import OMAReductions.R_oeis_a227899_R1

import Mathlib

namespace PrimeSumOfSquares

private def witnesses : ℕ → List ℕ
  | 0 => [3, 3, 5, 5, 3, 5, 3, 5, 5, 3, 3, 11, 7, 5, 11, 3, 7, 11, 5, 3, 5, 3, 5, 5, 3]
  | 1 => [19, 7, 5, 5, 5, 5, 11, 7, 5, 31, 5, 3, 7, 17, 3, 3, 7, 5, 17, 5, 3, 7, 11, 7, 3]
  | 2 => [29, 29, 5, 5, 3, 5, 17, 5, 7, 5, 3, 3, 31, 7, 3, 29, 29, 5, 17, 11, 19, 11, 17, 5, 31]
  | 3 => [5, 3, 7, 5, 5, 5, 7, 17, 5, 3, 19, 11, 17, 5, 11, 3, 3, 5, 7, 5, 5, 11, 5, 5, 11]
  | 4 => [3, 11, 11, 37, 5, 3, 3, 5, 5, 11, 5, 7, 11, 17, 5, 3, 59, 5, 5, 11, 5, 3, 5, 5, 3]
  | 5 => [29, 3, 5, 7, 3, 3, 11, 37, 19, 31, 5, 11, 5, 5, 31, 29, 3, 7, 19, 3, 3, 17, 31, 7, 11]
  | 6 => [19, 3, 5, 7, 3, 29, 7, 31, 5, 61, 3, 7, 7, 5, 31, 5, 7, 17, 7, 5, 79, 3, 5, 5, 5]
  | 7 => [19, 11, 5, 5, 5, 3, 3, 47, 7, 61, 19, 3, 11, 7, 11, 19, 7, 5, 17, 61, 3, 3, 17, 5, 31]
  | 8 => [79, 17, 5, 5, 11, 3, 11, 7, 5, 61, 5, 17, 11, 5, 5, 19, 19, 11, 17, 3, 3, 17, 11, 7, 31]
  | 9 => [79, 17, 37, 17, 5, 5, 3, 11, 47, 3, 29, 19, 5, 19, 5, 3, 3, 11, 17, 11, 19, 17, 5, 5, 131]
  | 10 => [5, 11, 37, 5, 31, 29, 3, 5, 7, 3, 5, 3, 11, 7, 3, 5, 11, 7, 19, 131, 3, 7, 7, 7, 3]
  | 11 => [19, 19, 5, 5, 3, 3, 47, 5, 17, 11, 3, 61, 37, 5, 31, 5, 17, 5, 5, 3, 5, 37, 61, 19, 61]
  | 12 => [59, 11, 7, 17, 151, 5, 7, 5, 7, 3, 19, 17, 17, 37, 61, 5, 3, 17, 5, 5, 79, 7, 5, 29, 3]
  | 13 => [3, 7, 37, 17, 131, 5, 7, 11, 29, 5, 89, 11, 37, 7, 5, 29, 17, 5, 5, 11, 3, 31, 7, 5, 241]
  | 14 => [29, 19, 7, 5, 61, 3, 7, 7, 7, 5, 29, 3, 17, 7, 5, 29, 11, 5, 5, 31, 5, 7, 107, 5, 31]
  | 15 => [79, 11, 17, 5, 3, 19, 3, 5, 5, 5, 3, 19, 5, 17, 191, 3, 59, 7, 17, 31, 79, 3, 5, 19, 3]
  | 16 => [5, 7, 11, 19, 11, 3, 7, 5, 7, 3, 19, 29, 7, 37, 61, 3, 19, 7, 37, 5, 19, 11, 17, 17, 3]
  | 17 => [59, 3, 7, 59, 5, 3, 7, 5, 5, 5, 5, 29, 5, 5, 3, 19, 11, 31, 5, 3, 19, 17, 17, 5, 241]
  | 18 => [3, 11, 5, 29, 11, 5, 11, 5, 17, 131, 5, 7, 5, 5, 5, 5, 3, 7, 7, 5, 5, 7, 31, 19, 3]
  | 19 => [19, 11, 7, 29, 241, 19, 3, 5, 17, 191, 5, 11, 5, 17, 61, 59, 29, 7, 17, 131, 3, 7, 5, 47, 5]
  | 20 => [5, 3, 37, 5, 11, 19, 7, 17, 5, 11, 19, 31, 5, 17, 3, 479, 19, 7, 7, 3, 3, 29, 5, 5, 421]
  | 21 => [5, 3, 7, 5, 3, 5, 3, 61, 7, 3, 3, 7, 17, 47, 11, 5, 11, 5, 5, 11, 29, 7, 5, 5, 5]
  | 22 => [19, 31, 5, 17, 131, 3, 47, 37, 7, 31, 5, 7, 17, 17, 31, 3, 17, 5, 19, 5, 3, 3, 17, 47, 131]
  | 23 => [19, 3, 17, 19, 3, 5, 11, 7, 37, 241, 5, 11, 17, 7, 271, 5, 11, 7, 19, 3, 29, 7, 7, 5, 5]
  | 24 => [5, 19, 5, 5, 3, 5, 3, 11, 5, 3, 89, 7, 47, 5, 5, 19, 7, 5, 7, 5, 5, 17, 7, 17, 61]
  | 25 => [3, 11, 7, 5, 11, 3, 3, 11, 17, 3, 29, 11, 31, 5, 31, 59, 17, 7, 7, 5, 3, 47, 67, 59, 3]
  | 26 => [29, 3, 7, 7, 5, 5, 7, 5, 5, 5, 3, 17, 7, 17, 5, 5, 7, 5, 47, 5, 3, 11, 5, 7, 11]
  | 27 => [59, 3, 47, 5, 31, 149, 11, 17, 17, 3, 5, 17, 11, 7, 5, 5, 17, 17, 37, 11, 5, 11, 11, 29, 11]
  | 28 => [79, 29, 5, 29, 241, 59, 11, 5, 19, 11, 409, 7, 5, 17, 191, 3, 11, 5, 7, 5, 5, 7, 5, 107, 3]
  | 29 => [29, 11, 61, 19, 3, 3, 19, 5, 5, 61, 3, 3, 11, 5, 3, 59, 3, 11, 5, 5, 19, 7, 5, 7, 5]
  | 30 => [229]
  | _ => []

private def witness (i : ℕ) (j : Fin 25) : ℕ := (witnesses i).getD j.val 0

private def smallPrimeProduct : ℕ := 2726988291753707962519660864579670665115341019393910656430522793434078724563541507233530107092495105029525965453749152828702605258285638934852102012671213767678945262203007199926116081202200204013043944171931789009065213927853848018336702696899610980454042137112191403491054169666815966975538250980010260181667407332679861062588015351319148894468273424500677235200909908661427397896962833286101764437390810207566136703881426453775363346047271953679380660454376291214015328307007729341463059718628836902992908911646700186684726742900532002198293678434415144719311817221536956523804462351236037530610536783051486853105145589226010873882427790847050673385102483160402555892777180268818380720057730675733717618127090566216284748958686615097097342121605620794709915252550344163988413079944155167690815238791752180577281214757902439930758314091340689133105797625781131639976264144333892242937924297946632567000188508954151464162333850632579954256724522959773796249744678939038172228648981688792601374845604151583521624145703086862268738342805121778695239491845068509501709756135293558778485071206361920644349117393412213861163343050035219686431401404138127117901665405723694599253263416741799990800778090798963358824179567682750589947305052644584857090120183766319566266624747039218620200189163742143854302187635550111771804517253767667146392005724431407841173887888926089194141457316456076268412130833446882666204957643249775160894511268571888309430009283324730429943206501565217120686912091874099949235867956791470312950310502782491211241671462620089260340716329661134114614965589980723963585406473700036067035594969508440106699947943002200404785117335215723149036580297934328294573530302467530555757667987856078250439480848873253364455241836742715837452094024186257226121067244229149195811400175356005487742622468372174076090446016478413839141103554896238541841759820948125638539810854105390005604840477109411224067704997858792005935387702317239113232243454965916453079530436188597274982207232249086051793580677499198519753552676223875766967516817936608481211870388920172476106514339139854774871473171973786202397294771414846878288068395067160834393863091705364767024376979549838350508135469852971353931469105309074383247529042053491376862780245377981588649881913554027741057974916690134696134224043153664496042555308891044341949349510487831158886610215413433843495568529343526198288069768315299942340762953342062250476272698297633277573884470447570191517003492158746094812048550368105267095142400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem product_eq : Nat.factorial 1062 = smallPrimeProduct := by decide +kernel

private def Certified (n : ℕ) : Prop :=
  if n ≤ 1062 then n.Prime else n ≤ 1127000 ∧ Nat.gcd n smallPrimeProduct = 1

private instance (n : ℕ) : Decidable (Certified n) := by
  unfold Certified
  infer_instance

private theorem primeOfCertified {n : ℕ} (h : Certified n) : n.Prime := by
  by_cases low : n ≤ 1062
  · simpa only [Certified, if_pos low] using h
  · obtain ⟨bound, coprime⟩ : n ≤ 1127000 ∧ Nat.gcd n smallPrimeProduct = 1 := by
      simpa only [Certified, if_neg low] using h
    by_contra composite
    have fac := Nat.minFac_prime (show n ≠ 1 by omega)
    have square := Nat.minFac_sq_le_self (show 0 < n by omega) composite
    have small : n.minFac ≤ 1062 := by
      by_contra! large
      have lower := Nat.pow_le_pow_left (show 1063 ≤ n.minFac by omega) 2
      omega
    have divides : n.minFac ∣ Nat.gcd n smallPrimeProduct :=
      Nat.dvd_gcd (Nat.minFac_dvd n) (product_eq ▸ Nat.dvd_factorial fac.pos small)
    rw [coprime] at divides
    exact fac.ne_one (Nat.dvd_one.mp divides)

private def Valid (i : ℕ) (j : Fin 25) : Prop :=
  let p := witness i j
  let n := 25 * i + j.val + 4
  n ≤ 754 → Certified p ∧ p < n ∧ Certified (3 * p - 4) ∧
    Certified (n ^ 2 + (n - p) ^ 2)

private instance (i : ℕ) (j : Fin 25) : Decidable (Valid i j) := by
  unfold Valid
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked0 : ∀ j : Fin 25, Valid 0 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked1 : ∀ j : Fin 25, Valid 1 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked2 : ∀ j : Fin 25, Valid 2 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked3 : ∀ j : Fin 25, Valid 3 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked4 : ∀ j : Fin 25, Valid 4 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked5 : ∀ j : Fin 25, Valid 5 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked6 : ∀ j : Fin 25, Valid 6 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked7 : ∀ j : Fin 25, Valid 7 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked8 : ∀ j : Fin 25, Valid 8 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked9 : ∀ j : Fin 25, Valid 9 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked10 : ∀ j : Fin 25, Valid 10 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked11 : ∀ j : Fin 25, Valid 11 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked12 : ∀ j : Fin 25, Valid 12 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked13 : ∀ j : Fin 25, Valid 13 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked14 : ∀ j : Fin 25, Valid 14 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked15 : ∀ j : Fin 25, Valid 15 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked16 : ∀ j : Fin 25, Valid 16 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked17 : ∀ j : Fin 25, Valid 17 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked18 : ∀ j : Fin 25, Valid 18 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked19 : ∀ j : Fin 25, Valid 19 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked20 : ∀ j : Fin 25, Valid 20 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked21 : ∀ j : Fin 25, Valid 21 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked22 : ∀ j : Fin 25, Valid 22 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked23 : ∀ j : Fin 25, Valid 23 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked24 : ∀ j : Fin 25, Valid 24 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked25 : ∀ j : Fin 25, Valid 25 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked26 : ∀ j : Fin 25, Valid 26 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked27 : ∀ j : Fin 25, Valid 27 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked28 : ∀ j : Fin 25, Valid 28 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked29 : ∀ j : Fin 25, Valid 29 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked30 : ∀ j : Fin 25, Valid 30 j := by decide +kernel

private theorem checked (i : ℕ) (hi : i < 31) (j : Fin 25) : Valid i j := by
  interval_cases i
  · exact checked0 j
  · exact checked1 j
  · exact checked2 j
  · exact checked3 j
  · exact checked4 j
  · exact checked5 j
  · exact checked6 j
  · exact checked7 j
  · exact checked8 j
  · exact checked9 j
  · exact checked10 j
  · exact checked11 j
  · exact checked12 j
  · exact checked13 j
  · exact checked14 j
  · exact checked15 j
  · exact checked16 j
  · exact checked17 j
  · exact checked18 j
  · exact checked19 j
  · exact checked20 j
  · exact checked21 j
  · exact checked22 j
  · exact checked23 j
  · exact checked24 j
  · exact checked25 j
  · exact checked26 j
  · exact checked27 j
  · exact checked28 j
  · exact checked29 j
  · exact checked30 j

theorem result : OMA.R_oeis_a227899_R1.H1 := by
  intro n hlo hhi
  let i := (n - 4) / 25
  let j : Fin 25 := ⟨(n - 4) % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 31 := by dsimp [i]; omega
  have hn : 25 * i + j.val + 4 = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn] at h
  obtain ⟨hp, hpn, hlinear, hsquare⟩ := h hhi
  exact ⟨witness i j, primeOfCertified hp, hpn, primeOfCertified hlinear,
    primeOfCertified hsquare⟩

end PrimeSumOfSquares

theorem OMA.solution : OMA.R_oeis_a227899_R1.H1 :=
  PrimeSumOfSquares.result