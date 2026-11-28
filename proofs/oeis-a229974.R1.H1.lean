import OMAReductions.R_oeis_a229974_R1

import Mathlib

namespace TriplePrimeProducts

private def witnesses : ℕ → List (ℕ × ℕ)
  | 0 => [(2, 1), (3, 1), (2, 1), (3, 1), (6, 1), (3, 1), (2, 3), (2, 3), (3, 3), (3, 5), (2, 3), (6, 5), (3, 1), (3, 3), (2, 1), (6, 9), (2, 3), (2, 1), (3, 1), (3, 10), (2, 3), (2, 3), (2, 18), (2, 15), (2, 15)]
  | 1 => [(3, 1), (2, 1), (2, 3), (3, 23), (2, 27), (2, 3), (3, 3), (2, 18), (3, 1), (6, 5), (2, 15), (2, 3), (2, 3), (3, 1), (3, 5), (2, 15), (3, 17), (2, 18), (6, 16), (2, 1), (2, 18), (2, 27), (2, 1), (3, 3), (2, 27)]
  | 2 => [(3, 17), (2, 3), (2, 15), (3, 33), (6, 15), (3, 12), (2, 1), (2, 48), (3, 1), (2, 1), (2, 18), (3, 3), (3, 12), (2, 15), (3, 10), (2, 15), (3, 3), (2, 18), (2, 15), (2, 15), (2, 3), (2, 27), (2, 15), (3, 3), (6, 5)]
  | 3 => [(3, 5), (2, 57), (2, 1), (2, 45), (3, 30), (2, 15), (2, 60), (2, 78), (3, 18), (2, 15), (2, 18), (2, 1), (2, 3), (6, 1), (3, 5), (3, 7), (2, 27), (2, 3), (2, 15), (3, 10), (2, 27), (3, 40), (2, 3), (2, 15), (6, 1)]
  | 4 => [(2, 78), (2, 15), (3, 12), (3, 1), (2, 1), (2, 15), (2, 87), (2, 1), (2, 45), (2, 60), (2, 57), (2, 3), (2, 108), (3, 3), (2, 87), (2, 18), (3, 5), (2, 105), (2, 15), (2, 15), (2, 3), (2, 18), (2, 3), (3, 110), (2, 15)]
  | 5 => [(2, 3), (2, 15), (3, 77), (2, 105), (2, 15), (3, 40), (3, 77), (3, 3), (3, 70), (6, 15), (2, 3), (2, 3), (3, 1), (3, 1), (2, 15), (2, 3), (2, 18), (3, 12), (3, 1), (2, 60), (3, 5), (2, 45), (2, 18), (2, 60), (2, 1)]
  | 6 => [(2, 3), (2, 18), (3, 7), (2, 150), (2, 27), (2, 18), (2, 57), (2, 3), (3, 138), (3, 5), (2, 15), (3, 23), (2, 3), (2, 15), (2, 1), (2, 165), (2, 48), (2, 15), (2, 165), (3, 45), (2, 3), (2, 18), (3, 1), (2, 105), (3, 5)]
  | 7 => [(2, 3), (3, 58), (2, 3), (3, 3), (2, 27), (3, 5), (3, 7), (2, 15), (2, 105), (2, 150), (2, 108), (2, 18), (2, 105), (2, 15), (6, 16), (2, 3), (2, 150), (2, 165), (3, 103), (2, 15), (2, 108), (2, 3), (2, 150), (2, 60), (2, 15)]
  | 8 => [(2, 48), (2, 48), (2, 45), (3, 23), (2, 87), (2, 60), (2, 1), (3, 5), (2, 15), (2, 45), (2, 150), (2, 207), (2, 15), (2, 60), (3, 5), (3, 1), (2, 87), (2, 3), (3, 10), (3, 5), (2, 27), (2, 48), (2, 15), (3, 5), (2, 27)]
  | 9 => [(2, 3), (2, 45), (2, 3), (2, 165), (6, 1), (2, 87), (2, 57), (2, 60), (3, 3), (2, 27), (2, 105), (2, 78), (3, 3), (3, 1), (2, 45), (2, 57), (2, 15), (3, 1), (3, 3), (2, 87), (2, 57), (2, 60), (2, 18), (2, 45), (3, 5)]
  | 10 => [(3, 12), (2, 3), (3, 7), (3, 3), (2, 1), (2, 18), (2, 165), (2, 1), (2, 105), (2, 105), (2, 60), (2, 3), (3, 58), (2, 60), (3, 70), (2, 3), (2, 60), (2, 105), (3, 1), (2, 15), (2, 18), (3, 5), (2, 1), (3, 58), (2, 27)]
  | 11 => [(2, 45), (2, 3), (2, 273), (3, 1), (6, 55), (2, 27), (2, 3), (2, 3), (3, 1), (6, 1), (2, 273), (2, 78), (2, 1), (3, 175), (2, 45), (2, 3), (2, 273), (3, 10), (3, 38), (2, 45), (2, 3), (2, 3), (2, 18), (2, 105), (2, 57)]
  | 12 => [(3, 12), (2, 45), (2, 150), (2, 165), (2, 207), (2, 18), (2, 15), (2, 3), (2, 45), (2, 207), (3, 10), (2, 57), (2, 258), (3, 1), (2, 15), (2, 3), (2, 18), (2, 108), (2, 150), (6, 16), (2, 105), (2, 57), (2, 3), (2, 60), (2, 57)]
  | 13 => [(2, 57), (3, 40), (2, 273), (3, 3), (2, 1), (2, 27), (2, 15), (2, 15), (3, 1), (6, 85), (2, 57), (2, 3), (3, 7), (3, 1), (2, 45), (2, 207), (2, 27), (2, 3), (2, 105), (3, 135), (2, 3), (2, 45), (2, 18), (3, 1), (3, 45)]
  | 14 => [(2, 48), (2, 45), (2, 45), (2, 255), (2, 27), (3, 1), (2, 1), (2, 3), (2, 105), (3, 95), (2, 78), (3, 5), (2, 1), (2, 105), (2, 15), (2, 60), (2, 87), (2, 60), (3, 238), (2, 357), (2, 273), (2, 1), (2, 45), (2, 15), (2, 27)]
  | 15 => [(2, 18), (2, 105), (2, 15), (3, 1), (2, 207), (2, 3), (2, 27), (2, 165), (3, 33), (2, 45), (2, 45), (2, 357), (2, 18), (2, 105), (2, 165), (2, 15), (2, 255), (2, 15), (3, 10), (2, 15), (2, 78), (2, 258), (2, 15), (2, 330), (3, 100)]
  | 16 => [(2, 3), (2, 1), (2, 18), (3, 5), (2, 1), (2, 288), (2, 255), (2, 45), (2, 45), (2, 105), (2, 105), (3, 47), (2, 3), (2, 60), (2, 105), (2, 3), (2, 1), (3, 138), (2, 330), (2, 255), (2, 15), (2, 60), (2, 105), (2, 105), (3, 40)]
  | 17 => [(3, 1), (2, 3), (2, 273), (2, 60), (2, 150), (2, 105), (2, 18), (2, 105), (2, 45), (2, 45), (2, 27), (2, 87), (2, 3), (2, 165), (2, 330), (3, 52), (2, 3), (3, 7), (2, 15), (2, 60), (2, 258), (2, 1), (2, 105), (2, 150), (2, 417)]
  | 18 => [(2, 18), (2, 18), (2, 18), (2, 330), (2, 87), (2, 27), (2, 165), (2, 288), (2, 15), (2, 105), (3, 5), (2, 3), (2, 165), (3, 10), (2, 15), (2, 48), (2, 105), (2, 1), (3, 3), (2, 60), (2, 87), (2, 3), (2, 3), (2, 165), (2, 405)]
  | 19 => [(2, 87), (2, 48), (2, 165), (2, 60), (2, 27), (2, 60), (2, 105), (2, 1), (2, 60), (3, 30), (2, 18), (2, 27), (3, 312), (3, 238), (2, 150), (2, 3), (2, 3), (3, 3), (3, 3), (2, 165), (3, 1), (2, 57), (2, 60), (2, 45), (2, 87)]
  | 20 => [(2, 18), (2, 60), (3, 3), (2, 15), (2, 255), (3, 10), (2, 1), (2, 273), (2, 105), (2, 15), (2, 45), (2, 15), (2, 3), (2, 60), (2, 330), (2, 273), (2, 288), (2, 150), (2, 405), (2, 165), (2, 60), (2, 1), (3, 12), (2, 330), (3, 110)]
  | 21 => [(2, 48), (2, 3), (2, 1), (3, 1), (2, 60), (2, 27), (2, 3), (2, 60), (2, 150), (2, 165), (2, 15), (2, 405), (2, 78), (3, 18), (3, 455), (2, 27), (2, 207), (2, 45), (3, 1), (2, 57), (2, 87), (2, 27), (2, 3), (3, 18), (2, 45)]
  | 22 => [(2, 18), (2, 27), (2, 255), (2, 60), (3, 100), (2, 273), (2, 3), (2, 273), (3, 3), (3, 5), (2, 78), (2, 18), (2, 15), (3, 58), (2, 60), (2, 330), (2, 1), (2, 3), (2, 60), (2, 57), (2, 3), (2, 48), (2, 288), (2, 15), (2, 255)]
  | 23 => [(2, 258), (2, 150), (2, 150), (2, 105), (2, 405), (2, 3), (2, 3), (2, 48), (3, 3), (2, 1), (2, 483), (2, 288), (2, 150), (2, 15), (2, 87), (2, 60), (2, 45), (2, 585), (3, 1), (3, 270), (2, 3), (2, 18), (2, 45), (3, 33), (2, 357)]
  | 24 => [(2, 258), (2, 15), (2, 3), (2, 45), (2, 357), (2, 18), (2, 357), (2, 288), (3, 5), (2, 207), (2, 3), (2, 18), (2, 3), (2, 585), (2, 447), (2, 57), (2, 105), (2, 528), (2, 60), (2, 27), (3, 390), (2, 105), (2, 78), (2, 60), (2, 567)]
  | 25 => [(2, 3), (2, 15), (2, 258), (2, 15), (2, 255), (2, 3), (2, 3), (2, 108), (2, 15), (2, 60), (2, 105), (2, 87), (2, 165), (2, 45), (2, 165), (2, 150), (2, 363), (2, 105), (2, 330), (2, 27), (3, 30), (2, 78), (2, 1), (3, 425), (2, 57)]
  | 26 => [(2, 108), (2, 108), (2, 45), (2, 105), (2, 15), (2, 48), (2, 273), (2, 528), (3, 170), (2, 45), (2, 60), (2, 18), (2, 273), (3, 10), (2, 45), (2, 60), (2, 108), (2, 15), (2, 585), (3, 385), (2, 258), (2, 1), (2, 150), (2, 585), (3, 25)]
  | 27 => [(2, 3), (2, 165), (2, 1), (3, 18), (2, 105), (2, 18), (2, 60), (2, 45), (2, 405), (3, 110), (2, 288), (2, 3), (2, 3), (2, 45), (2, 27), (2, 405), (2, 57), (2, 3), (2, 150), (2, 27), (2, 105), (2, 27), (2, 18), (2, 330), (2, 255)]
  | 28 => [(2, 3), (3, 10), (2, 18), (2, 45), (3, 25), (2, 15), (3, 5), (2, 78), (2, 45), (2, 15), (2, 417), (2, 48), (3, 1), (3, 18), (2, 27), (2, 357), (2, 15), (2, 48), (3, 18), (2, 447), (2, 3), (2, 27), (2, 648), (2, 45), (2, 57)]
  | 29 => [(2, 48), (2, 27), (2, 15), (2, 15), (3, 170), (3, 12), (2, 18), (2, 48), (2, 105), (3, 45), (2, 15), (2, 3), (2, 288), (2, 165), (2, 567), (2, 468), (2, 45), (2, 48), (3, 3), (2, 105), (2, 108), (2, 48), (2, 48), (3, 33), (2, 1)]
  | 30 => [(2, 108), (2, 3), (2, 3), (2, 105), (2, 357), (2, 87), (2, 18), (2, 45), (2, 15), (2, 672), (2, 48), (2, 57), (2, 78), (3, 268), (2, 27), (2, 15), (2, 15), (2, 105), (3, 38), (3, 70), (2, 57), (2, 3), (2, 528), (3, 1), (2, 672)]
  | 31 => [(2, 48), (2, 45), (2, 165), (3, 385), (2, 1), (2, 78), (2, 27), (2, 750), (3, 5), (2, 27), (2, 648), (2, 3), (2, 3), (3, 18), (2, 330), (2, 507), (2, 1), (2, 60), (2, 165), (2, 567), (2, 363), (2, 27), (2, 45), (2, 105), (2, 60)]
  | 32 => [(2, 165), (2, 78), (2, 60), (2, 105), (2, 255), (2, 18), (2, 27)]
  | _ => []

private def witness (i : ℕ) (j : Fin 25) : ℕ × ℕ := (witnesses i).getD j.val (0, 0)

private def smallPrimeProduct : ℕ := 887042321237294133496210857894949637685773736164401836059809823005207935956503710937431484137814427102797030738518423759191946817864043761512529363361598285579783571151229768907517784588149206076077091001290672249506580697693307061199178689901651462723298763270043744909610632410681224684457578291792910444749093545778861951309597785609796749568466979726119844240445661492350724313745574213980645541040006087973008357593314999266578972948301857782606316720019275473440458100293070933337747401831803803276674025186254541159934727693312914431737675962131463306855018302939068373375814671138787859449717749305277850085736091761564645186335523131967881485526046781884929774902115046257490184233066444831767054300306122436366103318426584983056960585403843437013543654808573620162525368484432965906617420881660427601070716101108569930402168535053719232428822541270758290613661794511430478362290489466036484636997124427788207753288461706070696176195512068430604491221303019965584577181467759209032242987795289062031090942497423513874335185489971752462854861014834417539902247844731429547429522047185158396735586267913004486399198129014361414607811965577410242415326723575759433839550986368184659421613353068493075770657579876051961701960355876492251769251612587192015847749461282979241651616424198307336886905537563753314977750832899762427399694370812129005534773261720615355294728403661620988119356293069973860590737523537458757146891539439068271565914184499393846949783817827622583797133720022925716628570132550603885495651988800090733255867417477163215801312029436545591870734588932313976435289451518782267303181123997648177075253575992905327770116378988583783116641038239261744035769604046151055362485544370473044263092915938837778105271472312892984693846095016038767307590189237733814369464462987801926618497517880329334892606231354540615797101544249398094813475826515105448167775784633630860378719923521911697022402250800565543475468153055064245812771768964446642320905016723700345392047840255928799877805932148510718386893478011202928702978158616657000941605993025444761638730939900468536701681421135384044289023967065105270454516216768647315372732175614845129002875463846932254056661600551407497521178985103360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem product_eq : Nat.factorial 960 = smallPrimeProduct := by decide +kernel

private def Certified (n : ℕ) : Prop :=
  if n ≤ 960 then n.Prime else n ≤ 915000 ∧ Nat.gcd n smallPrimeProduct = 1

private instance (n : ℕ) : Decidable (Certified n) := by
  unfold Certified
  infer_instance

private theorem primeOfCertified {n : ℕ} (h : Certified n) : n.Prime := by
  by_cases low : n ≤ 960
  · simpa only [Certified, if_pos low] using h
  · obtain ⟨bound, coprime⟩ : n ≤ 915000 ∧ Nat.gcd n smallPrimeProduct = 1 := by
      simpa only [Certified, if_neg low] using h
    by_contra composite
    have fac := Nat.minFac_prime (show n ≠ 1 by omega)
    have square := Nat.minFac_sq_le_self (show 0 < n by omega) composite
    have small : n.minFac ≤ 960 := by
      by_contra! large
      have lower := Nat.pow_le_pow_left (show 961 ≤ n.minFac by omega) 2
      omega
    have divides : n.minFac ∣ Nat.gcd n smallPrimeProduct :=
      Nat.dvd_gcd (Nat.minFac_dvd n) (product_eq ▸ Nat.dvd_factorial fac.pos small)
    rw [coprime] at divides
    exact fac.ne_one (Nat.dvd_one.mp divides)

private def Valid (i : ℕ) (j : Fin 25) : Prop :=
  let x := (witness i j).1
  let y := (witness i j).2
  let n := 25 * i + j.val + 4
  let z := n - x - y
  n ≤ 810 → 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
    Certified (2 * x - 1) ∧ Certified (2 * x + 1) ∧
    Certified (2 * x * y - 1) ∧ Certified (2 * x * y + 1) ∧
    Certified (2 * x * y * z - 1) ∧ Certified (2 * x * y * z + 1)

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

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked31 : ∀ j : Fin 25, Valid 31 j := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked32 : ∀ j : Fin 25, Valid 32 j := by decide +kernel

private theorem checked (i : ℕ) (hi : i < 33) (j : Fin 25) : Valid i j := by
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
  · exact checked31 j
  · exact checked32 j

theorem result : OMA.R_oeis_a229974_R1.H1 := by
  intro n hlo hhi
  let i := (n - 4) / 25
  let j : Fin 25 := ⟨(n - 4) % 25, Nat.mod_lt _ (by decide)⟩
  have hi : i < 33 := by dsimp [i]; omega
  have hn : 25 * i + j.val + 4 = n := by dsimp [i, j]; omega
  have h := checked i hi j
  unfold Valid at h
  rw [hn] at h
  obtain ⟨hx, hy, hz, hsum, ha, hb, hc, hd, he, hf⟩ := h hhi
  exact ⟨(witness i j).1, (witness i j).2, n - (witness i j).1 - (witness i j).2,
    hx, hy, hz, hsum, primeOfCertified ha, primeOfCertified hb, primeOfCertified hc,
    primeOfCertified hd, primeOfCertified he, primeOfCertified hf⟩

end TriplePrimeProducts

theorem OMA.solution : OMA.R_oeis_a229974_R1.H1 :=
  TriplePrimeProducts.result