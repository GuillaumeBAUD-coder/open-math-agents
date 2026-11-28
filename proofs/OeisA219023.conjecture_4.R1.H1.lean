import OMAReductions.R_OeisA219023_conjecture_4_R1

/-! Coprimality certificates for the quadratic prime pairs in the finite range. -/

namespace OMA.QuadraticPrimePairs

private def coversHeads (P : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | a, width+1 => decide (a.gcd P ≠ 1) && coversHeads P (a+1) width

private theorem coversHeads_sound (P a width : ℕ) (h : coversHeads P a width = true) :
    ∀ d, a ≤ d → d < a+width → d.gcd P ≠ 1 := by
  induction width generalizing a with
  | zero => omega
  | succ width ih =>
    change (decide (a.gcd P ≠ 1) && coversHeads P (a+1) width) = true at h
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at h
    intro d lo hi
    by_cases heq : d = a
    · exact heq ▸ h.1
    · exact ih (a+1) h.2 d (by omega) (by omega)

private theorem coversJoin {P a b c : ℕ}
    (left : ∀ d, a ≤ d → d < b → d.gcd P ≠ 1)
    (right : ∀ d, b ≤ d → d < c → d.gcd P ≠ 1) :
    ∀ d, a ≤ d → d < c → d.gcd P ≠ 1 := by
  intro d lo hi
  by_cases hm : d < b
  · exact left d lo hm
  · exact right d (by omega) hi

private theorem prime_of_covers {P b n : ℕ}
    (hcover : ∀ d, 2 ≤ d → d < b+1 → d.gcd P ≠ 1)
    (hn : 2 ≤ n) (hb : n < (b+1)^2) (hcop : n.gcd P = 1) : n.Prime := by
  by_contra h
  let d := n.minFac
  have hd : d.Prime := Nat.minFac_prime (by omega)
  have hsq : d^2 ≤ n := Nat.minFac_sq_le_self (by omega) h
  have hbound : d < b+1 := by
    by_contra! hbad
    have hh : (b+1)^2 ≤ d^2 := Nat.pow_le_pow_left hbad 2
    omega
  have hdiv : d ∣ P := by
    by_contra hnd
    exact hcover d hd.two_le hbound (hd.coprime_iff_not_dvd.mpr hnd)
  have hdg := Nat.dvd_gcd (Nat.minFac_dvd n) hdiv
  rw [hcop] at hdg
  exact hd.ne_one (Nat.dvd_one.mp hdg)

private def gcdWitness (small large n delta : ℕ) : Bool :=
  let p := n+delta
  let x := n^2-n-p
  let y := n^2+n+p
  decide (n<p ∧ p<2*n ∧ 2≤p ∧ p<201^2 ∧ p.gcd small=1 ∧
    2≤x ∧ x<20002^2 ∧ 2≤y ∧ y<20002^2 ∧ (x*y).gcd large=1)

private theorem gcdWitness_sound {small large n delta : ℕ}
    (hsmall : ∀ d, 2 ≤ d → d < 201 → d.gcd small ≠ 1)
    (hlarge : ∀ d, 2 ≤ d → d < 20002 → d.gcd large ≠ 1)
    (checked : gcdWitness small large n delta = true) :
    ∃ p : ℕ, p.Prime ∧ n<p ∧ p<2*n ∧ (n^2-n-p).Prime ∧ (n^2+n+p).Prime := by
  let p := n+delta
  let x := n^2-n-p
  let y := n^2+n+p
  have hg : n<p ∧ p<2*n ∧ 2≤p ∧ p<201^2 ∧ p.gcd small=1 ∧
      2≤x ∧ x<20002^2 ∧ 2≤y ∧ y<20002^2 ∧ (x*y).Coprime large :=
    of_decide_eq_true checked
  obtain ⟨hnp,hpn,hp,hpb,hpc,hx,hxb,hy,hyb,hxy⟩ := hg
  have hxc : x.Coprime large := hxy.of_dvd_left ⟨y,rfl⟩
  have hyc : y.Coprime large := hxy.of_dvd_left ⟨x,Nat.mul_comm _ _⟩
  exact ⟨p,prime_of_covers hsmall hp hpb hpc,hnp,hpn,
    prime_of_covers hlarge hx hxb hxc,prime_of_covers hlarge hy hyb hyc⟩

private def checkedRows (check : ℕ → ℕ → Bool) (first data : ℕ) : ℕ → Bool
  | 0 => true
  | width+1 => check first (data % 16384) && checkedRows check (first+1) (data / 16384) width

private theorem checkedRows_sound {check : ℕ → ℕ → Bool} {good : ℕ → Prop}
    (sound : ∀ n delta, check n delta = true → good n)
    {first data width : ℕ} (verified : checkedRows check first data width = true) :
    ∀ n, first ≤ n → n < first+width → good n := by
  induction width generalizing first data with
  | zero => omega
  | succ width ih =>
    rw [checkedRows, Bool.and_eq_true_iff] at verified
    intro n hleft hright
    by_cases eq : n=first
    · subst n
      exact sound _ _ verified.1
    · exact ih verified.2 n (by omega) (by omega)

private def small : ℕ := 0x10721710415a2da05cbc84fa1b70135b2178303a82df89fd9f39e0effcf072495028a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def smallRange2Checked : PLift (coversHeads small 2 199 = true) :=
  ⟨by decide +kernel⟩

private theorem smallRange2 : ∀ d, 2 ≤ d → d < 201 → d.gcd small ≠ 1 :=
  coversHeads_sound small 2 199 smallRange2Checked.down

private theorem smallCovers : ∀ d, 2 ≤ d → d < 201 → d.gcd small ≠ 1 :=
  smallRange2

private def large : ℕ := 0x207dc0f5ff86fd1be4eab851b9a588e0aad9c7b10b490a4b875a347241366dd05e3b7d719472ad173acdf01346915023a83f5da517634366f698fc302722db142fd7219e4dfd93d0e57cdd31414baf080f440da983fa56b87b72747d565eff54eff89905340d3d23591c5542dd467f5adf863e36ef77f8c40801fc6151bb19176ff69c523dff909df50e55d88767d290255d798b656068589f303b7c5cc39b40baeb2d1f2d208740ea9211d2d19e293abda344a24a146fdadba62f998ae678b9c1839a3402991faa27565521dddf7e6fc2a683933d41e2bb12d18902d3b62215f1fadc1f02f9e3a82ddebd15a0a0987330633a9839f8e05d99c36e08e0034e0af4ea484b961ac1f5379867d24ad7f596ab4cdb5f5a717814cf365db32072c5e99f70741fe42331b03b9869dc9ea6d5d0bec3ed1512bbde6317df6ba8e1f74f36311987bf1ba65d2bdf60679840dded7f1ad403149df616c79faed9f66974568c00884e4a9cf122b648627bfc3a93f6ee09fa356efe3a52dcb802738fe641c3b48698719f6182d091a2d840a0572d8c2b33ecb7d1a0c24ec90127cc38627f50d971375b374bcbfaf411fe988ec78cef5c7ffd398cfd6dc505af43b6507057bcdd39af00768d46f4dfa702899773ecfc819dbac3725f829be4cf09435c2a19bd04f9f4bad2803e7a3886ad9b78ebf8002a666f7588ce366aaea3863b3347548f440435e0173f61396e0aaf14fc895d5e1298df8c5588f6dcd9fbd0e6aa641de4058c2e8f5c10361ff7e2523b5b109cd8500d2657c9de230f013b6ffdf54a8112d0913f2996d13690375a94e8c52fec3b8ad6813aa6e5ca2ac42f69aa602f79fd4fba60e0e4258ca7bf8fedeb244f95c309f20c37b3d58d1850e38e32222c2995a6b42437206eeed9b495acec4e60554f7f3aa9d2a5d9c1dcb510bd5e3ffc098cd741d23115c4aacef20896b34b026133d4102fea14295bc4467c10a63688a29fe3dc8bb8c60ab09fecb0730ffdb5b0c379b34518b7b2fd2d5553ebaab2abeb9e68cdc3280cc41f4b344fe7204cdc8c5787f9ee2d521589673c5cbbcf2d9292f7925069556a54618a11971b8db55aad01d6791e6ba6bef20cb5d7efc338b1d3f2ea2992db65fc84e79f5afe3af01684cc148c944ed5ec1ee57a61668f114260a3128a967ff0cc01613dd3cb654867c5697887cbed2859f3be68edc013c5537ff50a00619a6091a5548463f83413b65a0a09f0d98dfdfc735cecd2b51b6c774c778a0604c7cb59725517f543201055d7928b862f69c122e90ca2fd05b016977a951e26eadf8a681f161915620d779856ffc0d45fe0fdd3963cb4197e2e54307b66edd773f68d15687f3fc51f1f06a10c373b36fc6715429603ffca4efac4e4d05391c0f031df03a4caa4edf06a4c49630c4bcdba39c5ca19be448fbfb3629bcae7e91a162c8c13fb4174613b421914e323e74952060367691acbf4a0c36eb47d8b5ea7b70654d38414a3c11f8705a8b11140875e17da1cb27bff3238de2e31740e8152c32ba7775475793db3ebd2d8799006351f69cb256f92bfaa31a296acbefbc0c98cad109d89ef35d79ed0fad381669fa74cff480d4f953cfc1816fab0746ae91dfc592683ba9bd2a30ca3120892ac0278e2855392fb0575dce3dad3badc1edf2e962c299ea5b8bebebc1b2ac8ec65d25f44f2250b51bc1706e35428fed5e7646cddd7887d3254f311decbb2737cfbbface64fcd8edc161b4071686c954d923c80dd8fae123deae9840074aec9e6dde3e69737eee5eb77ceab237672efb0d79d2b7efbecde40b110c8c67db273f40c8883fe778506c209117c0154f019fea9d73ac46a01f72908b2b72fe0cf7500b66189ed277cd5051f39844760d404b8d574d427540ffb6ec16582a9752587033e2605b5ae4a23d402758c65b6a6912ce85c4f6730023163f9586956f27e77ba86331640d08064e4d3d04b2c158eea7dea032b8bec39644f9a65e707b7a5feafbce756857d19ea19a8b8da68945ca504acaa9d2e8750b255128d92dcf17f75bd6e25fff979ea002a0a5f35f1c5f084af73093f1b841b448c60b308056b175d846c5e1dc5ed4980a571073f12835a426f74ec60480d3b46d7b292867e2196ce0037670070722b276d247873dac6e64c3e3234b3544815228b9bf8a550b8c3a281bd5e23d2995f3115292fe53586e5ed4a227f26011aefd5bb780e2544de2b0e97fa2314324f81e508adfbdf76c897e1b11b40ff362fdb2e90ed1e087f83f5d9019ce5d8e1d1a7c8704f7ead1eb12e3b94321826c41ff066e2eb2e4ecc76c6fce2cdf7f92d134412947fc183364aaafa12a034017dadb5fcf738f5786f4a71e71d20aea17926e7dfbfd450d0ce3c40762e1b4cc082874d6bfa91bbe065e6e4840a63bc0939a6f2900c2d34cd68973c972349579f0de44af35a4e4524d16df6806b79b5132c467a4ed8e1578b1f7eef3894a78b3ceef575701b3099390aa38db8ec369ba98943c3652766fc56186eb0a8faff5125f129cdd4e0055342f7f46113f63373d9c79b671a2528ff69e3e65d2d3998c6bff33905826a7f52a850ebdaddc7935b7d3502a84ad044bdc238c3b5c1541ca3c535957d0e5f7a9902b64845dcdd5e5d03f150b1118b151ecea753a77ea477192cf40d4dc13e91b2c311261c61bb8ef327bdf017ae5bc18e417d0cc4dff58fd76786efab5083946e15671194eea5de395e697b79ff6d871d387db0f1e7b239078480714adf28ecfdd03492a36bdd912a2123a0d6529c5e9905a03ee3392de008e676d0a560dbcad873fa2eca690522d03aeb7f0bc2a310ed9e4157bac7b1faf20eb4a76ab9c386ed4c7bc29f901c4cca3b1ced047581ff8e5ad7c14ba399f5895e75fd82606b8284bd32c2d67d5bd048f70c91b4567b5ce48b0a369e552ee9ee9eca654e7bd8cc7b9ce14f30e3cd2703a2b48a0210e313c7b836d008fdf4d1932313368db895bcc4f5ac57376701c603fb0c2f891f0e6dd17a9ca24fd9d603816a845cf48691ed6a3774f2af0d73c1d89c3565716798fe3e92cf48c3be31038c750b843fb10737b38a96cc935c9f68ba7f8e8a7aa8d20083f6f6e04e37f6354c9b17aeba085ad314018f0fa908020cf3ffe7e4345d4b0cb326fdbe827be02b6ba15d1baac35f8a537814454cd02568c9c0667bd52b889e961e8fb3245c69a0213b975e700c91d335494baf6900f09fb6af650a277ab371aba423cea2a14537368a8c04319ba28df082ae5e8d0a9d4b6f930f42379a4a239ff3c69a2422ff403bcb240766ed1a9d007b58a377cb9d103d17119a03e49d9fcf2febc29bb3149401f478282a57aa0ec94b114d4894c5ddc42d45a9b13602665326ad1e0e4dd29f432b3a76546348b5b6862caaa2fd4b90e68d7cf58d419f9f1e5662673c02ed8e57c01516cf5ac0114c4e488803170e89136c5cd6e4908a680e18858494fc5b438bc93f876bdaaf20e21b8f4d3d83de83ec1579edcf6d8709b160e6655f5a9930cf345f673abe6b09c4acb49e91f889104331b537a6bdf8acf8ab66794bd11bf0de1c5c129dd367ea3b45c812457fcc7ed407011ea6b89eef5117ca212c7fcc2f595515de577db08ae5d6189031c3fe5a6876a49677d7a93e408110fd5c607ef0deb24948211e6b0808c14ce18a75797f28de317a70797f19f47aca8912fca56fa2e84dcb4ef87a61c75f7820531611177654bde0533b86caf007891be3b415073e106f0be55ff69866e787996584717cb57c282a4d3f1fc352821eeebedec70392e7e034d583def8f4b1ddbd56d7de78908be36e77ff23faccc4971cb982746b6aaefbd7988de1fbc1d1fd1800bc37c30b95a64d5953daf8dd21f2b01379aa016c095e752a9c6856c75b6e0f4513ce0e62fccbd61362548bb336108271f33a443bb4877e184e4881010ab5bf2ca936705903e961d79403cea4b685401fb6cfa7a55cb56472478f400d59c53794fd59a87df5e90adf9915a57c14dd209170abf27276deb8d3a4b5deddc1f95f79bfcac9e8a5fc4826a757c5fb3b173baaf7fda40fae344540dfd137a32f24a22e9d93e9478f145f0bde0c90acc962fb1d2a3eee71daa05b546e2e4c7d5bb07d0db48e6cb52faa4836a73a62f74a50e4473e9d684ba83e32ce2fc66cc778579a775999dab76a00bb3d96c9360f67138653bde134e3df4abaf613678afb95da20837030a626f3ad4267ee55fadafd1e04bf4e3ae2183be5583d65697d52d2a066e01f92bd39d68ff50bb72a45e22258fe20de77b979cc060c4d321dcfcb6fe12d590750b4eb0ceb3214fe702be56c2c4d336c25658d845816d3522292526c44ffdd04abd05b773ff707fa69d94f29a2a5525eff1c6865e404db483fad160f8e15b0af7130040df19e93e6fbf06bfb6063d87d469ae732deeba24e1040a7841e5b10405d680e3a52d958c9043d44ad187dc5704ce5f396fef9c0eaaf893a24d71ff8b38693ce62f4386fde6e99cb550ee2b0e25368f0764397a50f35ae37cb73f7d65d2c75c55e62468fe022047e10b1b39dce9283fe4b08199da3880e23fd7dd8fa60ea535b832340e5173b711b22d4ed66b810a9bc877c4cb353622a544e806a42d3b30cefbe9c28cb9d027cd6636273f3a7d16b2746ab6bdac6420b65b53a5b6b6bbb4faf3e33dcc571c528f5cfa96ad3c25ab255fce10f524ea00e74510f77c73f9419c3e37368a823faaffdaa0432cd6a69b0d44b51543a14cd0ac88d443894dc4ddaebb607ade54a312aa24dd9344e1010eec9b858f11322b1eeb75338879453ddd2ed38e6008c3478c8c47ab71421c3152448301d375bcacd4364241cca6450166b2b53abab0fdf87acfbd430e3e0c94e456a4a84241ef01ed2d1f217153c05a1359a4b3c76383edac29a0d52a00010d9cf99b5233bde385aae76d60d384594b8300fecdb8537c202b28bef0049f980811ba8d02a5d1332e28c684675aeeaa805c836d5174eac1993ecc856bb7f63bfa3bb96af53f6f9f8daaea5f04f2e4e41216156f61f8ff2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange2Checked : PLift (coversHeads large 2 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange2 : ∀ d, 2 ≤ d → d < 402 → d.gcd large ≠ 1 :=
  coversHeads_sound large 2 400 largeRange2Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange402Checked : PLift (coversHeads large 402 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange402 : ∀ d, 402 ≤ d → d < 802 → d.gcd large ≠ 1 :=
  coversHeads_sound large 402 400 largeRange402Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange802Checked : PLift (coversHeads large 802 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange802 : ∀ d, 802 ≤ d → d < 1202 → d.gcd large ≠ 1 :=
  coversHeads_sound large 802 400 largeRange802Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange1202Checked : PLift (coversHeads large 1202 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange1202 : ∀ d, 1202 ≤ d → d < 1602 → d.gcd large ≠ 1 :=
  coversHeads_sound large 1202 400 largeRange1202Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange1602Checked : PLift (coversHeads large 1602 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange1602 : ∀ d, 1602 ≤ d → d < 2002 → d.gcd large ≠ 1 :=
  coversHeads_sound large 1602 400 largeRange1602Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange2002Checked : PLift (coversHeads large 2002 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange2002 : ∀ d, 2002 ≤ d → d < 2402 → d.gcd large ≠ 1 :=
  coversHeads_sound large 2002 400 largeRange2002Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange2402Checked : PLift (coversHeads large 2402 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange2402 : ∀ d, 2402 ≤ d → d < 2802 → d.gcd large ≠ 1 :=
  coversHeads_sound large 2402 400 largeRange2402Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange2802Checked : PLift (coversHeads large 2802 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange2802 : ∀ d, 2802 ≤ d → d < 3202 → d.gcd large ≠ 1 :=
  coversHeads_sound large 2802 400 largeRange2802Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange3202Checked : PLift (coversHeads large 3202 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange3202 : ∀ d, 3202 ≤ d → d < 3602 → d.gcd large ≠ 1 :=
  coversHeads_sound large 3202 400 largeRange3202Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange3602Checked : PLift (coversHeads large 3602 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange3602 : ∀ d, 3602 ≤ d → d < 4002 → d.gcd large ≠ 1 :=
  coversHeads_sound large 3602 400 largeRange3602Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange4002Checked : PLift (coversHeads large 4002 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange4002 : ∀ d, 4002 ≤ d → d < 4402 → d.gcd large ≠ 1 :=
  coversHeads_sound large 4002 400 largeRange4002Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange4402Checked : PLift (coversHeads large 4402 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange4402 : ∀ d, 4402 ≤ d → d < 4802 → d.gcd large ≠ 1 :=
  coversHeads_sound large 4402 400 largeRange4402Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange4802Checked : PLift (coversHeads large 4802 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange4802 : ∀ d, 4802 ≤ d → d < 5202 → d.gcd large ≠ 1 :=
  coversHeads_sound large 4802 400 largeRange4802Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange5202Checked : PLift (coversHeads large 5202 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange5202 : ∀ d, 5202 ≤ d → d < 5602 → d.gcd large ≠ 1 :=
  coversHeads_sound large 5202 400 largeRange5202Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange5602Checked : PLift (coversHeads large 5602 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange5602 : ∀ d, 5602 ≤ d → d < 6002 → d.gcd large ≠ 1 :=
  coversHeads_sound large 5602 400 largeRange5602Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange6002Checked : PLift (coversHeads large 6002 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange6002 : ∀ d, 6002 ≤ d → d < 6402 → d.gcd large ≠ 1 :=
  coversHeads_sound large 6002 400 largeRange6002Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange6402Checked : PLift (coversHeads large 6402 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange6402 : ∀ d, 6402 ≤ d → d < 6802 → d.gcd large ≠ 1 :=
  coversHeads_sound large 6402 400 largeRange6402Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange6802Checked : PLift (coversHeads large 6802 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange6802 : ∀ d, 6802 ≤ d → d < 7202 → d.gcd large ≠ 1 :=
  coversHeads_sound large 6802 400 largeRange6802Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange7202Checked : PLift (coversHeads large 7202 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange7202 : ∀ d, 7202 ≤ d → d < 7602 → d.gcd large ≠ 1 :=
  coversHeads_sound large 7202 400 largeRange7202Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange7602Checked : PLift (coversHeads large 7602 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange7602 : ∀ d, 7602 ≤ d → d < 8002 → d.gcd large ≠ 1 :=
  coversHeads_sound large 7602 400 largeRange7602Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange8002Checked : PLift (coversHeads large 8002 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange8002 : ∀ d, 8002 ≤ d → d < 8402 → d.gcd large ≠ 1 :=
  coversHeads_sound large 8002 400 largeRange8002Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange8402Checked : PLift (coversHeads large 8402 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange8402 : ∀ d, 8402 ≤ d → d < 8802 → d.gcd large ≠ 1 :=
  coversHeads_sound large 8402 400 largeRange8402Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange8802Checked : PLift (coversHeads large 8802 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange8802 : ∀ d, 8802 ≤ d → d < 9202 → d.gcd large ≠ 1 :=
  coversHeads_sound large 8802 400 largeRange8802Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange9202Checked : PLift (coversHeads large 9202 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange9202 : ∀ d, 9202 ≤ d → d < 9602 → d.gcd large ≠ 1 :=
  coversHeads_sound large 9202 400 largeRange9202Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange9602Checked : PLift (coversHeads large 9602 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange9602 : ∀ d, 9602 ≤ d → d < 10002 → d.gcd large ≠ 1 :=
  coversHeads_sound large 9602 400 largeRange9602Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange10002Checked : PLift (coversHeads large 10002 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange10002 : ∀ d, 10002 ≤ d → d < 10402 → d.gcd large ≠ 1 :=
  coversHeads_sound large 10002 400 largeRange10002Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange10402Checked : PLift (coversHeads large 10402 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange10402 : ∀ d, 10402 ≤ d → d < 10802 → d.gcd large ≠ 1 :=
  coversHeads_sound large 10402 400 largeRange10402Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange10802Checked : PLift (coversHeads large 10802 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange10802 : ∀ d, 10802 ≤ d → d < 11202 → d.gcd large ≠ 1 :=
  coversHeads_sound large 10802 400 largeRange10802Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange11202Checked : PLift (coversHeads large 11202 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange11202 : ∀ d, 11202 ≤ d → d < 11602 → d.gcd large ≠ 1 :=
  coversHeads_sound large 11202 400 largeRange11202Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange11602Checked : PLift (coversHeads large 11602 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange11602 : ∀ d, 11602 ≤ d → d < 12002 → d.gcd large ≠ 1 :=
  coversHeads_sound large 11602 400 largeRange11602Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange12002Checked : PLift (coversHeads large 12002 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange12002 : ∀ d, 12002 ≤ d → d < 12402 → d.gcd large ≠ 1 :=
  coversHeads_sound large 12002 400 largeRange12002Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange12402Checked : PLift (coversHeads large 12402 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange12402 : ∀ d, 12402 ≤ d → d < 12802 → d.gcd large ≠ 1 :=
  coversHeads_sound large 12402 400 largeRange12402Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange12802Checked : PLift (coversHeads large 12802 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange12802 : ∀ d, 12802 ≤ d → d < 13202 → d.gcd large ≠ 1 :=
  coversHeads_sound large 12802 400 largeRange12802Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange13202Checked : PLift (coversHeads large 13202 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange13202 : ∀ d, 13202 ≤ d → d < 13602 → d.gcd large ≠ 1 :=
  coversHeads_sound large 13202 400 largeRange13202Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange13602Checked : PLift (coversHeads large 13602 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange13602 : ∀ d, 13602 ≤ d → d < 14002 → d.gcd large ≠ 1 :=
  coversHeads_sound large 13602 400 largeRange13602Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange14002Checked : PLift (coversHeads large 14002 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange14002 : ∀ d, 14002 ≤ d → d < 14402 → d.gcd large ≠ 1 :=
  coversHeads_sound large 14002 400 largeRange14002Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange14402Checked : PLift (coversHeads large 14402 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange14402 : ∀ d, 14402 ≤ d → d < 14802 → d.gcd large ≠ 1 :=
  coversHeads_sound large 14402 400 largeRange14402Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange14802Checked : PLift (coversHeads large 14802 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange14802 : ∀ d, 14802 ≤ d → d < 15202 → d.gcd large ≠ 1 :=
  coversHeads_sound large 14802 400 largeRange14802Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange15202Checked : PLift (coversHeads large 15202 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange15202 : ∀ d, 15202 ≤ d → d < 15602 → d.gcd large ≠ 1 :=
  coversHeads_sound large 15202 400 largeRange15202Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange15602Checked : PLift (coversHeads large 15602 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange15602 : ∀ d, 15602 ≤ d → d < 16002 → d.gcd large ≠ 1 :=
  coversHeads_sound large 15602 400 largeRange15602Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange16002Checked : PLift (coversHeads large 16002 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange16002 : ∀ d, 16002 ≤ d → d < 16402 → d.gcd large ≠ 1 :=
  coversHeads_sound large 16002 400 largeRange16002Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange16402Checked : PLift (coversHeads large 16402 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange16402 : ∀ d, 16402 ≤ d → d < 16802 → d.gcd large ≠ 1 :=
  coversHeads_sound large 16402 400 largeRange16402Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange16802Checked : PLift (coversHeads large 16802 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange16802 : ∀ d, 16802 ≤ d → d < 17202 → d.gcd large ≠ 1 :=
  coversHeads_sound large 16802 400 largeRange16802Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange17202Checked : PLift (coversHeads large 17202 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange17202 : ∀ d, 17202 ≤ d → d < 17602 → d.gcd large ≠ 1 :=
  coversHeads_sound large 17202 400 largeRange17202Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange17602Checked : PLift (coversHeads large 17602 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange17602 : ∀ d, 17602 ≤ d → d < 18002 → d.gcd large ≠ 1 :=
  coversHeads_sound large 17602 400 largeRange17602Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange18002Checked : PLift (coversHeads large 18002 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange18002 : ∀ d, 18002 ≤ d → d < 18402 → d.gcd large ≠ 1 :=
  coversHeads_sound large 18002 400 largeRange18002Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange18402Checked : PLift (coversHeads large 18402 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange18402 : ∀ d, 18402 ≤ d → d < 18802 → d.gcd large ≠ 1 :=
  coversHeads_sound large 18402 400 largeRange18402Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange18802Checked : PLift (coversHeads large 18802 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange18802 : ∀ d, 18802 ≤ d → d < 19202 → d.gcd large ≠ 1 :=
  coversHeads_sound large 18802 400 largeRange18802Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange19202Checked : PLift (coversHeads large 19202 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange19202 : ∀ d, 19202 ≤ d → d < 19602 → d.gcd large ≠ 1 :=
  coversHeads_sound large 19202 400 largeRange19202Checked.down

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def largeRange19602Checked : PLift (coversHeads large 19602 400 = true) :=
  ⟨by decide +kernel⟩

private theorem largeRange19602 : ∀ d, 19602 ≤ d → d < 20002 → d.gcd large ≠ 1 :=
  coversHeads_sound large 19602 400 largeRange19602Checked.down

private theorem largeCovers : ∀ d, 2 ≤ d → d < 20002 → d.gcd large ≠ 1 :=
  (coversJoin (coversJoin (coversJoin (coversJoin (coversJoin largeRange2 (coversJoin largeRange402 largeRange802)) (coversJoin largeRange1202 (coversJoin largeRange1602 largeRange2002))) (coversJoin (coversJoin largeRange2402 (coversJoin largeRange2802 largeRange3202)) (coversJoin largeRange3602 (coversJoin largeRange4002 largeRange4402)))) (coversJoin (coversJoin (coversJoin largeRange4802 (coversJoin largeRange5202 largeRange5602)) (coversJoin largeRange6002 (coversJoin largeRange6402 largeRange6802))) (coversJoin (coversJoin largeRange7202 (coversJoin largeRange7602 largeRange8002)) (coversJoin (coversJoin largeRange8402 largeRange8802) (coversJoin largeRange9202 largeRange9602))))) (coversJoin (coversJoin (coversJoin (coversJoin largeRange10002 (coversJoin largeRange10402 largeRange10802)) (coversJoin largeRange11202 (coversJoin largeRange11602 largeRange12002))) (coversJoin (coversJoin largeRange12402 (coversJoin largeRange12802 largeRange13202)) (coversJoin largeRange13602 (coversJoin largeRange14002 largeRange14402)))) (coversJoin (coversJoin (coversJoin largeRange14802 (coversJoin largeRange15202 largeRange15602)) (coversJoin largeRange16002 (coversJoin largeRange16402 largeRange16802))) (coversJoin (coversJoin largeRange17202 (coversJoin largeRange17602 largeRange18002)) (coversJoin (coversJoin largeRange18402 largeRange18802) (coversJoin largeRange19202 largeRange19602))))))

private def HasWitness (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ n<p ∧ p<2*n ∧ (n^2-n-p).Prime ∧ (n^2+n+p).Prime

private theorem witness_sound (n delta : ℕ) (h : gcdWitness small large n delta = true) : HasWitness n :=
  gcdWitness_sound smallCovers largeCovers h

private theorem joinWitnesses {a b c : ℕ}
    (left : ∀ n, a≤n → n<b → HasWitness n) (right : ∀ n, b≤n → n<c → HasWitness n) :
    ∀ n, a≤n → n<c → HasWitness n := by
  intro n lo hi
  by_cases h : n<b
  · exact left n lo h
  · exact right n (by omega) hi

private def witnesses4518Data : ℕ := 0x6837102b00610bf02e3006815b00a032b194020b02c83dd03580b30098025073016708080830740109004030b02f801303500b507b80fb0b9804306c8259007003509b804711900a302e090b092804f0d400a9017811910f017f044018102c011908380171eb004f01a805f083805f00682590bb01f104483c101d04db03b0041038814b06080c70b0012b092808300b025304c00fb068827506984b10bf80b901f003b015810f0368119005809502903d9010009504480a9057826501f058d263811305304a500100a100a031305781b700b03f50b08091015805b009801701480791aa811b0250095029805915f806701e81c110f000b045803110a801d068813700504e100884070100073060806d00a00fb0a781c30c9801f05b01a306580bf05c038500580830c7005304d015105b016702800430ce012d00400ad0ac01db06502d10b300b301181af0590265018820f10a82db02f004f05d87070e20127009824d0ef00fb086802507400f1015805301780610d8817b004000b026806d2138181021803b044818706f8007030829309a009b07402d701f058d0568095093854702904f1038818b26a835b090825705c8473

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses4518Checked : PLift
    (checkedRows (gcdWitness small large) 4518 witnesses4518Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses4518 : ∀ n, 4518 ≤ n → n < 4768 → HasWitness n :=
  checkedRows_sound witness_sound witnesses4518Checked.down

private def witnesses4768Data : ℕ := 0x53800506b009d01a829f038800b0c08d5d04480a1004013f164038508e028d04481a50ab800d07183a10628167131010f04881cd02980410c6812701f00830190007075812d012800b2b782cf015856500981d305b00973e181a500b02b706a003100681ff00382571c3009704400370ce804711c80d907402c5083014f059807313a0739028017f07d801d0b3014501002ed05682d104a004901001fd03880490260421010016700280770cf845703b0209007006d07e801300e00710628173006808507f01790f1038f015818d00b003b05b00cb0bf0031038815501d80df00380d30428053031001331a00a906b0059002805b024823501481c1004003b015820b005023909e804709f80af0a400fb01a80bf0b4840f1000227119804d15c81c301d0149152807700e014501a82a50a902db135829b02083dd088019101e803700e010d00a00b502a806d01a03e306d009506500790110059046009509501cf09400110f882c503e00a300f821b056803700e02cb0290461016000d2e4042d022009b02c81d301d084707e88c90dc00fb1e681c3007027b097005906b051d00d01910c700bf00384ff01d01fd019002b0c804ff

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses4768Checked : PLift
    (checkedRows (gcdWitness small large) 4768 witnesses4768Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses4768 : ∀ n, 4768 ≤ n → n < 5018 → HasWitness n :=
  checkedRows_sound witness_sound witnesses4768Checked.down

private def witnesses5018Data : ℕ := 0x60801f036803b05e029504d01c902183cb19d805b02902d703f83fb0028101012808b00e02f904481d301a003d06380a70c100ef02c002b000820318e803100c8007029056306a0079035046903100d100a008301a0121038836b02c804103b003d02c01b5017812b0dd009102000d708080d303b004f05d870711681c3092028f00b00830e3802f0aa049303880a1017804d00680c705e03d702082b10ec02b301e810103883a107a003d01b81eb029801704701db02482cf0190199012815d029837101480b30b3006d005010d00a012102180f1020016700100a1006824102a82270d3000b00f80af017826300a00170848943026809b007009b01a0169086806b03a00bf04e8163008012b0bc810d0f200970320281097009b017015101783cb02c80f708a8a9f0ce82ab02380730a1010301a80e901901e107b809101580c512880fb05180c1000830b038804701a02d705e041900700bf057823b008851500400f525e839700b82ab03580fb48e00f1036802f05381af00e00bb03f808305681a903b027107708e703700c50b9032b00b001700400ef05d852901300a70118199060827109b82f305b005b060804f04180a1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses5018Checked : PLift
    (checkedRows (gcdWitness small large) 5018 witnesses5018Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses5018 : ∀ n, 5018 ≤ n → n < 5268 → HasWitness n :=
  checkedRows_sound witness_sound witnesses5018Checked.down

private def witnesses5268Data : ℕ := 0x2202b7086807d0ce07db0278095010003104e8319044809b004008b05f018d023011904c00ad008030705903dd02980a3017016900400d70ac035b03386af00500dd05382631460217000801d1738065176007909b003b06d00291fe800700e003b061000b02d823b05b00bf00401010c6808b01d84bb005807903380df044018b15a021b13100fd0670257119822100b0055062805900b813f0d2805b1be80e909d005f03b004f00e01c103e803b0e78067063816d0a900a1051804307300fb3f5800b009848706f800b1648007048810304e80fb040004d02182e3043003b0cb840f1028bb908000c500100bf02f02c5023801d0ce81ed00b001302683dd043002504700130c2017f0ec82d5068004f04602cf01481c1029007300801a904c035b02a80f101e803b05b00ad0d881d501a83a1022000708482b300e00b900d00a7189830113003f502f805901a00cd01100f502e003b041009706982f90538113008010306d058d029816705783c106c807101c048d06f803102080770148031024800d01701850040191042803d05a8191010001705a84ff10780a1011802b029021104781cd14201fd07e850b009808905f8173

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses5268Checked : PLift
    (checkedRows (gcdWitness small large) 5268 witnesses5268Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses5268 : ∀ n, 5268 ≤ n → n < 5518 → HasWitness n :=
  checkedRows_sound witness_sound witnesses5268Checked.down

private def witnesses5518Data : ℕ := 0x4005f02f00f704481490370077005010f0560401059801901a001f09286fb076014b012821d02782a51d2003b09f804904e8059062802b087824d07480dd002800709e007904f008302682570ce001300e816709102811cd04750068e87092801f0e304a50a780470220049008033105e0e870988119074006d00102f30340031092007902c024b03e80b504282710040197029800b023014b00580a101f000d00681d5010025703400b3066838502e001700b804f01581d503b0239136004f08a809100700a70b080950e780a30028167074806700e0019004000b007020b093801306d004102500d710d04ff04d02e700281cd00e001900681c1121004706801ab06a007702e013700b00eb0a102f906d003100b05dd06d003511b021b00b0b5303e803b01c02cf05902d101604d307c009515f804f00c809508800470110451031021b24400f107402c5033827b0ac0041198801301601d30b9804f2630055054816709e80b504d031f01f0581100010f07882890010095029812d01b805b074081b01f004f0e7801f0a4801d00d00f112380b501d02a51f7801f057807f02b00830ce80d3008003101d059f0c5800702a814b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses5518Checked : PLift
    (checkedRows (gcdWitness small large) 5518 witnesses5518Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses5518 : ∀ n, 5518 ≤ n → n < 5768 → HasWitness n :=
  checkedRows_sound witness_sound witnesses5518Checked.down

private def witnesses5768Data : ℕ := 0x30866102781970fb8029086008501005090ad8029015835b013063512880850ed8169059017f053817b099839703b82cf12d024d029039d011005f03581d50de809703a023909700dd00f804f01281c104a804d02600e500380e9010019f14d8367005002f04c010f056026502c8101199001d077013f02081df038804105300c701782ed00b80b5021834902c00b90c402052660547025004d06a01af15f8b5901580c50e2036701d021108f038f08b004103e019f017890501900f1050001f00401310928127051850b0ae80bf0898167030819f03e009514380b502f00d301e86f515580cb03e001300e030b01900c100083d309700a1022000702900b50a901670e382db003809102382f30c7026328b80070370155281800d04289490568209073004905787b1029026f05800a70c6810f073001111b005901581e106d021b083801306f810300281910388017035009d006822705e00670c8004f04000350e681c911180a900280e3032803b1e3805b01001130718079050030110a02570f100d305c01db0478083239803103f8103022004104f01510c6813f01600290580047095005b03f806b01f031701b80f101c010d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses5768Checked : PLift
    (checkedRows (gcdWitness small large) 5768 witnesses5768Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses5768 : ∀ n, 5768 ≤ n → n < 6018 → HasWitness n :=
  checkedRows_sound witness_sound witnesses5768Checked.down

private def witnesses6018Data : ℕ := 0xd1004700580bb25e82c5064026308f800b030814500f805900401ff01b808b04e812b0d601bd02c01510038137011803d08a82770a882f906a013d04a0397037002f05380130248175023832f017822f01d005b00c867d1e880e9020015d029830b059802f02a81ff03580170bc809d02c0637065810d01900a116401cf00680050bf814922d019900583cb013005300b018d06a00a10160031005052901581af02200a903f8655098012b148008303f819f00b811f031019903b012100a04730ce80cb0c9844b01a00d1029800d02600a901001cd0a1804300e05fb02a803b02800bf0680085010001d1bb808b09080b500088031468055069806102900591d8002b000857706c82210b9849101d02b3045817300880fb03080d300e807d09e801f07e80a303f8149038807d05302350448119077803501282e300e046102e005907b81f3039812501000dd056001900b82cf01f001d02780f101480831af803703501c905b003b02800130500637062817301d80af04e81f3004028d00a014b03f8409008802f0e2014b009811500f8a5b083835f02900370a902f90bb011f02a814b006805f03d004107e809702c813d09100c7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses6018Checked : PLift
    (checkedRows (gcdWitness small large) 6018 witnesses6018Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses6018 : ∀ n, 6018 ≤ n → n < 6268 → HasWitness n :=
  checkedRows_sound witness_sound witnesses6018Checked.down

private def witnesses6268Data : ℕ := 0xb80af0db809101f0551025003b00f80b502680cb077803101281d5034017f04600d300e003700e803b04780d313d01c904900dd029812517183b505680dd0fb819308c11771738065038807d01a018700c82b101781690d8806702f02991bb801d01b800d028021b01f0049018807f07b81370190079113017b0590053049010103084e1007005901f00dd14180a304301c1004019110581030218263038805f00681630bc849d02500ef069845703b00cb0448073003823b0c7012b014801303f82cb0520041107814b00681f301e8a5b0268097006810304f03a1052002503984930ce02e707780a900b0745011002f09400c702c0451092006b13f004f00e01f302d82f91ac824504a0499035800b06b81391e3824d053804102980890dd03a3009833b00282592540385044801d06d009500e0139005031706a00b9072827101d007718881c300381f303d013703d00e50a881b70c8003507601a303b0277062801d0c701df04a020b037049100b800500980f7003810d0070115083022f03f862f001000712f82ef027819d0058e5f09201db008025710001ff13a010f02a805915d0229060849900e001d00a009d0d7012d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses6268Checked : PLift
    (checkedRows (gcdWitness small large) 6268 witnesses6268Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses6268 : ∀ n, 6268 ≤ n → n < 6518 → HasWitness n :=
  checkedRows_sound witness_sound witnesses6268Checked.down

private def witnesses6518Data : ℕ := 0x1a015700e813101000e5039830d00b009514b01cf08a855901284d9110829b1a780d301f0323176802f068007901d005300a01b700e039100e01df00101a306f817b01002db17800370f080af1148c59022015d0f5036700402510df004101d07f901d00ad0b9824d17a81bd03f81a921101190b1810f0050083017800d03f831302180bf007042d01a014b07e83b906e811f07b845702f83ad019030d0b7811b0068059038808303b033100101671d5005f029040f05b04f716302150f0804f01a815500100d71c5836701580170358187006814b02183890ec803118380131180167056829f05a80c703b001d038801f00c87b10ef029f06880a900380d302a8359058003d012839d0098059035804f006817500c80470970155074018d03f80bf00e801303c83a3060838f0298043114813f018826911681490bf028303e007d0fb80d30e0008b062049d0fb807103e0007008858d05680530218df3015804703881db0a101a500e80e900100a1051838504301e505b006d015801301182ed00400d7024862b00684bb03b80a902a803d02681a9092802f0e781b700c80ad00d00b51df0247006801d031003b00e03a3002830b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses6518Checked : PLift
    (checkedRows (gcdWitness small large) 6518 witnesses6518Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses6518 : ∀ n, 6518 ≤ n → n < 6768 → HasWitness n :=
  checkedRows_sound witness_sound witnesses6518Checked.down

private def witnesses6768Data : ℕ := 0x13e80bf0d9030b01d08fb0e302e700280470ec000d06f813d0ec81c113101c903582cf2db813914480070a4014931601d300086af029013700400e515f82d1051810104c003d05d8067020015b02201cd08d82bf04e81551f0014b01280370290263043031f05a8013003820909b8059167001f09f816711b010306500f1003819717380fb006802b04c03a1010000b030861f004003b0070013005026b0c2034108c804d176004f00a05e7010001d0c9810f01303471e1088f0aa00d301a00590220221021804300e0509065818d03984930c985ff094000512b02ef01108bd01480ef0d5803d006838906a03ad11c023b02902f9100016101e822f07c02b1073005b02a804f0b0807d00b82b702187630cd02bd0c5825901a012702b00d709e8191138827d026053301f007d047028f137819102200170e482d11f0026f01c04e7105816902302753d00167128002b02c002f1078187036812100b025704782590ec035b06a0047022015507d088f06580dd01002ad0650655007004709e81a512f8547011029919d81a508c00fd02a81a3004005503f841502910eb0a9008308f023b01780dd05e001103f803d11c011f035812d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses6768Checked : PLift
    (checkedRows (gcdWitness small large) 6768 witnesses6768Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses6768 : ∀ n, 6768 ≤ n → n < 7018 → HasWitness n :=
  checkedRows_sound witness_sound witnesses6768Checked.down

private def witnesses7018Data : ℕ := 0x8380df00e0a1b03d0617061002f03201f3056826f09d00c503b018700e01fd07180ef0c9812700d00950b084ff03680f7073041903d02ab015834f07b83dd038810307b863701a80bf00e817b01584ff01b811f107821d02182d104401d317385c946a026505f01cd06d000500980e505682ed0ca0103035058302183e3047803b07e82b30b1817f127001310282d105e0185224801d20301ed02a817304c009b009819f008833504f00170ce001300683f505e00f708a82b306b0089049004f065016900e80b30a6003b00681b700080a10bc804109080310740065070004f044048700e01a9080805507e81ff013016701f019113282bf03880b9053810f00984030290185577042700383e503080830fa004305781d50518233058000505d85a10ea8071053813f0ef030d01d847306a01d50518187008051503106d903e00c706c847300a004708002a7040014f0088103056023b00e008902801870248079009845b218824503b0085044819104481a902d80e500e0119019004f056010301a046d02e038b1a308e901b812506701f302c0127001017907180770428079002802910782270f200bb00b84bb0dc00130920637

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses7018Checked : PLift
    (checkedRows (gcdWitness small large) 7018 witnesses7018Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses7018 : ∀ n, 7018 ≤ n → n < 7268 → HasWitness n :=
  checkedRows_sound witness_sound witnesses7018Checked.down

private def witnesses7268Data : ℕ := 0x19401b108d81f11528173045803103e892f13482150ce00130a601cd007026305f02d10c200290c700370ab87b1006803b0118155102820b009810101001ff02780310308d67206800b008001919d897d12b803b044003d0c70191014838903380b504a81a301900bf07e822900886350e501e106b00f1021803b1d50073024810300b09410a0006d005003106f83d701c01a31940457007026f0a3001f08d80a300801130fb840f020017502306f521100af017002502c068f07f02a500c82c500b041f02e003704283c102501610da806d0a400b503f82b711e003b01d004304d80a1022009b03f8271053856319f007f04b80e5004032f01f080b185012d01a802f053854719b8055015813102682cf018813901280bf013005f08f05c504a003b10d806b0cf81e103d004704180311c595c1029809507d804f17d80b5008810d004053305c007f02601af05680a302d839703f8119091030103f880b150823302200070ba83a305980ef08200c7006811b020016d0448103005030d06a03cb16c00dd072808b0310185028010f00804e100b801702980cd03f850b022001103d00d10b780d302201df0f1000b045810309981c1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses7268Checked : PLift
    (checkedRows (gcdWitness small large) 7268 witnesses7268Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses7268 : ∀ n, 7268 ≤ n → n < 7518 → HasWitness n :=
  checkedRows_sound witness_sound witnesses7268Checked.down

private def witnesses7518Data : ℕ := 0x29826f07600a903f813f050012b014845503081cf06a015b01f0047041026b04d81af10f00830218127004020900401b7003835b0bf021501d80770a403a301884d904600b307e889b018809b17f80f10a7000701a01731c3004902900eb06c80dd065800700c8937079017f05e03470ce06fd00a02690a6013725b841b01000ef05e00bf11a8067057855117f82ab00e0145030821b00280c707d00e50478005026809b03f8079011800b0460059015849305601f106a003d018819901902db071801901105ef004043702f819305a83fd00682e701c006d0dd001f019011f101811905901390160179044814b05001e100384430a6011308a80a90130185095829b041013f00e014f06a01b7042812107581c1044803d09201db056010d130005906681e10eb0263017819d01e85591fa8173137816902602770158323184000502181f3022011f03e83fd14180fd05d81e50cb80b5129801306281eb0a6016901d04e700681af04301ed0a282e30bc821512b812b09c80791af8227100079d06f801f020022112d014b0548007002837102200371c4007304a005901301fd08c079f05d835f00100413a582c508c04d90118137

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses7518Checked : PLift
    (checkedRows (gcdWitness small large) 7518 witnesses7518Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses7518 : ∀ n, 7518 ≤ n → n < 7768 → HasWitness n :=
  checkedRows_sound witness_sound witnesses7518Checked.down

private def witnesses7768Data : ℕ := 0xbf809106b022f029809513000650b1824d09e81cd05b00af05d80f102a82f908802b30fe007904300d70130059039817b00102930bf805313a012103b05f90d9007103c83df030815509e825f030855901d0077134843902184ed03f805f1960031020024700105c90928139018828f022010d02981ed08f0379056011306a01bd158015d02300470b9808305904270ad01490e200790b3016902900fb05b00eb0650415099869b04d80070b1805b13000ad1f7800502c0883093817902b000b04e8139005810101a844b1d7828302f82bd6c1017508f05a700e02271090025012821d03584f10040127167038505480d102800d3015802b02384670568079089004f00c874f0c7003d020023503f80590f7004d032003104282330100013272055904280a1019004701a096d0c881a9044813f009818d0c58641196007105302a7088027509580b505780f10a881eb01301b700e021d00b80ad0b5003d06f861903083110cb812b032006d03d0a6d0bf812706b03a90ce04af00400110c8023b06f810705203b3060805b0368173028012b132814b00b0005008847f02a842d04b8365071809707b803700e03290e080b301b815d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses7768Checked : PLift
    (checkedRows (gcdWitness small large) 7768 witnesses7768Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses7768 : ∀ n, 7768 ≤ n → n < 8018 → HasWitness n :=
  checkedRows_sound witness_sound witnesses7768Checked.down

private def witnesses8018Data : ℕ := 0x9c855301f004115581f302a80a306c81af06d01bb0098235013017302c80fb099812100b004702e03e506f814b05c011f05380bf08303fd00700b905b01af018810f01f017308381cf0b001bd13001fd011803501700d300100ad034001d03382ef01a80173be004f0bf0019015803b0d601df06f80f702a807700b805b00980af00683dd06d00530440b1700e041f016003112380b501d021b01000970608079001005f1b702b30e603eb01280dd07c01db00b07b7105808301300e305f0529015808302200d7092037900703d101f00470c2001907184df242803107a000704c01fd083802b006809d047825707c015100c812d0220155029817904a04b1083804703d003d01a013902503a10dd814b0458955074060539b804901d008b12083e9002804f084810f0178005007001d01581c304583fb10f05090128253027805f0e5004f05780a300580d1001006707a01270568077004018d155119500e018b0bc807f18501c300a0167098805902181bd07601d30bc8137068002b023825721100af0a580f705180dd09280cb00c814b038872b040031d059014b02200bf062816718c82d10340089092804f02783fd00a00a1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses8018Checked : PLift
    (checkedRows (gcdWitness small large) 8018 witnesses8018Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses8018 : ∀ n, 8018 ≤ n → n < 8268 → HasWitness n :=
  checkedRows_sound witness_sound witnesses8018Checked.down

private def witnesses8268Data : ℕ := 0x100cb0ce80430ce001f01580dd163001d11c014b07401010e981ff006813f06c8185100014508900cd051822708e006d01b930f02680dd0c701152108b1701d81550100293194018104c020f01000bf08480c100b09b9038808325700d9059007707f00670c3817b077016d06701b703f8031025020903d01871c8830706e825d11e0121042806110001550d300f10170109086008315400b3053018701d014f19d841f00b00f103700b301481490d881c300380d1004018703b01b706b812b04480cb01d06f106d03fb181023902d810f00682b7023811f0c68547052013d110826b173002b01d03590388245036824d01e829f04781e50c9855902901670a4810f05a8619017838f04c0089141832b060801d002833d07e813904e81d30448095006800d04900bf18a001f02d809d03f812b028002501700310178053052003708a872702a80bf053815501a0157068000504482a703203eb019003b09a004906f826b047888d0e800e307108e9001024500e81df02900c70388371163019107e8085000805f022003d06b03910850059035801f011023501a85ab05200f707880130b801bb0ad80910308c3101d81eb06a0167

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses8268Checked : PLift
    (checkedRows (gcdWitness small large) 8268 witnesses8268Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses8268 : ∀ n, 8268 ≤ n → n < 8518 → HasWitness n :=
  checkedRows_sound witness_sound witnesses8268Checked.down

private def witnesses8518Data : ℕ := 0xd602d503b011500400831c1815703c83c1010028102c820f20901c304881250a782750f68079017803b0bc80b5039844b01b8137416806502785a7062877f077800707582c50e500d703b80e3003822f0458053097007700b01570b3012b2638239122001f005847f038803700081030ad810d04a803d00f808b0b8018b023810d07b8a630e0046700d00310ce00a303e004d1378047048800d014803b05b004103e028902900bf02200072300097042826301602ff0a884ff019017f07d80a103b02470260167004009708600bb03d011900b803d06f801908b030b00e821d1b08169006800b0b9806b07b828907e815500886530158073000800510786e900e002b00104912fe007d02f04510928a8b0220155008079f01f0311025007f04706fd00b819d17f821106800fd003824b03d00a900c81d500a0257191801704d00f706f8293190006d00f81a50568083047803112382c500682330178329189810902382a506d038501581870718eed0b8004908f007f0388275046001703f804f065008315881131760a45020003b028071b51082a104c00b90b501b70b183a303a01df022006501881bd14383651e4001701e81ff

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses8518Checked : PLift
    (checkedRows (gcdWitness small large) 8518 witnesses8518Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses8518 : ∀ n, 8518 ≤ n → n < 8768 → HasWitness n :=
  checkedRows_sound witness_sound witnesses8518Checked.down

private def witnesses8768Data : ℕ := 0x1a7814500380e310000a9185019900085ab07180d707e801916b85150c580f10a285fb01a830503400d70c20a5105f01c100a016900e01e105380d70ad810302c0103067023901000e90c681b707e89d7007004f02185ef03380e901780251a0004f02500dd014812b07e810f02b001111981a306381d50190257155812703b004303086ad043001d02a81b70358803038804307e810f03e810103d01030128253006813d080819112981c901e8275143810906c84990ec805906b800d008014b06082030688179024806d00a00cb00d01b707b85050bb08330ad81df036806d00100dd1c3002b089076901d00a102800850f802ef08b00830f580430650c9d03701d306a010302480af018822d12d01cd086026b01a038f17f807104b829b08d80770a7809700380d30478e5109a027b257076302f01f701f02590e000a30a1033b008803d0ed821d02e017302e0005102819f09982810bf80dd08f032b03883f506100d704e81d50fb8245023826316701a50148677053808305f01990970257029842706f8199006815500700d104e80d308b006500580950ef028900680bf011803d01586af02f009b0388191050000d00f867d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses8768Checked : PLift
    (checkedRows (gcdWitness small large) 8768 witnesses8768Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses8768 : ∀ n, 8768 ≤ n → n < 9018 → HasWitness n :=
  checkedRows_sound witness_sound witnesses8768Checked.down

private def witnesses9018Data : ℕ := 0xb018b01c001d015836701603ef037008b1b200cd01480891a800b5006800701e82f91af80830b00c0d08f8239038817500080c700b011300e80310d1003104880bf02e027713280fd018807d12d01f303201d5005807710f00cd13700c701f0047106004303f827701580d7133004f07b812104280dd0a000dd0e002dd026809b0628149204807908805ab00401450338037029825708680bf0350ac903d001706704ab0ab83c101b82db03e80d124802b3012804d05381f301d03d302d811917f801907403d90310119056808307b8211017800505e008900e018703100290eb01490ef007900b820f11980a1093811b0260137026812504e83250740635022010100f8bad00e0119058020308d83d301880ef0820173021806709e804d05b0121006807f023820905b008304a018d083821b02980e90d283df0158587013005917301b70d4001d05800830128181020020f06280fb00501e100886350790073036823504e8245065804308c02c5047814f0388005012810302201f105f801304a017509e00c50f884eb01102c5023826309280970e4820504f019101a809709985dd03f801710a8101015815d005017300a0487

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses9018Checked : PLift
    (checkedRows (gcdWitness small large) 9018 witnesses9018Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses9018 : ∀ n, 9018 ≤ n → n < 9268 → HasWitness n :=
  checkedRows_sound witness_sound witnesses9018Checked.down

private def witnesses9268Data : ℕ := 0x4020b02180130448077068804d0230955022002909d015b14181a500c808305382a725e862505a81df056808308184b10bc814904f01cf02180071bb82f900a00c702a830100b014f02681f3330814b03381af09e80b502c01cf04481a3097035b02a80a3058013700880cd116010909281df00700b303080e50a400d703a002f12b035b06b80ad02f80ef1d4828f05e015b18e82a713a028900803a114681a906f812706c80bf01900df084810303580f500b81631be008b006800b01c008304e8037053820f3df0047005001301283cb0388073009809d01a01fd0ac008307580c7038803500d01631910169002803505506170038139004003b010005914f005b03f83dd026803707e82d700e038f00e806b05003d3012804105b00b306c801304d82f90f8805b07401ed00102750a6004f081833d01902f90bc823b09981f901a8083025001300500310100041004001301d03d300e06d710c010d015806702481f11c3003b275040901b802907c01e5074040301d00830478031122014b029019102b007d03f831f03701c101480bf05d89d300e01b5022010d01d006102d90df0e2009b09e050501a0083101804700c8097

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses9268Checked : PLift
    (checkedRows (gcdWitness small large) 9268 witnesses9268Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses9268 : ∀ n, 9268 ≤ n → n < 9518 → HasWitness n :=
  checkedRows_sound witness_sound witnesses9268Checked.down

private def witnesses9518Data : ℕ := 0x7e812d00b83b30298059095023b02a81a306d006703080310b000770a900df01e814b00b01af06580b300b025908c00a1019004f0e780c102f007d00404610f5014b026800b09702f90f080d90100545020807708a81a507e8017001017921082d106400c500a000b0c68091010025705e00b50278259028095f0220017029018101784910070185057857700e070d014800510581f3011034103d005b10d016903f8257004006d05485d100c8077182803701a018d056010d06b80ad0a880b5065008307f019f006863702980590eb0169021807900102a504780a907d0067053817324a01b10e001f301584eb06580dd05f04c301782db02c80071a0042d00a000b037040f141800d007004108b01f3032006d01f07bb24580e903f80730bc85bd142001718380f1047807d053807d00e024d018803b028006d17301f9090813d4528167005045700a004713f002b01100370b3009500e8011017006d00880fb09a009b26d840f08680d103d00791e38049030804d178004f0fe02b901000dd013007300080070560155064009501280b50428119043027508d86af00e02e10028191182003d02202ed065823904d01e70358d49

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses9518Checked : PLift
    (checkedRows (gcdWitness small large) 9518 witnesses9518Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses9518 : ∀ n, 9518 ≤ n → n < 9768 → HasWitness n :=
  checkedRows_sound witness_sound witnesses9518Checked.down

private def witnesses9768Data : ℕ := 0xd1007d00d003703f8565007024b03282271460055008020f0220155011015700a029314b009b00b006d0298437016011911903b50290cfb03100e302c00c7089810719d84ff086010f00f82e117b00bf020017502180bf01f01ed13401f304c008308680d107b80b526b02ab02c81310dd01b705782c30be049308a809102481670d602c50d4016902801a305e0385119009d03386e902802a5096813f029001701c00893c681ff02c802f02800312bd005b00382572ef014b0b3001f06282ed2ab80f5033825329502f922600a9069841b03f8005023809101d001f013021b0a002630ce049301e845502e0353114817b02f801d03580cb08300bb00383dd00e80dd00804e114383e907480f703b030108d828d06e819106080b504702870130013048811b048831705384c90038a4b030801d038800b00f852904482b706101790ef0af901882870e382571f585ad00682a506a00310368169014849105e028103f8073040049d077814b10707bd074810700b82c5149021101a82db05b008301a005b03c812b02200130098061026004706d01e5008020505e1d5704a804d050042d0538569062809b28b804f05c01850b6803d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses9768Checked : PLift
    (checkedRows (gcdWitness small large) 9768 witnesses9768Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses9768 : ∀ n, 9768 ≤ n → n < 10018 → HasWitness n :=
  checkedRows_sound witness_sound witnesses9768Checked.down

private def witnesses10018Data : ℕ := 0x10041161004f0ad8047029804903f812d00b8071044818d04e803100c82e700580fb150816300080d70d3010f13a013f00106e921d004101100430ec03fb028002500b06af01d03a70b2009100b001f0250269014829f0ec00790a9056303d012134e808500b038f02e01cd030824100e012b095804701a0031012844303b81bd06c8649091008311b02d101d031902b046733d00830ab831f058026319900b50c38031017874f11500610530457074023301a806b0c2023b08900a10d3019905901db01d06e9199000b18382bf02300fb01f039d07b84b7132868f0a00017030813f015801700700050428103038826f02b000b06504f900e01850cb803b0a2801f00f83171c600f10680037056808310a82f503080b501d010709d002f0d101f3013040701f014b0e0016903e01310bc80d108d869700101df001024506f8a0f07902391d801a30a1003d02981c701600e30f6813f08b001702381850a1020b03284a30c7001d033801309e03530a900530800055004074f077803d10b83a300b01e500400b30518187006810700a01690b3040900b03bf083804f00981330ce01550298041003804f06c812b16f011911182d1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses10018Checked : PLift
    (checkedRows (gcdWitness small large) 10018 witnesses10018Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses10018 : ∀ n, 10018 ≤ n → n < 10268 → HasWitness n :=
  checkedRows_sound witness_sound witnesses10018Checked.down

private def witnesses10268Data : ℕ := 0x56021d018818b06d04550b90013074022701a80e9059003701f03dd06d006b00806cd1a0816d02b00c5132812100282510c4040f03b027701480e3065830b0aa01750050bf304000830068199015803b05200891dc007902903cb005807d0c2021d018820f05080d1030806703b077f15281030980025073130702980f102d82cb09a074303e819709e00310130083068818d0650d99059801708f80b306c808502c004d170816709c80f707580b3004005300f828f02e040700b821b04b801305d80a1070003b16401c301880e30280103095005b01a0449017844302c056b056015509a00b51df018d11e02db0130239116088f053803504f003700e03fd00501eb041805b06500c1016011f19600a903b01b703983a10cb808300b01030608227034001308a862b0f1000b16d82d51fd05d105683dd01780fb029017508503fb155838f24f809d07d8a4f022001f06f83010f40155077802502183c1004039b08f801d03f817b09d005924b895506f80c10c3804131c00e5054802508a816706d02fb04400cd021830b0c7012b0b0134b00e007101a8241015845703e804d08f840f006814b00e861d0fb81b7015815102907d9

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses10268Checked : PLift
    (checkedRows (gcdWitness small large) 10268 witnesses10268Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses10268 : ∀ n, 10268 ≤ n → n < 10518 → HasWitness n :=
  checkedRows_sound witness_sound witnesses10268Checked.down

private def witnesses10518Data : ℕ := 0x9c80470520011083079f02c812b00a0407012814b03a02e106580f106f82110c8022717f80a301704ab143815510a80791a483490a400fb01c029319b81b702201bb10900e5111843901c016701f000b0c200a300d004708b00dd03080af0f1083f110807f06500b5111800508e00b918981870b1880f07300f10c6828f00400890d6004f183802b041030b15283850770127006801d0c5813306204ed10a841f02c80373a581f302980bf0b502771df02dd0ac006b169019903e013f0a786b913781ed06b00eb04a000b05200d9056053b079004100b8059015814b038812b09b812b00380fd029001101a81690a4018d1a78cb3010000d16a030106f8083059811b08785d109e826f0880127092007905c0287019014901d008500682d50d3010302a806d062816700880eb00e00bb158029300a01250b18103155800b0a482d70a8806d06f819d0c102a708a8193035804d1d2045507d00a905500590a181a507b80a9029847306101a308f012106d00d70a4815d01a042d00401bb02380311208481099806b134837102a80c7050801d01780670bf0037092049100703370ce003d051802901480d702905d100980d10358149

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses10518Checked : PLift
    (checkedRows (gcdWitness small large) 10518 witnesses10518Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses10518 : ∀ n, 10518 ≤ n → n < 10768 → HasWitness n :=
  checkedRows_sound witness_sound witnesses10518Checked.down

private def witnesses10768Data : ℕ := 0xe501d900e03c7086012b05502b3048861903b05a508800371c88199063833b00100a1164025903283c52110169041002509383fb0ce81ff02001ab04483dd00b817308f06850bc813701c010d059051d056815504c01d510d000d0298b3302680d107700c702687070220215089018d0ec0029034001d00b033d00b8065008814901d01c3009819d3b98031191046f0220005026808b042800708785ab0bc80eb0518163030804700e81670e1801306c809b01600410b0015d10d00a10790211065031902f005910304bb0158049056019107c00df0ae804f01000bf03100b5030863708b019d052029909206df01a823307a800b03f83fd09a010128602f9273812d04880bf038802b042864f0b78425068807f07100e5062800b0b5007706f841b0778119026808307e80d300086290b080132660421019065313480dd03b057d00e00a10568011111823b0b50503058004f1af05b31580b330280bf300b012d02f013d0b0821d077002b02303cb00b8305018809100b02b102200c105300e50ab847902c804103081c305202e104c0103141818703c812b02980dd00c809d0008d0106d00a31a480af02c021b07f010113e813f

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses10768Checked : PLift
    (checkedRows (gcdWitness small large) 10768 witnesses10768Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses10768 : ∀ n, 10768 ≤ n → n < 11018 → HasWitness n :=
  checkedRows_sound witness_sound witnesses10768Checked.down

private def witnesses11018Data : ℕ := 0x102814b06a011f02200dd13a00e508a8461022001702d801902480830b3803d107012d10281e500700430b300e5047824b00a001307b8253029004d056807707a02470b1812b0dd864f045810310a82ed06d0133143003d02c005f007002f006803d011028d1b400e51940175014821b26f80bf09c800d01c01df097003d0d40013001016701602e1128024d0068035034025d28b81b70be019d035803d158057106f809b15580b508180970008083134805b0260271143830b05980bf0038817042832f00e80e516406df01b80cb107832b185007300d02cf2608259057810304702bd047801705a810302682630bf811900089190a8808307f0031006872700985bd0a781991aa8163000802f1a802c526c008503701a30358227248012102684af013015b065004f02900a1052013d26a84cf00704a302f8199059001f029826904f04910de840909b007706280490158151088003b21b822714782d105182f906880f700e083503881bb07a80f103f803d01d01c106d044313880df01f0605056801707884b70f88491020802b01b807905d831701480e308a830d00a00e31d2008329f089b00801670a9014924e009d017829f

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses11018Checked : PLift
    (checkedRows (gcdWitness small large) 11018 witnesses11018Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses11018 : ∀ n, 11018 ≤ n → n < 11268 → HasWitness n :=
  checkedRows_sound witness_sound witnesses11018Checked.down

private def witnesses11268Data : ℕ := 0x2900ad01481130290af9045843106400bf1e3818703881c700b84d901d02ef071913906d00cd030830700e096b1b5805905601b703d00e9022000710a0a6f02c017f11081af2b58661054801d09e80a103e00a307583dd1378079006815d11483a10bf8085039814b0ef00e901f02c52a203fd00a03ad16d814b07e81c30128275053835b0f5029b01c020918283af02d822308a8b9900402110fb010f077062f0448163065026b06f826f01903670518085041827b10003dd02c01330460473134819f0080241008888d01d84430bf04930c984c706d000549105ef0cd01b504d83530f680670fb803b121000b04a09430c088c9017839d04b801303384911b5801705a814b05380fb164807f1118031041013d028021b1328391017001d071801f15081ab000845500100cb024852316180950a7800b03501c307c01e509e809510586190e60593011825714183bb096817909a017b1cb825f00085c918e8005080024d04488150a4801306981d502c04b502380bb141929707e80110d78335015806703081a908080130320289035809508380d30bc010900b83a10340139125029508b05b7001031d08a8a51023003b157003d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses11268Checked : PLift
    (checkedRows (gcdWitness small large) 11268 witnesses11268Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses11268 : ∀ n, 11268 ≤ n → n < 11518 → HasWitness n :=
  checkedRows_sound witness_sound witnesses11268Checked.down

private def witnesses11518Data : ℕ := 0x5680af027830705600470b680171a481690bc843104f003b021813f006805310c003b0f380eb0260479038817305c00a300c829f02981750c9829b00b015500e805304e8103015806504f028f01a00b503e80dd100003b149010901580950b5001f02c014b012863506281eb00380550308257073004d03c810f056819d07f037f042823b0250089118009703b005b01780ef242816905900df00a009501f013101a01bd03f838f020801d092010f07b8017025009d132815d02802ab09b887b24c807902c02d50a900830de82a1044819107c003700b02530518119004002504703a302e0c170310061065015d01100e90010155185019f02903a110a813f01b804f0a584f700401c7015800702c0077016017303f81f30b3004703282870ec00e5019008305c804f0ba814b030832f031001d0c500c105780ef035818b06082b9040058d01900e317302ef03f806505800d700b06cd006802f0fa00130c9830d022018500880b502002b30419085112003d044010313f01190298043026006d05e038f08380ef07b849300b84c71ae01c10608169014801120980a904a017b04b816709e852319b806d01780471ab01a30a1010f

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses11518Checked : PLift
    (checkedRows (gcdWitness small large) 11518 witnesses11518Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses11518 : ∀ n, 11518 ≤ n → n < 11768 → HasWitness n :=
  checkedRows_sound witness_sound witnesses11518Checked.down

private def witnesses11768Data : ℕ := 0x12080370058095173809705c006701b8473044800503e00eb00b874f064019905f01b707e82271f7802f047003101d020f014812d2810055038810d05b016901101a50008239029805f00f834f01f0047083804f0008a6f04a01c702502a504e8097055025104d810d03384ed004000504783e9054813908a82ed029800d017029b1000239065800d01b8493074029900d01bd01a063700c86a702f81a300b01db030807700b82b100501c90ad065308f823b01e80cd01281df01180c503f826b080814f034001303080a908b01eb00a003d4bb018106b0095001021d12e004f011985f100003700e01bd01300a1016001d0dd048705e019d01000890dd018701880e305c8595060849303b018500881a3081811b082037103580530bd8103056021b02801f101a0c6100e087502380610c200e501d822701901b708a8193035843d062814b02c035b035067110f05e102180070b3008304781cd47482c5062823301600110ec00e501d04130d3015d13a00a30170401088007910100f105780590cb8047017045111200a10cd0071332024d04000dd09d009512801a50050125020805900e001f02c803b05e00b503b027700d0119

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses11768Checked : PLift
    (checkedRows (gcdWitness small large) 11768 witnesses11768Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses11768 : ∀ n, 11768 ≤ n → n < 12018 → HasWitness n :=
  checkedRows_sound witness_sound witnesses11768Checked.down

private def witnesses12018Data : ℕ := 0x2e0605175002501d0b35004008305f813700b000d00b80770040169009807f02e252510a812d0f3829b006854506b80b50c0823b02c04791a8005900e044b08e02510550407033832b034031110300fb00e00b5005071317f807108d82d701d019101180bf017046907e820301d81e5056024d009825700d03a1111802b02600b300b803b0cc83a306402630bf81931f700d900e01af061003d06506a3015817310780cd03381f300a01a30ee023b0c980b501d04c105e014903e014b01a00770c700f510a007304c012b07a80b301a01f30a9022702c804318c830105782ab110815503f800d02382c314b01c3048833705f83cb3da8137026039d0e783ad038810309200e5038802900105ef06c858304602750850a6f065005b04481490220637045801304900b31960139098018d003874f15d014b0bf044b05380cb06282b91e6818703201f7032804f19b850b01102ff15a00d102a823b00c82f906a00d7018841500b074f00b80b507b81b701a818b079014508305590398491037003b08d803702982b70d6026300e035500802270b0843d056084701005630028007057804f060805305e02b905906c108380e90370013

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses12018Checked : PLift
    (checkedRows (gcdWitness small large) 12018 witnesses12018Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses12018 : ∀ n, 12018 ≤ n → n < 12268 → HasWitness n :=
  checkedRows_sound witness_sound witnesses12018Checked.down

private def witnesses12268Data : ℕ := 0x26818b173003707182270a90067048812d06f8317116804f1a780a9046005921707e522e814503080770bf810f081804f029003b11981ed00680130158167034019d01e814b06c811901000b90d5821106f81490aa82c503f803d059013d06d055904101c300502090478091029106f00b00fb00a012102a830d08b000b100004303f817b00280c503585470a4057d029809505e001300e0409014809500b801f13d038b07b805914500dd06981f30f88155062804d0218103056819d020808b0f381ed06d001107c022704a015703f81670d3037f0c502050100899019002f008009715500bf1348011029030d00281bb005804f00e00a300680d101f00770f2002b071005926b007d10d007302e01910d602b108c165701780bf086802503b042d065801d04900bf01286cd01c01673cb803b06800a306a03dd130009702c024107c0713092820b0cf80d304e811302c827503f8eb900e008304903ad01a003d02c004d0c70155101000d0308119029804904709731000bf302200bf0470a6f0a900050a4858904a00b501b805905b00bf167027101f022d09e82d118f816f04881a300b80350008343029033500e80790ed8103

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses12268Checked : PLift
    (checkedRows (gcdWitness small large) 12268 witnesses12268Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses12268 : ∀ n, 12268 ≤ n → n < 12518 → HasWitness n :=
  checkedRows_sound witness_sound witnesses12268Checked.down

private def witnesses12518Data : ℕ := 0xe4885302383650d6003b063815d0da81cd317802b08a81210a108e70ef804f0560b05182824505f81631418bf50110065035837113e82d100b806b08380dd0ed804f046011927a01190b3025f00400830c280f707d0a330fb8ccb0070073060832b031012508202770e7820b022007713c012b0de80fd100010d04781af011007f0220059083803102601b7006803503a001d00e030d004011f02080ef19b81b105d845b06d00dd01b83b502800dd01300af056044b07c01af00280a30800397010076705f812b07e84ed0098071044816703089bb0188cb908800650ae833700502f910780a300f81e704000bf0070011113076305182f3052011f09c81a500401d900d01fd0ce004902980b90f10155039818d037047f0fb809706501b706c800b01180710038199030833509400e301a014b052024508c825707e821d05181a325481a50908349001025714e00532618499015802901180590d28dc9012828d05800132fc046900a001112280830ce01c30088c6b112019106b00c1073095f06581cf011004313c0905007003104108710bc810728a830723d84c3048800b01480e504a020b004003b0ec813f06f818702a8af1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses12518Checked : PLift
    (checkedRows (gcdWitness small large) 12518 witnesses12518Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses12518 : ∀ n, 12518 ≤ n → n < 12768 → HasWitness n :=
  checkedRows_sound witness_sound witnesses12518Checked.down

private def witnesses12768Data : ℕ := 0x5b008306d0181239006d00981910190a270650367008014f07c038503e003103700fb00100e90ab848d065058109d00831ca044b0b804bb004007d0c208e902a80b30e680b501d011b059001d0e981c10b1822907b82390bc810706804ff164822707c005915986af00401cd0bf801300380d30fe003b04901c31d48343076009501a805b045840304600ef0ec80a3012807303d00a104a802b03f810300681e503880eb0c980e507783f514c805b03f8157071034d10f00b5018801f0038047004020300f809102180a1059801711a80e506c8113056806d2ed022f0070413055001f065032b01f00050ce833d042832b01a01af1d5011307e840302205ab00b801700c816903881a9008802f077056503e00710e680bf01d009102680ef11e01cd063840903d0c9500b807102f013f0bc8407130003502300c70a9089308c80e528b81e104f03a103700b50d5805500400b91cd84cd018808502f85090b800e901a0ab1029801d0d9007112080f1008827b0010059182044b0bf81d319302111988073027805f1ca812d1a1817500880b3029807902d807f00401370ac003d01b824d01002f903401bd08604ff00c803b0238083

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses12768Checked : PLift
    (checkedRows (gcdWitness small large) 12768 witnesses12768Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses12768 : ∀ n, 12768 ≤ n → n < 13018 → HasWitness n :=
  checkedRows_sound witness_sound witnesses12768Checked.down

private def witnesses13018Data : ℕ := 0x10780bf14481631f78ce3059804f00c81b707b81a903401f1029004f06d002907609610e000cd01e84b517b0209122001302380590970067072833101005270a780f702d80f10a180410aa814902c018702c810108c811904a000d00b012b03d01a508901390050059164818700382c500402f9020801326786a3092018b010001912f8e2f0658335085003d030813900e01fd0a9014b01d011500104bb0e200a301e828f00b02f9004012b074003109200d70e500af06c80970040233011803b0a880af015820f1c600e506800bb01b80bf01780470a1007301f01c112881490b9058306801c709a005f16404a505180890bc81b70ef0145009805f0a900bf006821109e00bf03582331e6861301d023908682fb0e6028904481e50ce813d11181690e0030b19000d31af018704400052368257020001309703ad289009b02900910538dc102200fb093813f0a10191026802f0650031089005907900b513a075d07d809b01001c302f016900a056f0178073078804305680830a7804702a823b16184970e685ef04a02d106b012b1840263065004901c019710002b107e820b097008303581cd02601f304f018505680830230013

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses13018Checked : PLift
    (checkedRows (gcdWitness small large) 13018 witnesses13018Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses13018 : ∀ n, 13018 ≤ n → n < 13268 → HasWitness n :=
  checkedRows_sound witness_sound witnesses13018Checked.down

private def witnesses13268Data : ℕ := 0x6080af051823902e01f307a002b00104eb03d007103f80f70d301fd04a812b02a83df030814f10780d703b039702c82f9044803110d064f06f81c115a002903981e704d8a1f022039101700eb0e506e9034009d0ce00b504700830f580a902189eb00402ab11b008b0218a2d06b01df09e80e50ed810301003e91c6000502f004f00381eb06d020b06c8d151c300e9116804f05901d508603350a300f106f827101880111ac80d3066824d0008e4b298003d126852f029012b070002f074003d04481190a18121365095504d00e90e6825905181390310005040008300c804304881a31f30065089018d00886cb004015705f012d02c0029032836b03f809705481f7019006508d816303e01d309e831705001e100a04f7079010f00f85890b7801d04a803d00c810f056817f01c01450a4024d055017f0280077092045702385450a6015d04a009d05a822706a01f702f00af051803b059800710e814b03103a700d011501a00f102f008304c003b10280a309581a302980dd11f000d023818514e012707b81c900403a10a900170d580c710281370e6803700e02ef02a803b0c1018705900b5065832908b022f042855301c0263

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses13268Checked : PLift
    (checkedRows (gcdWitness small large) 13268 witnesses13268Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses13268 : ∀ n, 13268 ≤ n → n < 13518 → HasWitness n :=
  checkedRows_sound witness_sound witnesses13268Checked.down

private def witnesses13518Data : ℕ := 0x8080e903a03dd185033d00502a512a004728b838500081a326b023909f81ed02d832916486f502f005502903170c280bf16b86df00680b902981b7024840f00500bf1f9014919103f701d05ed0cb899d0098025023018524a00d7047000701782ed05c8421479033d099852d12580e30b3037900284910a7814b164037f04302570bc80f1023006d00f82cf0b500490008007083026300a004708f04390a6020902e00cd0dd00a902f008902b01b700b002b017805f19602f900503c103f80831f0002900800f7065003b02c803b04701990c202e7058007301d06370ba80e91fc0353185019f00e817919d838f009803d01e883304000a300b009d02c000b047811b1ca005b0740305047806114d804f042835303a004f1af05d704581670bf801f0c800b502806530ec809b0e3009d0298473065849105307bd0010263052003113707b1122017f00881a307e806704001f106d009501d01ff01b806501f000b04e81e700e058d06d024705a81b713c035f06e80e30dd0301004044f046001d0fb004901a01e515d0031042833d0538083026801f07709fd04a02cf05c800702606df06580b901f00cd00b161b0b6832305500a1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses13518Checked : PLift
    (checkedRows (gcdWitness small large) 13518 witnesses13518Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses13518 : ∀ n, 13518 ≤ n → n < 13768 → HasWitness n :=
  checkedRows_sound witness_sound witnesses13518Checked.down

private def witnesses13768Data : ℕ := 0x29c819f0890199012862313001390d28ef50e5019d088013d0bf056501184310b9805928b80d3016018b035805902780a308c800b0c400ad081830701a01c1055001302a82d108b04bb16f00251a3004f00a01b50e380bf02c0055059054521583fd14c037300a032909e820b02f02a703f81fd07c004f053030114909c502383d903f8d3308203a117f801d08d818100f87850628329072824d0500275236816305183f703b08d505201d304b814b029009b09b8089030834909081df01f02f919882d102c025704481a505f006d08503cb00102990920109022047300a014b00b012102e007d014802507e84e100c80950aa81d501581c300e803b0ce829556a817b0b4888d029816308300bb08800470dc009502600e507404f11e4001d05602e303202450e3821d06f82bf00701314a983cb00981cf010025700b80f50b487b703100650e504a309e004f092028d05380610998793098807101c01af01d001901585e10a90047005001303c80bf23e003507a03c706f878b029818d09382ef04481c7001007703b0277009813d18e8577146017503e04af062832910b829b0f5060504480fd00e006d030829300280c5026003d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses13768Checked : PLift
    (checkedRows (gcdWitness small large) 13768 witnesses13768Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses13768 : ∀ n, 13768 ≤ n → n < 14018 → HasWitness n :=
  checkedRows_sound witness_sound witnesses13768Checked.down

private def witnesses14018Data : ℕ := 0x1af00b5014857538f80950ef00bb0470c1d14382530998f37042805902803df0ce004f001006506a00d9024804f00a00ef01484570998139026016706d00bf113016906503cb09a006500e01db0518ad302981971a4812d086000506700cd02188dd056816101c029f00381ff01603590a9004f024849f11802570ad80ad000824110a8545020812103201d50e480a107000e302901b702300a708c816702901cf02000d7152804f02c031319a00b30a900f106380f702903650868079227005b07407790628059030843904785b11de001d060812d0638095038846912680130ee06f502e013905c025f01d012b22d801703083490f3807d01481a30a101d50208293089810f04e85470818269010012b04a0313088065f04f015703b008b001019106881510c0828902682f305801f111183c102f80e90d486eb03f823b0008a550d603010a401570010455038818109802a705e038f02c82090a1025907703e321a01e508d830d00280e90ad82c50068337078832f0a1831714482bf05c834700880af01881bd07e80290b0806d1310fa904c04d303402570c684cf00c80710d78209030836700f86531b400c7068018701f0191

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses14018Checked : PLift
    (checkedRows (gcdWitness small large) 14018 witnesses14018Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses14018 : ∀ n, 14018 ≤ n → n < 14268 → HasWitness n :=
  checkedRows_sound witness_sound witnesses14018Checked.down

private def witnesses14268Data : ℕ := 0x882030d9012b105840f00a02ed0a600290ce0aff01e834d03d036704282dd0a003ad00b805f03c808b125816705e00431d6036705b028d00102ed03f803d01b83f501c05c9164007301d859f013016712e027d03f84eb013007d0d2807f00e00dd0ac00d10e185950010065014806d240814b01101b502e00592138067044039509e819906b00bb09984911d200bf0e0015d00b85c90b080a3021810f00103410b080e5128040f04a008901f096b1fd04e700b805903580b50ed8121026830b06d00fb05a819904a029300b802f05301690b5014f023813f03b0aab027815b391016701d02d100f8257289042d0de8445029003b0a901871610091092089905e003d10e804f06f833502c816701d00b502f001d15b820901a07c9008807d0fb80c700e002507b8353065806718502c500680dd1d80053023082901f0041070003700e0943004004d0670457176012d015829309a00e50f981b7039826308080e903c81f304e821b0ce8079050013f0860209023807f0dd01ff025020f03700b50218049065006b03882f902a814b05300bf1ac80fb03e016318a07c70a4825f01b83fd0f88af1017807314d8469045804d07d85b3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses14268Checked : PLift
    (checkedRows (gcdWitness small large) 14268 witnesses14268Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses14268 : ∀ n, 14268 ≤ n → n < 14518 → HasWitness n :=
  checkedRows_sound witness_sound witnesses14268Checked.down

private def witnesses14518Data : ℕ := 0x7c00050f38013030814902083ef05f02c508b01f709b813f1e681ff02201d30fa07db1d785a100080b32ef00290a280670260c1d128815506082e308b007700a015b09383850e4818b004023525401c30068083001003d128002b01880112a4028914001cf008001d12580e900801c90a400dd17e002f0ec0973130035f077800501584a506f80e90f5804709200b500700b909283dd0a7003d00f83dd01300af04d011504a05bd0fa01f706508ad0dd011908e02530ef03970b905f304600a914901bd0490149010008308903a30c686b9116811b017048701a04eb03b80d311180e5030822701d809103b006d01b80890a7808309985bf04a832f46d80830f98103035010d01f025904e801914381fd13f013901a05fb03b02c902500ef2018013042808911f81fd0b3003d008008905681b70b30373029085d0268169020042100b008304a812110e8bb90880281010001305900c708d822700d012b07e85fb02b02b723680bf09f80430010cd11300041072802502486b9002804f0c3824d02e011903882b113703a316a82a503d00dd04e80df018803b0f100b50cf800d01a016703880d7056039718705bd007001701b84e1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses14518Checked : PLift
    (checkedRows (gcdWitness small large) 14518 witnesses14518Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses14518 : ∀ n, 14518 ≤ n → n < 14768 → HasWitness n :=
  checkedRows_sound witness_sound witnesses14518Checked.down

private def witnesses14768Data : ℕ := 0x15c808501584192e7858109f81cf01c06b90a600dd06f804f11185ab02800d90e18673155810702200b30ab8289015829302e021b02181db026020f029817b0e000c101486e902e07fd06081030a4012b020813d0260397062855d12581331df01b70190149002810332d83a3018806b13f00d105480df05002bd173812703e019f0ce05bd0d602bd0b4850b0dd879703b814933501d502a8101080856f05602710448095026813f1310373001092308380d701102d70838a970a484490ad03d3097067d08c804f16e838501d00830b98121074002b00b05ed215822704a003d097012b08b0083062043f04c02bd04001b727b054707e8317038820f08d830108480bf05b04731b2025900682b70010079015825f030831704f025d065001905b061709a00a3012826b03884f104180d100b03c1059801d07a84e12cf07f3017826901a80dd03200f706e81eb0ec80eb02f072d00b03350d48031290004f04001730a4809b1e381a507781af0f880471580253014820306a022f00c826504b86051ca8599042851d111821b0388029065005b10301eb00e802f06504ff08900cb0d7851d2138409119809513484c30500061026800b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses14768Checked : PLift
    (checkedRows (gcdWitness small large) 14768 witnesses14768Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses14768 : ∀ n, 14768 ≤ n → n < 15018 → HasWitness n :=
  checkedRows_sound witness_sound witnesses14768Checked.down

private def witnesses15018Data : ℕ := 0x44843110781810c99189018831d05c83712b103c10080c6b062818506383cd01482390fb819f04280190158293061005b032035b0c700cb01f004f00683df03b01a300a003102183c1000805f00100a100e022301904cd071814f0ab846f03f801d004031d01a03970ce8bbd0f7009b11c01e102000a10e2010d065022900980411348257129811b02a800b0cb80af000818d001058d11c800706506af0b801a913780bb03f8d5d020019d05f825703084e709e00b904c00a90c2004301c0bf31120005026038b06800a116c001707d01f303f81f707d820f012814b02c81a3002825913e829500984b520200290ab8421056008308b00b5030800706f84d905680610c383010c700e900e809102903b50340059005801d07700c100800890c4001302784c3008005919180910c3804f0c4006500404eb1550709015852d02c80eb35a83fd01a815b0118293491018703d033b06a03a10a40175001033501a818b10583f10bc82f90a7824505f019900100e900d006b04a033d02c010d008849d00b03c104c010d27a0121048800d01700dd0bf80e904a0a0f01a005920500830170031008819d03b8127029049307a80650ee02d1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses15018Checked : PLift
    (checkedRows (gcdWitness small large) 15018 witnesses15018Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses15018 : ∀ n, 15018 ≤ n → n < 15268 → HasWitness n :=
  checkedRows_sound witness_sound witnesses15018Checked.down

private def witnesses15268Data : ℕ := 0x28d869d04b855f0920419028004904e82c5092009b005808916402d10938065049017b114801f0778581116810d03b018d0a2812b026804100e0499062847f028024702a824d004005304a8149015830d00a024b01486170e0003d05301c705680dd0ef007901f00dd0178091078825f03083a10a900a900f85d10ba817315a004320485b3028073d0a6017308a803d025007d017807702a831f00b0293035829f011001304000a102080e50ad014b0cb800b038807f3c384e102301d3094033508d807900980590658257042804903e81cd47c814b090819911981af02c818d19d004f0f3812506a00eb10a0e6b09c80a1049003d1a302710340abb01f008b04580670b984af1d2021d0458115164009514c801709983c104701cd007012107400c701d012b1d681ff08a81bd04a01010a6023b005054700b0227182800d01a01b703b029308b008900503010c4019d133002501a0103009815507901c1003802b015815b02680830c802b305c8407071817505a80a9042800b07c001f0d281d502900d701d809500681f3057810d01c027701580b5023806b017812b006804f02b0a0108381c3009833d254013710d818d0530103

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses15268Checked : PLift
    (checkedRows (gcdWitness small large) 15268 witnesses15268Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses15268 : ∀ n, 15268 ≤ n → n < 15518 → HasWitness n :=
  checkedRows_sound witness_sound witnesses15268Checked.down

private def witnesses15518Data : ℕ := 0x4a001f0a1807d1af82570a4007f029013704f008310d01db01001af1330011050003d01305b700581f9209008b01102a518b804f1d7803700802a509a0239020016f05386350bf81810f2004f07e8293013004300506df0bf034d0ef8103213856509f82930f8801300684ab0c383a1290805901d003d116049d04483a710580bb00e029f01d82f911d835b015836b05e007728b84ed01b854501481cd0ab82a103582b113c000b25e822f04b899b0f880c103b006d0a40047020801713b805b02982c904f013f02181b700700e30a7821b1ee0073035858103d00b520f01cf0028623074857d0c380a913a011903e803503987ed00e0281056836506f8097057840705500f106f852300101a31f781691aa85e900a012b260834d0a701f314d844303400130d58955022008307f01090c2012103202ed05c80951fd045101482570b8003b25280bb03d00a101a80ad03e0421008821b038816105600e50a4020903880772cc04ed01a829f01f00bf042805505081a30a601a3042808502f80ef0cb80bf01e80e504f01c1034003d0c8030d071808300b80c508300131c481491540211033851701d03a1254809504a010f00a0083

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses15518Checked : PLift
    (checkedRows (gcdWitness small large) 15518 witnesses15518Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses15518 : ∀ n, 15518 ≤ n → n < 15768 → HasWitness n :=
  checkedRows_sound witness_sound witnesses15518Checked.down

private def witnesses15768Data : ℕ := 0x56822709e80eb0a10dc902c056f1a200b501a02ad07004af19600591aa81ed0008047017803d11602a706a00950190079026034909280650f8804d01580f105c01d308084a500e00730fb83113a3001317605e900581912a4002906f806101a8cb30f401cd0ff884703b01c70448113120809707d00170b982c51b200f104401fd0970083138825f00882f90b500370818121105827507c008900b02d104a00d7062804312f88ad04d003502380d1074045100e01f104482450cf82c500109a7260803510d038b1460227217004702908ad00100f516600d10c989d902a80fb0cb80b53d580d300981e50568a0116282890fc84cd2db802b0d581e706f82f90028167005030d102874f005806d07e8301031003505b038500b02a106384af224812138908050d2825710f0281081804f0b004bb0bf812d12f8865021801700d001907e80f1038851b00d00f10fb003700f804d13f003b018821102b067102e004103c80bb04704cd109014b03f8883053806506a006100e03850d4003b06b878b030810f015840d23686370c2000d01c0509080843d00801330470167059806d08c056500b8233031010306800c700500cb0538673

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses15768Checked : PLift
    (checkedRows (gcdWitness small large) 15768 witnesses15768Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses15768 : ∀ n, 15768 ≤ n → n < 16018 → HasWitness n :=
  checkedRows_sound witness_sound witnesses15768Checked.down

private def witnesses16018Data : ℕ := 0x35836703f82a7060812b028009701a00e50268bb1031006b0ce030d0ef828d00100c70590565001051b05b0185018817b05381a309280670200073185008311080bb074036702e01af00100910770a8102002630aa8103099810f02684d30628095042806d12e80a1035801706b00190ce031709d0035128058309e832f03880910dd00a901b80bf028047302c01a502682030d3036714180310d4815504480370a40a0900e0293059808301a0169031036b14681d50e4814b05c0125233803b03f801f0070101029810322a004f09880bf088017503b00550d102b107f00dd210841b01780cb01481152a9822f08c02090f8831f0770427030845b06a02bd0fe006d03204431f78065053006d040096b1c1828900805650130c1d0d1814913e817b08c011908202591fd007902b01df2bd81690cf8007023067d04480b503f88d1053812b15b84ff0260775024812501c004330f8457043024b08c810f07e819f07f02a50da812b07e81690bc03cb33d000b089018d0e781490f2818d0b1822f03884a9034002f10a0187019001702f82d105d8187052021b3cb82570b180a3001027534481a90fb018d038829f013018712980d3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses16018Checked : PLift
    (checkedRows (gcdWitness small large) 16018 witnesses16018Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses16018 : ∀ n, 16018 ≤ n → n < 16268 → HasWitness n :=
  checkedRows_sound witness_sound witnesses16018Checked.down

private def witnesses16268Data : ℕ := 0xb018107483e300883350ba80a305081df10a82bf0e0009d05e03dd06402510fc812106a00170538151006819902300530a780d301580af06f80f518e80d107e814b062005919d810f0ce00d90b80335064000b177808b05e08a506d001d3800b1706883cb0b500950ec00cd01d83dd029863705f01e101f02f905e01e504b8103040059f0f4012d021821d03f80d707c005f09981b7089858103a014b38f01db08a842b05b010d039865b03980952ae806706b00070568029064009d026017b03f814f03280d702903a3004044917c824515c80fd0a3025718e80b50f2096d0d2803b04482d110e8a0f137060500a0043030830d038816d02b002f012839700b805308503df102823b02004a3100005b16584c302a830b071827103506e50bf000b0a780df195846907404b503283ef17601d506580dd076009504e862502386fb08b001d02f038500d064109702bf03081450658371029815505d853b08d8035049036b056013f00980fb0e680b303f849309c803b0a9004f0c200b511f859f01000790ab82d70e0038f0a0017f087808b0178317092804105d87390478083062817b02c045701000f52f203971e507ab0410461

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses16268Checked : PLift
    (checkedRows (gcdWitness small large) 16268 witnesses16268Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses16268 : ∀ n, 16268 ≤ n → n < 16518 → HasWitness n :=
  checkedRows_sound witness_sound witnesses16268Checked.down

private def witnesses16518Data : ℕ := 0x35809b0f1014f0c201d5020035f041810d03f81b102f051b0f400d3072808509e808302e02db04b809100102810d180070aa041b01783e901602ed030812100400e9049067312080fd05c010d0748095005013301c05c90bc807300804ab16c04af1a6813d005004f00882511d8001915c80b5055012506280ef09500cd01005e1326828900e03c703a02f9035845103b080b03f8d670e5000d00502c502182330ca01010ba845710d83f5082051d1c583a301e84eb088014b0d4011b003810d100000505d80a901a80b30fe811f17003f1088035305e0073111817b041015504c01b717601810110581056803d01d02bf0c5804726f821504a02d706a154102f8047069835b00881cd23380250950c9d00a03cb01481f3060812704582b1001015506f824d001047315a01130ef0181026800b149804703c84e103b007102c86dd19401b705004eb05b01c31418265014867126803f1282805b001064104000f508002110158059020805909e042d0448005017806b0ba81030ce867108801b70ba8067004006b0ec84e102f007902602390c7018b033807301287c7106007914782a706d052117b00a7021801f00a031d03d029f

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses16518Checked : PLift
    (checkedRows (gcdWitness small large) 16518 witnesses16518Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses16518 : ∀ n, 16518 ≤ n → n < 16768 → HasWitness n :=
  checkedRows_sound witness_sound witnesses16518Checked.down

private def witnesses16768Data : ℕ := 0x4f013105a8415065081505e00170a28b9b031036b0c281b715503d3005012b0a7801f12803d901881a92a7031f093802b01b851500b814b00b01f3038860500a00350dd02a70388a4901d802f083010300a064d00d0083077020b05902932110209039804300505bd083801706f816f0068275011804700802c50f101bb02b04510e0009708900710b6818510d01e1059816708b021b072828901f05f906581a902004b703080830b801f10da022f0a4007d068806b05600b503881df16301030b300d301e83ef1f782d103b024d053001d00b82ab04e803110a8059020820f38183010f883ad03a006d0a409bb0388071101831701d021d04e82c30b8014b060803d0a7815518282f9020009d09e83fb02980530578b1709c845b074806d0b3001308e00e31e8816703380af00e025d290803b02a818705c85ab08080bf05d810305d8263043003512f803d0308155034004d0b3003d09d00a140600d103080cd01a818b02980b518800d3098856f14b001906383d906581eb011808303f8199015826f11684c306803df01b859911f841b099821d01881a30cb810f12e007901700fb11980370368241092810d020801103504ff

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses16768Checked : PLift
    (checkedRows (gcdWitness small large) 16768 witnesses16768Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses16768 : ∀ n, 16768 ≤ n → n < 17018 → HasWitness n :=
  checkedRows_sound witness_sound witnesses16768Checked.down

private def witnesses17018Data : ℕ := 0x4e8037026805f152803b00e00df09100ef19d80e906b053b00b83a1068815b0ed81991238083023806b02c028903400bf0c880b508a83370e0014f047806d02f02290de8e75100000507287c300404cd02980d308481690c7043d01a80cd1898397016019d0eb0353015820b0490221182824505f00bb0b504cd23681cd09e049903880ef020800d0ff8f1f0b303d707c0005068012d031003b11b028915803af008821b06a02ef09080d902903e91ff009706089c105381cd0ce801d08a81d5030829f0bc818132902e3009841900a015d3ec003d04486e90d301490b182fb046020903100d70e4815d0538f59019006505f063704c027b0c7024d0998295016002f0a6012b37101cf01301fd05e00d101881750178095013032f04401810dd012b0b801790ad005b021823305e032f065008b019016713606a30590c3d086807d16c00650158187046037103d0083068056b00b02630568139084829501f000b02983d10e78bf506b828705384430a4003d03b82b7026804700e042d06980a108382bf065008b00104730c7022d029024d0ba82f302681c702c066702c00170208031065044502183a72e7800b00e00a902e0119

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses17018Checked : PLift
    (checkedRows (gcdWitness small large) 17018 witnesses17018Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses17018 : ∀ n, 17018 ≤ n → n < 17268 → HasWitness n :=
  checkedRows_sound witness_sound witnesses17018Checked.down

private def witnesses17268Data : ℕ := 0x196016d09a006d04e84cf05200590e9801f086007903280d13238079048822302a81af13f002b03c830701d0059182810105780f101781a9031008b1c8859505680650208103047059b0ad818501f004f15b03df15e03bf0dd80170c50007006812b0c7000b06500a901d01f70ac001d05d83f100a00590280259056002b00980050ce84e11c885c50b1812b074822901d027100406d700a00790ad05591a7819d09e82c5015803d05200a1010004f06f81750e0807d05382890ef000705f00bf013011303f82e3004023903400b30a10013001062f0a600610b7818706d01c1287816701a050501881d3035824d108800d00a03dd01a82bd01e825f09702f903b821b01e82b308a84310b50037245006d06b80170da801308d812d01d061701f022709803010d280bf100002b0c5008b0130173188803111303970da80830f880732a2045700e805908c812b23904ab000812b18e80e5131009d03f8527202000504d01630838725028004d00806c11148113014806106f8013029819702b02ed07b801907a0e69053809706f80c702d83a1047873d0dd027105e000b022000d02601c30a1811312401db074004f043004711e03b5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses17268Checked : PLift
    (checkedRows (gcdWitness small large) 17268 witnesses17268Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses17268 : ∀ n, 17268 ≤ n → n < 17518 → HasWitness n :=
  checkedRows_sound witness_sound witnesses17268Checked.down

private def witnesses17518Data : ℕ := 0xce8161006825f030812b03880c5008003105e078b10601312e5826b015805909b81a504a012d0098005035808b018817b07603ad029818701a00af03f81df064000703980b504f01e50d901bd01d09cd03e80a1175010d01285a101102990ce804f006810f00a008309700cb015805500b8443034010302300f106f81611a3806108302c502200470370031030817502683e305b00c700e011508501c10a900490ad06c10478707077803b08c099d0a8878b0da80af07e81d5037012b0aa8c7717304bd014831d097010d03981b700280650b5019d01d02ad04a0095007001106508fb042809b02b025301a00310488323044801f03f8139059003b20681f307d00a901b817308081a9021824104a01c105e0125057814b1eb00b906d03470b0030103b00e304d808301d00c101d83bf0ad81c105c000706a01cd4c783670290235077018503401d302181030a4005300880d9060830d022000b01900590ab8067029001104480130398af9049074f0bc800d04a016f00b016708381cf03201ff0a6001706d00f704a04690c8030505800d305d83eb025005912880e5011017500582810e501cd065059b02e006506d011f00f805b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses17518Checked : PLift
    (checkedRows (gcdWitness small large) 17518 witnesses17518Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses17518 : ∀ n, 17518 ≤ n → n < 17768 → HasWitness n :=
  checkedRows_sound witness_sound witnesses17518Checked.down

private def witnesses17768Data : ℕ := 0x16b801f0bd821b1a501d501b83a906b80d129c810700e036100e02090d1820b01e803106d00d70b5010321b021114c00172650289030837302e03e308b014b10101330620b9915d0047011011500401fd1018013066804f0400c5316f05590338277015812501900bf119007900104cd0a605ef0ab8025005809516900df08f042d00b867d04f001301a07db07e82030aa803700694ef00e002f0c881ff01d03cd0db86170c70509108821d044003b01f004701280d909c80d10fa001304b89070100047047830706501ff16284d917c81d510d000d02d81670ce828905001b70c1005904000e901281d518e8407082000b10282c500102f9043005528b8385016002912e81f30e78733060815b0d6006d018803d2a080470448041044002504f00bf11f80f723d845705e043106a0055092003d016060b01481c303383eb053800506d00d304a004f04e808308081bb04a05b902904cd0af018700f80a901580410ef80f700685470070011046009511481c304e809b02e003d02c048706a012b02e005f07282410400aa9043003102a8031038828d001008b17301c3019002f02807750308493010010d3b200830980013011a453

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses17768Checked : PLift
    (checkedRows (gcdWitness small large) 17768 witnesses17768Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses17768 : ∀ n, 17768 ≤ n → n < 18018 → HasWitness n :=
  checkedRows_sound witness_sound witnesses17768Checked.down

private def witnesses18018Data : ℕ := 0x65036b04480410ce049301b806b0d789c520c028f06f871900880950cf842d01a0a9705682270d2807f04483cb007011512c84c3010004710780cd12084a50188197196001d04e820b04e843d24581030bd818d07d01a30ad80970bd80f700b0761289002b203024d18202271240239132873900703050dc025713700af04180b90ec83dd06f849f09982571300073071016306508c9002807f0080385030815501483c7102810f00a0521161822705d81c301f01490da81fd084804900a166d13000ad0ce01b70040173082008b01a0d51029848b07601212f48727038810118880a90ec0037026030b100021126c0259014960716c013903f819f0d105c907480bf10a00a90218209023825717604ff05683650a60469231849f010001112883a1165835b03502451c600bf0db825f0130155070010706501c3042818b14e014905d824d02a8257049003126d82a103a0197001003b1f4020b0128149056825303c804f10d046104d8215083038503100ad001018d029012d00280770ad81eb425012700080a703d004f0f200e500508031f780af045819907e8191028005900380e505180b9167807d012814b006806b08f8137

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses18018Checked : PLift
    (checkedRows (gcdWitness small large) 18018 witnesses18018Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses18018 : ∀ n, 18018 ≤ n → n < 18268 → HasWitness n :=
  checkedRows_sound witness_sound witnesses18018Checked.down

private def witnesses18268Data : ℕ := 0xad80b900980e500105e71b5823b26488e90b08443004005907e84e10aa051507d85290ab81a502980c505e00d10c2003106b860500884bb044012102184f702f81670b783df13e82150ec80bb0bf074507f02e104481af03080490d585931a0814b02c00d303f8581022019d01103610d8805915b83a9074010f2a2004700e8149102812d0188be1026819105901db01d800509700790ed81b70a2849d13480fd05a845d035845525f024d1b08aab0b502990bb010900b02c504d029f020825911c008500b881b0220079101042702300ef1000247000814516480bf211001708301e119882b708f855f0dd001f00e867101483a30b001ed00e82c32ab844b0fe039701487f7013018702f004f0010b2102c8007012856501580b901a856910a05d102a801d058035b0c681630c6813d0cb806d04a021101c012b01f02dd04b800701004af03401010de8cf70d600710a90073074031f04a016708982cf2d382fb023859f1dc825712b03df0308149010014b01e818d0ef074f09880fd0c3835b03d090b01d8395074037901300a705f81f306506af011009b0fb80dd0d701b70190a7901302ab0f0804f26b07a9011803b035003d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses18268Checked : PLift
    (checkedRows (gcdWitness small large) 18268 witnesses18268Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses18268 : ∀ n, 18268 ≤ n → n < 18518 → HasWitness n :=
  checkedRows_sound witness_sound witnesses18268Checked.down

private def witnesses18518Data : ℕ := 0x5d8a8d02600d7121075704d004f00b01cd130014b02780910fb84bb05c84130b905dd0bc80ad06d01d32c00103244015508c808315805cb04b82b108381af081845707894090b8007111d818d02202f90af028d11303d3015814f13484f1222812102502f9028038507e80a3009809b130012b04581a500813730358107090809109a00650fb818508301870dd017f03880110b002c501d080f073059f10d004903b85930a183172ff006702a844308080e902007b704f074310303130ce01f306a025106a01ab08d803d14181eb014833d065030d026016d1d2021d1388169083009515a01bd04580eb026822700a017b1c5844b0c7035f02c80770dd006d00c82750a780fb173014b094023908381fd05c00a3041074f137830509800910a600bf0cd003d0668973088002905086e5068008b0190599028038507b805506b004d03580950c8017b04881191a5032f0ad01f301a8527020825101b89eb0ce02ab0d180d10128685082024511381a528b84ab00f84f102980dd14780fd08482f90a6009b03e039711e00fb0dc036d003869103082b70c4013103f80d3002862f04d8353141838501c008904f086f0f200430bc82ed

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses18518Checked : PLift
    (checkedRows (gcdWitness small large) 18518 witnesses18518Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses18518 : ∀ n, 18518 ≤ n → n < 18768 → HasWitness n :=
  checkedRows_sound witness_sound witnesses18518Checked.down

private def witnesses18768Data : ℕ := 0x7481252b900430a8856501102090b680e502c00af008004d40f008b0e784e1000818506d009103b017b0ba80ef0b3818d03c83850fb842506d018503b001304580ef06a01031280259068023901a826301881e700f8e751ff012d04b809d00b85bd03701390038637056032300100bb03f8349022007706b81f312b03f706b04cd0c7021102301e700a00471c6001702483070bc8581007029b04b89eb088025d0268091150844b0638059014814b02186bb022023924d013f063806700282bd10a800b1d300af06084f7002817501b84cf37600f501a8241056007907a00770a7813f03f81750c2012b08802932390025041802904c017505a87d51148155106002f2ae0dc90950335035800509c810301887eb019024d0590a8d052023906d0149020003d029021b0448215029024101a047f1f603971af04570a1828109b818d00682c50a0017f07301b706f802b06100590e202570d8860d03081c103101090a5824106589a701a8241099863709c81130bc80c50a881f309b028704600ef150820b067011f0298079156816f100038f12d003503084d507e892305980e90440493044800b0a481270a406550980095019010d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses18768Checked : PLift
    (checkedRows (gcdWitness small large) 18768 witnesses18768Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses18768 : ∀ n, 18768 ≤ n → n < 19018 → HasWitness n :=
  checkedRows_sound witness_sound witnesses18768Checked.down

private def witnesses19018Data : ℕ := 0x31009b24200370010347007011907b840f00400dd02b003703b068500403fb09401372900085022001d0bc81690a280a302e0911010004909e015d07707071bd046304b815d03380f50c101e514180f1124003500a00d33260307078841f1af8ae702c070f010012b05e000d0ab860d0b512a10868013053003d0bf052d169012703f87750a781011018a1304a00eb04587bb0bc829506b016905f00d103d00d300801270bf000b16f010300b023b05b005312d00910ec00e504f02db02384d90b78f3d03b074308b00b506f808b00f830b12881cf011018d08b012b0d6006d06200f1065812502681511b681b7002822d00d00b50b3049302c00b906d00b301880250f581670a901cd011003106f81eb04d806105a840f0a1015500e807f25e82ef15881bb010011902c001900f807d33d02bd13d013905600dd41b02f313e849903b01c1020834706508650ec819112100eb0650637057816705800473ce0283004099b13c0149066839700501a304f0445029004303b01a304300250320349001059902980250ce02c5002802900a019904a00fd0bd841f1288167090832b065016731781e107e84ab03d0293004021b00c81b7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses19018Checked : PLift
    (checkedRows (gcdWitness small large) 19018 witnesses19018Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses19018 : ∀ n, 19018 ≤ n → n < 19268 → HasWitness n :=
  checkedRows_sound witness_sound witnesses19018Checked.down

private def witnesses19268Data : ℕ := 0x10d002b09283fb09a024d07d027d0a307bb03d00410d5809d01a829f09d00fb05a841b074059902982531a0003108c03b901000fb213816308c84f1263803b03200f700f86351cd81e501e8313015894103880e500804e107e8afd013004f0fe021105f0011019010d00383d901d00950da805932484a501b8095452802b03f84e117381671b2812b092008b03d041302381c909981a500a023308c808301d008505c024b33282b300c851100b08b731480b504280f714603a102980250e481ff06282bd0040061489826b0310a5b023801308d830d00986e90bc809700e01cf0238623071805b04b805508d812b00a005b0008559029004708800590b7803109b0011082008b01d03c102384d308b00bf059003d0848083010004102f00bb1208077155801f06500d300e085d11b04af0bf00f106080bf1ae04932e28d3f029829301f015d00e028908000a119d807905a803703f830b0a780470ce040f0bc807113300e307e82a7022022701f00c7021836706f80051d501c1197027d00880d101301e1062005508f835310300b5264834903f831101d80190860103007001d01780972f184cf07a02ed173806509b018703581a3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses19268Checked : PLift
    (checkedRows (gcdWitness small large) 19268 witnesses19268Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses19268 : ∀ n, 19268 ≤ n → n < 19518 → HasWitness n :=
  checkedRows_sound witness_sound witnesses19268Checked.down

private def witnesses19518Data : ℕ := 0x1f014f013009b09c812102c020f0fa04a51670631018818b1d983df09801d505502f900101af024840308384f7278803d15e00c701a0173040007700b049305c8251010068502901f916f017907180792d5001f00a00950bf81b109f819f003819109a02db01b8667015819100b80d71d7810f04102db00a03a117a814500e012b14b003b05f0067047070708804071c400cd01301cd05c815502900130158053220015d213824d05e00bf01f02b1149003d12e060b07900b3141820b02e077f02e00290ae82e310a81c100e806502a803d14e017f049010d137001304583cb05802c501d045700b81c7056814b0a401e7056096b0d601251a781f309c81c1013032b1d4814b0448047025007d0d880e502982e105804af383058301782cf3418137141806104902b118e83230bf034f0dd82810280175035006d06580170cb865b1e381b7027806513d81ff09206430a8801d15581c10ed819903d0083116801f07e84a51f2814901901af0800013047079707c01030ef01ff006803506a03a308a80a302603dd14e03fd02300bb0358227121000508f0523038810d002801d0ed85d10b788a503880b91f581d508981bb005803b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses19518Checked : PLift
    (checkedRows (gcdWitness small large) 19518 witnesses19518Data 250 = true) := ⟨by decide +kernel⟩

private theorem witnesses19518 : ∀ n, 19518 ≤ n → n < 19768 → HasWitness n :=
  checkedRows_sound witness_sound witnesses19518Checked.down

private def witnesses19768Data : ℕ := 0x5ed06703fd0068481020006b1168581324820500085db1af8073101084d05d808300a007f01e8595074012510f03891b98103090808301781910bf0463025016705b030d08900a300d009519d8029009802506f81850e080c506507ed01a02f906a002f02901030098083014853b00e01cf00702750c400a90b1801f00500770808079000846f13282630ce80c1137044b00b032f00e804f15503c105000ef01c004724f804902e041f004005909b007903d04d93d000e9020001309a015503882270d281b700101070da829b4868781081833b02e0211210812d038811f07900fb063827d00b067116c0035111821102984af02200cb02a85ef0650515088006d141821d02a801111b01190e784ed00400b30c701a306b023b044837108f832303f82892638ce301a811f0a280790a401130df00410e7857702a84df3e680e5006819f02c830b583001d0c8024d008078b143808305600bb0c700a111200fb07588dd03082f300e85c311c01031718065053804f0ef00af03400ef0e983c1494024100f84d952c00d703f822f01d012b065814b0530367

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def witnesses19768Checked : PLift
    (checkedRows (gcdWitness small large) 19768 witnesses19768Data 233 = true) := ⟨by decide +kernel⟩

private theorem witnesses19768 : ∀ n, 19768 ≤ n → n < 20001 → HasWitness n :=
  checkedRows_sound witness_sound witnesses19768Checked.down

theorem complete : ∀ n, 4518 ≤ n → n < 20001 → HasWitness n :=
  (joinWitnesses (joinWitnesses (joinWitnesses (joinWitnesses (joinWitnesses witnesses4518 (joinWitnesses witnesses4768 witnesses5018)) (joinWitnesses (joinWitnesses witnesses5268 witnesses5518) (joinWitnesses witnesses5768 witnesses6018))) (joinWitnesses (joinWitnesses (joinWitnesses witnesses6268 witnesses6518) (joinWitnesses witnesses6768 witnesses7018)) (joinWitnesses (joinWitnesses witnesses7268 witnesses7518) (joinWitnesses witnesses7768 witnesses8018)))) (joinWitnesses (joinWitnesses (joinWitnesses (joinWitnesses witnesses8268 witnesses8518) (joinWitnesses witnesses8768 witnesses9018)) (joinWitnesses (joinWitnesses witnesses9268 witnesses9518) (joinWitnesses witnesses9768 witnesses10018))) (joinWitnesses (joinWitnesses (joinWitnesses witnesses10268 witnesses10518) (joinWitnesses witnesses10768 witnesses11018)) (joinWitnesses (joinWitnesses witnesses11268 witnesses11518) (joinWitnesses witnesses11768 witnesses12018))))) (joinWitnesses (joinWitnesses (joinWitnesses (joinWitnesses witnesses12268 (joinWitnesses witnesses12518 witnesses12768)) (joinWitnesses (joinWitnesses witnesses13018 witnesses13268) (joinWitnesses witnesses13518 witnesses13768))) (joinWitnesses (joinWitnesses (joinWitnesses witnesses14018 witnesses14268) (joinWitnesses witnesses14518 witnesses14768)) (joinWitnesses (joinWitnesses witnesses15018 witnesses15268) (joinWitnesses witnesses15518 witnesses15768)))) (joinWitnesses (joinWitnesses (joinWitnesses (joinWitnesses witnesses16018 witnesses16268) (joinWitnesses witnesses16518 witnesses16768)) (joinWitnesses (joinWitnesses witnesses17018 witnesses17268) (joinWitnesses witnesses17518 witnesses17768))) (joinWitnesses (joinWitnesses (joinWitnesses witnesses18018 witnesses18268) (joinWitnesses witnesses18518 witnesses18768)) (joinWitnesses (joinWitnesses witnesses19018 witnesses19268) (joinWitnesses witnesses19518 witnesses19768))))))

end OMA.QuadraticPrimePairs

theorem OMA.solution : OMA.R_OeisA219023_conjecture_4_R1.H1 := by
  intro n hlo hhi
  exact OMA.QuadraticPrimePairs.complete n (by omega) (by omega)