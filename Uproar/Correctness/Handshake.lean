/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Uproar.HandshakeState
import Uproar.Transport
import Uproar.Correctness.Symmetric
import Uproar.Correctness.Keys

/-! # Honest parties agree

`Link` relates the party about to write a message to the party about to read it: the same
symmetric state, the same PSKs, correct knowledge of each other's keys, every key the validator's
walk says was sent actually delivered, and honest keys and reliable randomness on both sides.
Writing a token and reading it back preserves `Link`, so does a whole message, and the reader
recovers the payload. The results: `initialize_synced`, `Synced.initiator_writes`,
`Synced.responder_writes` and `Synced.finish`. -/

namespace Uproar

open Cryptlib.Util.Bytes (ofVector size_ofVector)

namespace Protocol

variable (P : Protocol)

def EHonest (kp : KeyPair) : Prop :=
  match P.exchange with
  | .dh d => d.Honest kp
  | .kem e _ => e.Honest kp

def SHonest (kp : KeyPair) : Prop :=
  match P.exchange with
  | .dh d => d.Honest kp
  | .kem _ s => s.Honest kp

/-- Every seed a party may draw gives both KEMs a `Reliable` state. -/
def Reliable (seeds : Nat → Vector UInt8 32) : Prop :=
  match P.exchange with
  | .dh _ => True
  | .kem e s => ∀ i, e.kem.Reliable (e.kem.stateFromSeed (seeds i)) ∧
      s.kem.Reliable (s.kem.stateFromSeed (seeds i))

end Protocol

structure PartyOk (P : Protocol) (st : HandshakeState) : Prop where
  e : ∀ kp, st.e = some kp → P.EHonest kp
  s : ∀ kp, st.s = some kp → P.SHonest kp
  seeds : P.Reliable st.seeds

/-- `y`'s knowledge of `x`'s keys is correct, and `y` holds every key `x` has sent according to
`v`, `x`'s view in the validator's walk. -/
structure Knows (x y : HandshakeState) (v : PartyView) : Prop where
  re : ∀ k, y.re = some k → ∃ kp, x.e = some kp ∧ kp.pub = k
  rs : ∀ k, y.rs = some k → ∃ kp, x.s = some kp ∧ kp.pub = k
  sentE : v.sentE = true → ∃ kp, x.e = some kp ∧ y.re = some kp.pub
  sentS : v.sentS = true → ∃ kp, x.s = some kp ∧ y.rs = some kp.pub

/-- The writer `a` and the reader `b`, with their views `va` and `vb` in the walk. -/
structure Link (P : Protocol) (va vb : PartyView) (a b : HandshakeState) : Prop where
  ss : a.ss = b.ss
  psks : a.psks = b.psks
  idx : a.msgIndex = b.msgIndex
  roles : b.initiator = !a.initiator
  ka : Knows a b va
  kb : Knows b a vb
  oka : PartyOk P a
  okb : PartyOk P b

theorem Link.symm {P : Protocol} {va vb : PartyView} {a b : HandshakeState}
    (h : Link P va vb a b) : Link P vb va b a :=
  ⟨h.ss.symm, h.psks.symm, h.idx.symm, by rw [h.roles]; simp, h.kb, h.ka, h.okb, h.oka⟩

namespace HandshakeState

variable (P : Protocol)

theorem take_append (a b : ByteArray) : take (a ++ b) a.size = .ok (a, b) := by
  unfold take
  rw [if_neg (by rw [ByteArray.size_append]; omega)]
  congr
  · exact Cryptlib.Util.Bytes.extract_append_left a b
  · have h := Cryptlib.Util.Bytes.extract_append_right a b
    rw [← ByteArray.size_append] at h
    exact h

theorem bind_ok {ε α β} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := Except.bind_eq_ok

theorem ePubLen_honest {P : Protocol} {kp : KeyPair} (h : P.EHonest kp) :
    kp.pub.size = ePubLen P := by
  unfold Protocol.EHonest at h
  unfold ePubLen
  split at h <;> rename_i heq <;> rw [heq]
  · exact DH.size_pub _ h
  · exact KEMFn.size_pub _ h

theorem sPubLen_honest {P : Protocol} {kp : KeyPair} (h : P.SHonest kp) :
    kp.pub.size = sPubLen P := by
  unfold Protocol.SHonest at h
  unfold sPubLen
  split at h <;> rename_i heq <;> rw [heq]
  · exact DH.size_pub _ h
  · exact KEMFn.size_pub _ h

/-- `generateE` yields an honest key pair, and touches nothing but the draw counter. -/
theorem generateE_spec {st st' : HandshakeState} {kp : KeyPair} (hok : PartyOk P st)
    (h : generateE P st = .ok (kp, st')) : P.EHonest kp ∧ (st' = st ∨ st' = st.drawn) := by
  unfold generateE at h
  split at h
  · rename_i kp' he
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hok.e _ he, .inl rfl⟩
  · unfold Protocol.EHonest
    split at h <;> rename_i heq <;> rw [heq]
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨DH.ofSeed_honest _ _, .inr rfl⟩
    · obtain ⟨kp', hs, h⟩ := Except.map_eq_ok.mp h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨KEMFn.ofSeed_honest _ hs, .inr rfl⟩

end HandshakeState

/-- A party's view after it sends `t`, as far as `Knows` is concerned. -/
def PartyView.after (v : PartyView) (t : Token) : PartyView :=
  { v with sentE := v.sentE || t == .e, sentS := v.sentS || t == .s }

theorem Knows.congr {x y x' y' : HandshakeState} {v : PartyView} (h : Knows x y v)
    (he : x'.e = x.e) (hs : x'.s = x.s) (hre : y'.re = y.re) (hrs : y'.rs = y.rs) :
    Knows x' y' v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk; rw [hre] at hk; rw [he]; exact h1 k hk
  · intro k hk; rw [hrs] at hk; rw [hs]; exact h2 k hk
  · intro hv; rw [he, hre]; exact h3 hv
  · intro hv; rw [hs, hrs]; exact h4 hv

theorem PartyOk.congr {P : Protocol} {x x' : HandshakeState} (h : PartyOk P x)
    (he : x'.e = x.e) (hs : x'.s = x.s) (hseeds : x'.seeds = x.seeds) : PartyOk P x' :=
  ⟨by rw [he]; exact h.e, by rw [hs]; exact h.s, by rw [hseeds]; exact h.seeds⟩

namespace Link

variable {P : Protocol} {va vb : PartyView} {a b : HandshakeState}

/-- Both sides apply the same update to their symmetric state. -/
theorem withSS (hl : Link P va vb a b) (f : SymmetricState → SymmetricState) :
    Link P va vb { a with ss := f a.ss } { b with ss := f b.ss } :=
  ⟨by simp [hl.ss], hl.psks, hl.idx, hl.roles, hl.ka.congr rfl rfl rfl rfl,
   hl.kb.congr rfl rfl rfl rfl, hl.oka.congr rfl rfl rfl, hl.okb.congr rfl rfl rfl⟩

theorem drawn (hl : Link P va vb a b) : Link P va vb a.drawn b :=
  ⟨hl.ss, hl.psks, hl.idx, hl.roles, hl.ka.congr rfl rfl rfl rfl,
   hl.kb.congr rfl rfl rfl rfl, hl.oka.congr rfl rfl rfl, hl.okb⟩

/-- The writer sends its ephemeral public key and the reader records it. -/
theorem sendE (hl : Link P va vb a b) {kp : KeyPair} (hkp : P.EHonest kp) :
    Link P (va.after .e) vb { a with e := some kp } { b with re := some kp.pub } := by
  refine ⟨hl.ss, hl.psks, hl.idx, hl.roles, ⟨?_, ?_, ?_, ?_⟩, hl.kb.congr rfl rfl rfl rfl,
    ⟨?_, hl.oka.s, hl.oka.seeds⟩, hl.okb.congr rfl rfl rfl⟩
  · intro k hk; simp only [Option.some.injEq] at hk; exact ⟨kp, rfl, hk⟩
  · exact hl.ka.rs
  · intro _; exact ⟨kp, rfl, rfl⟩
  · intro hv; exact hl.ka.sentS (by simpa [PartyView.after] using hv)
  · intro kp' h; simp only [Option.some.injEq] at h; exact h ▸ hkp

/-- The writer sends its static public key and the reader records it. -/
theorem sendS (hl : Link P va vb a b) {kp : KeyPair} (ha : a.s = some kp) :
    Link P (va.after .s) vb a { b with rs := some kp.pub } := by
  refine ⟨hl.ss, hl.psks, hl.idx, hl.roles, ⟨?_, ?_, ?_, ?_⟩, hl.kb.congr rfl rfl rfl rfl,
    hl.oka, hl.okb.congr rfl rfl rfl⟩
  · exact hl.ka.re
  · intro k hk; simp only [Option.some.injEq] at hk; exact ⟨kp, ha, hk⟩
  · intro hv; exact hl.ka.sentE (by simpa [PartyView.after] using hv)
  · intro _; exact ⟨kp, ha, rfl⟩

theorem popPsk (hl : Link P va vb a b) (ps : List ByteArray) :
    Link P va vb { a with psks := ps } { b with psks := ps } :=
  ⟨hl.ss, rfl, hl.idx, hl.roles, hl.ka.congr rfl rfl rfl rfl, hl.kb.congr rfl rfl rfl rfl,
   hl.oka.congr rfl rfl rfl, hl.okb.congr rfl rfl rfl⟩

end Link

theorem PartyView.after_ne {v : PartyView} {t : Token} (he : t ≠ .e) (hs : t ≠ .s) :
    v.after t = v := by
  obtain ⟨_, _, _⟩ := v
  cases t <;> simp_all [PartyView.after] <;> decide

open HandshakeState

theorem encryptAndHash_ok {P : Protocol} {st st' : HandshakeState} {pt o : ByteArray}
    (h : encryptAndHash P st pt = .ok (o, st')) :
    ∃ ss', st.ss.encryptAndHash P.cipher P.hash pt = .ok (o, ss') ∧ st' = { st with ss := ss' } := by
  unfold encryptAndHash at h
  obtain ⟨⟨o', ss'⟩, h1, h2⟩ := bind_ok.mp h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  exact ⟨ss', h1, rfl⟩

theorem decryptAndHash_of {P : Protocol} {st : HandshakeState} {ss ss' : SymmetricState}
    {pt o : ByteArray} (hss : st.ss = ss) (h : ss.encryptAndHash P.cipher P.hash pt = .ok (o, ss')) :
    decryptAndHash P st o = .ok (pt, { st with ss := ss' }) := by
  unfold decryptAndHash
  rw [hss, SymmetricState.decryptAndHash_encryptAndHash P.cipher P.hash h]
  rfl

theorem token_s {P : Protocol} {va vb : PartyView} {a b a' : HandshakeState} {o : ByteArray}
    (hl : Link P va vb a b) (hw : writeToken P a .s = .ok (o, a')) (rest : ByteArray) :
    ∃ b', readToken P b (o ++ rest) .s = .ok (rest, b') ∧ Link P (va.after .s) vb a' b' := by
  simp only [writeToken] at hw
  obtain ⟨kp, hkp, hw⟩ := bind_ok.mp hw
  have has : a.s = some kp := by
    unfold need at hkp; split at hkp
    · simp only [pure, Except.pure, Except.ok.injEq] at hkp; subst hkp; assumption
    · cases hkp
  obtain ⟨ss', henc, rfl⟩ := encryptAndHash_ok hw
  have hsize : o.size = sPubLen P + if b.ss.cs.hasKey then 16 else 0 := by
    rw [SymmetricState.size_encryptAndHash P.cipher P.hash henc, ← hl.ss,
      sPubLen_honest (hl.oka.s kp has)]
  refine ⟨{ ({ b with rs := some kp.pub } : HandshakeState) with ss := ss' }, ?_, ?_⟩
  · simp only [readToken]
    rw [← hsize, take_append]
    simp only [bind, Except.bind]
    rw [decryptAndHash_of hl.ss.symm henc]
    rfl
  · exact (hl.sendS has).withSS fun _ => ss'

theorem token_psk {P : Protocol} {va vb : PartyView} {a b a' : HandshakeState} {o : ByteArray}
    (hl : Link P va vb a b) (hw : writeToken P a .psk = .ok (o, a')) (rest : ByteArray) :
    ∃ b', readToken P b (o ++ rest) .psk = .ok (rest, b') ∧ Link P va vb a' b' := by
  simp only [writeToken] at hw
  split at hw
  · rename_i psk psks hps
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨mixKeyAndHash P { b with psks } psk, ?_, ?_⟩
    · simp only [readToken, ByteArray.empty_append]
      rw [← hl.psks, hps]
      rfl
    · exact (hl.popPsk psks).withSS fun ss => ss.mixKeyAndHash P.hash psk
  · cases hw

/-- What the validator's DH rule guarantees about a DH token: the writer has already sent the key
it contributes, so the reader holds it. -/
def DhReady (t : Token) (initiator : Bool) (v : PartyView) : Prop :=
  ∀ m th, dhRoles t initiator = some (m, th) → (if m then v.sentS else v.sentE) = true

theorem dhRoles_swap {t : Token} {init m th : Bool} (h : dhRoles t init = some (m, th)) :
    dhRoles t (!init) = some (th, m) := by
  cases t <;> cases init <;> simp_all [dhRoles] <;> obtain ⟨rfl, rfl⟩ := h <;> rfl

theorem need_ok {α} {x : Option α} {w : String} {a : α} (h : need x w = .ok a) : x = some a := by
  cases x with
  | none => cases h
  | some a' => simp only [need, pure, Except.pure, Except.ok.injEq] at h; rw [h]

theorem Knows.peer {x y : HandshakeState} {v : PartyView} (h : Knows x y v) {st : Bool}
    {k : ByteArray} (hk : peerKey y st = some k) : ∃ kp, ownKey x st = some kp ∧ kp.pub = k := by
  cases st
  · exact h.re k hk
  · exact h.rs k hk

theorem Knows.sent {x y : HandshakeState} {v : PartyView} (h : Knows x y v) {st : Bool}
    (hs : (if st then v.sentS else v.sentE) = true) :
    ∃ kp, ownKey x st = some kp ∧ peerKey y st = some kp.pub := by
  cases st
  · exact h.sentE hs
  · exact h.sentS hs

theorem PartyOk.own_dh {P : Protocol} {st : HandshakeState} (h : PartyOk P st) {d : DH}
    (hd : P.exchange = .dh d) {m : Bool} {kp : KeyPair} (hk : ownKey st m = some kp) :
    d.Honest kp := by
  cases m
  · have := h.e kp hk; unfold Protocol.EHonest at this; rw [hd] at this; exact this
  · have := h.s kp hk; unfold Protocol.SHonest at this; rw [hd] at this; exact this

theorem token_dh {P : Protocol} {va vb : PartyView} {a b a' : HandshakeState} {o : ByteArray}
    {t : Token} (ht : t.isDH = true) (hl : Link P va vb a b) (hr : DhReady t a.initiator va)
    (hw : writeToken P a t = .ok (o, a')) (rest : ByteArray) :
    ∃ b', readToken P b (o ++ rest) t = .ok (rest, b') ∧ Link P va vb a' b' := by
  have hwd : writeToken P a t = (do pure (ByteArray.empty, ← dhToken P a t)) := by
    cases t <;> simp_all [Token.isDH, writeToken]
  have hrd : ∀ msg, readToken P b msg t = (do pure (msg, ← dhToken P b t)) := by
    intro msg; cases t <;> simp_all [Token.isDH, readToken]
  rw [hwd] at hw
  obtain ⟨a1, hdh, hw⟩ := bind_ok.mp hw
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  unfold dhToken at hdh
  split at hdh
  · rename_i d m th hd hroles
    obtain ⟨A, hA, hdh⟩ := bind_ok.mp hdh
    obtain ⟨x, hx, hdh⟩ := bind_ok.mp hdh
    obtain ⟨K, hK, hdh⟩ := bind_ok.mp hdh
    simp only [pure, Except.pure, Except.ok.injEq] at hdh
    subst hdh
    have hA := need_ok hA
    obtain ⟨B, hB, hBx⟩ := hl.kb.peer (need_ok hx)
    obtain ⟨A', hA', hbA⟩ := hl.ka.sent (hr m th hroles)
    rw [hA] at hA'
    cases hA'
    have hK' : d.dh B.priv A.pub = .ok K := by
      rw [DH.dh_comm d (hl.okb.own_dh hd hB) (hl.oka.own_dh hd hA), hBx]
      exact hK
    refine ⟨mixKey P b K, ?_, ?_⟩
    · rw [hrd, ByteArray.empty_append]
      have hroles' : dhRoles t b.initiator = some (th, m) := by
        rw [hl.roles]; exact dhRoles_swap hroles
      simp only [bind, Except.bind, dhToken, hd, hroles', need, hB, hbA, pure, Except.pure, hK']
    · exact hl.withSS fun ss => ss.mixKey P.hash K
  · cases hdh
  · cases hdh

theorem PartyOk.reliable {P : Protocol} {st : HandshakeState} (h : PartyOk P st) {e s : KEMFn}
    (hk : P.exchange = .kem e s) (i : Nat) :
    e.kem.Reliable (e.kem.stateFromSeed (st.seeds i)) ∧
      s.kem.Reliable (s.kem.stateFromSeed (st.seeds i)) := by
  have := h.seeds; unfold Protocol.Reliable at this; rw [hk] at this; exact this i

theorem token_ekem {P : Protocol} {va vb : PartyView} {a b a' : HandshakeState} {o : ByteArray}
    (hl : Link P va vb a b) (hw : writeToken P a .ekem = .ok (o, a')) (rest : ByteArray) :
    ∃ b', readToken P b (o ++ rest) .ekem = .ok (rest, b') ∧ Link P va vb a' b' := by
  simp only [writeToken] at hw
  split at hw
  · rename_i e s hk
    obtain ⟨x, hx, hw⟩ := bind_ok.mp hw
    obtain ⟨⟨ct, k⟩, hencap, hw⟩ := bind_ok.mp hw
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨B, hB, rfl⟩ := hl.kb.re _ (need_ok hx)
    have hBh : e.Honest B := by
      have := hl.okb.e B hB; unfold Protocol.EHonest at this; rw [hk] at this; exact this
    have hdec := KEMFn.decap_encap e hBh (hl.oka.reliable hk a.draws).1 hencap
    refine ⟨mixKey P (mixHash P b ct) k, ?_, ?_⟩
    · simp only [readToken, hk]
      rw [← KEMFn.size_encap e hencap, take_append]
      simp only [bind, Except.bind, need, hB, pure, Except.pure, hdec]
    · exact hl.drawn.withSS fun ss => (ss.mixHash P.hash ct).mixKey P.hash k
  · cases hw

theorem token_skem {P : Protocol} {va vb : PartyView} {a b a' : HandshakeState} {o : ByteArray}
    (hl : Link P va vb a b) (hw : writeToken P a .skem = .ok (o, a')) (rest : ByteArray) :
    ∃ b', readToken P b (o ++ rest) .skem = .ok (rest, b') ∧ Link P va vb a' b' := by
  simp only [writeToken] at hw
  split at hw
  · rename_i e s hk
    obtain ⟨x, hx, hw⟩ := bind_ok.mp hw
    obtain ⟨⟨ct, k⟩, hencap, hw⟩ := bind_ok.mp hw
    obtain ⟨⟨ect, a2⟩, henc, hw⟩ := bind_ok.mp hw
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨ss', hss', rfl⟩ := encryptAndHash_ok henc
    obtain ⟨B, hB, rfl⟩ := hl.kb.rs _ (need_ok hx)
    have hBh : s.Honest B := by
      have := hl.okb.s B hB; unfold Protocol.SHonest at this; rw [hk] at this; exact this
    have hdec := KEMFn.decap_encap s hBh (hl.oka.reliable hk a.draws).2 hencap
    have hsize : ect.size = s.ctLen + if b.ss.cs.hasKey then 16 else 0 := by
      rw [SymmetricState.size_encryptAndHash P.cipher P.hash hss', ← KEMFn.size_encap s hencap]
      rw [← hl.ss]; rfl
    refine ⟨mixKeyAndHash P { b with ss := ss' } k, ?_, ?_⟩
    · simp only [readToken, hk]
      rw [← hsize, take_append]
      simp only [bind, Except.bind]
      rw [decryptAndHash_of hl.ss.symm hss']
      simp only [need, hB, pure, Except.pure, hdec]
    · exact (hl.drawn.withSS fun _ => ss').withSS fun ss => ss.mixKeyAndHash P.hash k
  · cases hw

theorem token_e {P : Protocol} {va vb : PartyView} {a b a' : HandshakeState} {o : ByteArray}
    (hl : Link P va vb a b) (hw : writeToken P a .e = .ok (o, a')) (rest : ByteArray) :
    ∃ b', readToken P b (o ++ rest) .e = .ok (rest, b') ∧ Link P (va.after .e) vb a' b' := by
  simp only [writeToken] at hw
  obtain ⟨⟨kp, a1⟩, hg, hw⟩ := bind_ok.mp hw
  obtain ⟨hkp, ha1⟩ := generateE_spec P hl.oka hg
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hl1 : Link P va vb a1 b := by rcases ha1 with rfl | rfl; exact hl; exact hl.drawn
  let F : SymmetricState → SymmetricState := fun ss =>
    if P.pattern.hasPsk then (ss.mixHash P.hash kp.pub).mixKey P.hash kp.pub
    else ss.mixHash P.hash kp.pub
  refine ⟨{ ({ b with re := some kp.pub } : HandshakeState) with
      ss := F ({ b with re := some kp.pub } : HandshakeState).ss }, ?_, ?_⟩
  · simp only [readToken]
    rw [← ePubLen_honest hkp, take_append]
    simp only [bind, Except.bind, pure, Except.pure, F]
    split <;> rfl
  · have h := (hl1.sendE hkp).withSS F
    have ha : (if P.pattern.hasPsk = true then
        mixKey P (mixHash P { a1 with e := some kp } kp.pub) kp.pub
        else mixHash P { a1 with e := some kp } kp.pub) =
        { ({ a1 with e := some kp } : HandshakeState) with
          ss := F ({ a1 with e := some kp } : HandshakeState).ss } := by
      simp only [F]; split <;> rfl
    rw [ha]
    exact h

/-! ## The validator's walk, as far as `Link` sees it -/

theorem Knows.views {x y : HandshakeState} {v v' : PartyView} (h : Knows x y v)
    (he : v'.sentE = true → v.sentE = true) (hs : v'.sentS = true → v.sentS = true) :
    Knows x y v' :=
  ⟨h.re, h.rs, fun hv => h.sentE (he hv), fun hv => h.sentS (hs hv)⟩

theorem Link.views {P : Protocol} {va vb va' vb' : PartyView} {a b : HandshakeState}
    (h : Link P va vb a b) (hae : va'.sentE = true → va.sentE = true)
    (has : va'.sentS = true → va.sentS = true) (hbe : vb'.sentE = true → vb.sentE = true)
    (hbs : vb'.sentS = true → vb.sentS = true) : Link P va' vb' a b :=
  ⟨h.ss, h.psks, h.idx, h.roles, h.ka.views hae has, h.kb.views hbe hbs, h.oka, h.okb⟩

/-- One step of the walk moves only the sender's view, by exactly what `PartyView.after` says,
and a DH token passes only once the sender's contributing key has been sent. -/
theorem stepToken_spec {hasPsk init : Bool} {w w' : Walk} {k k' : Nat} {t : Token}
    (h : stepToken hasPsk init w k t = .ok (w', k')) :
    ((w'.party init).sentE = true → ((w.party init).after t).sentE = true) ∧
    ((w'.party init).sentS = true → ((w.party init).after t).sentS = true) ∧
    ((w'.party !init).sentE = true → (w.party !init).sentE = true) ∧
    ((w'.party !init).sentS = true → (w.party !init).sentS = true) ∧
    (t.isDH = true → DhReady t init (w.party init)) := by
  cases t <;> cases init <;>
    simp only [stepToken, Walk.setParty, Walk.party, encrypting, bind, Except.bind, pure,
      Except.pure, throw, throwThe, MonadExceptOf.throw] at h <;>
    (repeat' split at h) <;>
    (try simp only [reduceCtorEq, Except.ok.injEq, Prod.mk.injEq] at h) <;>
    (try obtain ⟨rfl, rfl⟩ := h) <;>
    simp_all [Walk.party, PartyView.after, Token.isDH, DhReady, dhRoles, dhKeysHeld]

theorem writeToken_frame {P : Protocol} {a a' : HandshakeState} {t : Token} {o : ByteArray}
    (h : writeToken P a t = .ok (o, a')) :
    a'.initiator = a.initiator ∧ a'.msgIndex = a.msgIndex := by
  cases t <;> simp only [writeToken] at h
  · obtain ⟨⟨kp, a1⟩, hg, h⟩ := bind_ok.mp h
    have : a1.initiator = a.initiator ∧ a1.msgIndex = a.msgIndex := by
      unfold generateE at hg
      split at hg
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hg; rw [← hg.2]; exact ⟨rfl, rfl⟩
      · split at hg
        · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hg; rw [← hg.2]; exact ⟨rfl, rfl⟩
        · obtain ⟨_, _, hg⟩ := Except.map_eq_ok.mp hg
          simp only [Prod.mk.injEq] at hg; rw [← hg.2]; exact ⟨rfl, rfl⟩
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]; split <;> exact this
  · obtain ⟨kp, -, h⟩ := bind_ok.mp h
    obtain ⟨_, -, rfl⟩ := encryptAndHash_ok h
    exact ⟨rfl, rfl⟩
  all_goals first
    | (obtain ⟨a1, hd, h⟩ := bind_ok.mp h
       simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
       rw [← h.2]
       unfold dhToken at hd
       split at hd
       · obtain ⟨_, -, hd⟩ := bind_ok.mp hd
         obtain ⟨_, -, hd⟩ := bind_ok.mp hd
         obtain ⟨_, -, hd⟩ := bind_ok.mp hd
         simp only [pure, Except.pure, Except.ok.injEq] at hd
         rw [← hd]; exact ⟨rfl, rfl⟩
       · cases hd
       · cases hd)
    | (split at h
       · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact ⟨rfl, rfl⟩
       · cases h)
    | (split at h
       · obtain ⟨_, -, h⟩ := bind_ok.mp h
         obtain ⟨_, -, h⟩ := bind_ok.mp h
         first
           | (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact ⟨rfl, rfl⟩)
           | (obtain ⟨⟨_, _⟩, he, h⟩ := bind_ok.mp h
              obtain ⟨_, -, rfl⟩ := encryptAndHash_ok he
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.2]
              exact ⟨rfl, rfl⟩)
       · cases h)

theorem token_step {P : Protocol} {va vb : PartyView} {a b a' : HandshakeState} {o : ByteArray}
    {t : Token} (hl : Link P va vb a b) (hr : t.isDH = true → DhReady t a.initiator va)
    (hw : writeToken P a t = .ok (o, a')) (rest : ByteArray) :
    ∃ b', readToken P b (o ++ rest) t = .ok (rest, b') ∧ Link P (va.after t) vb a' b' := by
  cases t with
  | e => exact token_e hl hw rest
  | s => exact token_s hl hw rest
  | psk => rw [PartyView.after_ne (by decide) (by decide)]; exact token_psk hl hw rest
  | ekem => rw [PartyView.after_ne (by decide) (by decide)]; exact token_ekem hl hw rest
  | skem => rw [PartyView.after_ne (by decide) (by decide)]; exact token_skem hl hw rest
  | ee | es | se | ss =>
    rw [PartyView.after_ne (by decide) (by decide)]
    exact token_dh rfl hl (hr rfl) hw rest

theorem tokens_agree {P : Protocol} :
    ∀ (ts : List Token) {w w' : Walk} {k : Nat} {a b a' : HandshakeState} {o : ByteArray},
    Link P (w.party a.initiator) (w.party (!a.initiator)) a b →
    stepTokens P.pattern.hasPsk a.initiator w k ts = .ok w' →
    writeTokens P a ts = .ok (o, a') → ∀ rest : ByteArray,
    ∃ b', readTokens P b (o ++ rest) ts = .ok (rest, b') ∧ a'.initiator = a.initiator ∧
      a'.msgIndex = a.msgIndex ∧ Link P (w'.party a.initiator) (w'.party (!a.initiator)) a' b'
  | [], w, w', k, a, b, a', o, hl, hs, hw, rest => by
    simp only [stepTokens, pure, Except.pure, Except.ok.injEq] at hs
    simp only [writeTokens, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    subst hs
    exact ⟨b, by simp [readTokens, ByteArray.empty_append, pure, Except.pure], rfl, rfl, hl⟩
  | t :: ts, w, w', k, a, b, a', o, hl, hs, hw, rest => by
    obtain ⟨⟨w1, k1⟩, hs1, hs⟩ := bind_ok.mp hs
    obtain ⟨⟨o1, a1⟩, hw1, hw⟩ := bind_ok.mp hw
    obtain ⟨⟨os, a2⟩, hw2, hw⟩ := bind_ok.mp hw
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨he', hs', hpe, hps, hdh⟩ := stepToken_spec hs1
    obtain ⟨b1, hr1, hl1⟩ := token_step hl hdh hw1 (os ++ rest)
    obtain ⟨hini, hidx⟩ := writeToken_frame hw1
    have hl1' : Link P (w1.party a1.initiator) (w1.party (!a1.initiator)) a1 b1 := by
      rw [hini]; exact hl1.views he' hs' hpe hps
    obtain ⟨b2, hr2, hini2, hidx2, hl2⟩ := tokens_agree ts hl1' (by rw [hini]; exact hs) hw2 rest
    refine ⟨b2, ?_, hini2.trans hini, hidx2.trans hidx, by rw [← hini]; exact hl2⟩
    simp only [readTokens]
    rw [ByteArray.append_assoc, hr1]
    exact hr2

theorem Link.nextIdx {P : Protocol} {va vb : PartyView} {a b : HandshakeState}
    (hl : Link P va vb a b) :
    Link P va vb { a with msgIndex := a.msgIndex + 1 } { b with msgIndex := b.msgIndex + 1 } :=
  ⟨hl.ss, hl.psks, by simp [hl.idx], hl.roles, hl.ka.congr rfl rfl rfl rfl,
   hl.kb.congr rfl rfl rfl rfl, hl.oka.congr rfl rfl rfl, hl.okb.congr rfl rfl rfl⟩

theorem stepMessage_tokens {hasPsk init : Bool} {w w' : Walk} {m : List Token}
    (h : stepMessage hasPsk init w m = .ok w') : stepTokens hasPsk init w 0 m = .ok w' := by
  unfold stepMessage at h
  obtain ⟨w1, hs, h⟩ := bind_ok.mp h
  simp only [bind, Except.bind, pure, Except.pure, encrypting, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' split at h
  all_goals first
    | (simp only [Except.ok.injEq] at h; subst h; exact hs)
    | (simp at h; done)
    | exact hs

/-- An honest writer's message is read back by the honest reader with the same payload, and the
pair stays linked under the validator's next walk state. -/
theorem message_agree {P : Protocol} {w w' : Walk} {a b a' : HandshakeState} {pt msg : ByteArray}
    (hl : Link P (w.party a.initiator) (w.party (!a.initiator)) a b)
    (hstep : stepMessage P.pattern.hasPsk a.initiator w
      (P.pattern.messages.getD a.msgIndex []) = .ok w')
    (hw : HandshakeState.writeMessage P a pt = .ok (msg, a')) :
    ∃ b', HandshakeState.readMessage P b msg = .ok (pt, b') ∧ a'.initiator = a.initiator ∧
      a'.msgIndex = a.msgIndex + 1 ∧
      Link P (w'.party a.initiator) (w'.party (!a.initiator)) a' b' := by
  unfold HandshakeState.writeMessage at hw
  obtain ⟨tokens, hcur, hw⟩ := bind_ok.mp hw
  have hfin : HandshakeState.isFinished P a = false := by
    cases hf : HandshakeState.isFinished P a
    · rfl
    · simp [HandshakeState.currentMessage, hf, throw, throwThe, MonadExceptOf.throw, bind,
        Except.bind] at hcur
  have htok : tokens = P.pattern.messages.getD a.msgIndex [] := by
    simp [HandshakeState.currentMessage, hfin, pure, Except.pure] at hcur; exact hcur.symm
  have hcur0 : HandshakeState.currentMessage P a = .ok tokens := by
    simp [HandshakeState.currentMessage, hfin, pure, Except.pure, htok]
  subst htok
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at hw
  split at hw
  · cases hw
  rename_i hturn
  split at hw
  · cases hw
  rename_i r hwt
  obtain ⟨buf, a1⟩ := r
  split at hw
  · cases hw
  rename_i r henc
  obtain ⟨ct, a2⟩ := r
  simp only at hw
  split at hw
  · cases hw
  rename_i hsize
  simp only [Except.ok.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨b1, hr1, hini1, hidx1, hl1⟩ := tokens_agree _ hl (stepMessage_tokens hstep) hwt ct
  obtain ⟨ss', henc', rfl⟩ := encryptAndHash_ok henc
  refine ⟨{ ({ b1 with ss := ss' } : HandshakeState) with
      msgIndex := ({ b1 with ss := ss' } : HandshakeState).msgIndex + 1 }, ?_, hini1,
    by simp [hidx1], ?_⟩
  · have hidx : b.msgIndex = a.msgIndex := hl.idx.symm
    have hcurb : HandshakeState.currentMessage P b = HandshakeState.currentMessage P a := by
      unfold HandshakeState.currentMessage HandshakeState.isFinished; rw [hidx]
    unfold HandshakeState.readMessage
    rw [hcurb, hcur0]
    simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
    have hturnb : (P.pattern.initiatorSends b.msgIndex == b.initiator) = false := by
      rw [hidx, hl.roles]
      cases h : P.pattern.initiatorSends a.msgIndex <;> cases ha : a.initiator <;>
        simp_all
    rw [if_neg (by simp [hturnb]), if_neg (by simpa using hsize), hr1]
    simp only
    rw [decryptAndHash_of hl1.ss.symm henc']
  · exact (hl1.withSS fun _ => ss').nextIdx

theorem writeMessage_turn {P : Protocol} {a a' : HandshakeState} {pt msg : ByteArray}
    (hw : HandshakeState.writeMessage P a pt = .ok (msg, a')) :
    HandshakeState.isFinished P a = false ∧ P.pattern.initiatorSends a.msgIndex = a.initiator := by
  unfold HandshakeState.writeMessage at hw
  obtain ⟨tokens, hcur, hw⟩ := bind_ok.mp hw
  have hfin : HandshakeState.isFinished P a = false := by
    cases hf : HandshakeState.isFinished P a
    · rfl
    · simp [HandshakeState.currentMessage, hf, throw, throwThe, MonadExceptOf.throw, bind,
        Except.bind] at hcur
  refine ⟨hfin, ?_⟩
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at hw
  split at hw
  · cases hw
  · rename_i h; simpa using h

/-! ## Whole handshakes -/

/-- The initiator `ini` and the responder `res` are in step: linked under a walk state from which
the rest of the pattern still validates. -/
def Synced (P : Protocol) (ini res : HandshakeState) : Prop :=
  ini.initiator = true ∧ ∃ w w', Link P w.init w.resp ini res ∧
    stepMessages P.pattern w ini.msgIndex (P.pattern.messages.drop ini.msgIndex) = .ok w'

theorem drop_getD {α} {l : List α} {i : Nat} (d : α) (h : i < l.length) :
    l.drop i = l.getD i d :: l.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons h]
  simp [List.getD, List.getElem?_eq_getElem h]

theorem Synced.step {P : Protocol} {ini res : HandshakeState} (hs : Synced P ini res) :
    ∃ w w', Link P w.init w.resp ini res ∧
      (HandshakeState.isFinished P ini = false →
        stepMessage P.pattern.hasPsk (P.pattern.initiatorSends ini.msgIndex) w
          (P.pattern.messages.getD ini.msgIndex []) = .ok w' ∧
        ∃ w'', stepMessages P.pattern w' (ini.msgIndex + 1)
          (P.pattern.messages.drop (ini.msgIndex + 1)) = .ok w'') := by
  obtain ⟨_, w, wf, hl, hsm⟩ := hs
  by_cases hfin : HandshakeState.isFinished P ini = false
  · have hlt : ini.msgIndex < P.pattern.messages.length := by
      simp [HandshakeState.isFinished] at hfin; exact hfin
    rw [drop_getD [] hlt] at hsm
    obtain ⟨w1, h1, h2⟩ := bind_ok.mp hsm
    exact ⟨w, w1, hl, fun _ => ⟨h1, wf, h2⟩⟩
  · exact ⟨w, w, hl, fun h => absurd h hfin⟩

/-- The initiator writes; the responder reads the same payload and the two stay in step. -/
theorem Synced.initiator_writes {P : Protocol} {ini res ini' : HandshakeState} {pt msg : ByteArray}
    (hs : Synced P ini res) (hw : HandshakeState.writeMessage P ini pt = .ok (msg, ini')) :
    ∃ res', HandshakeState.readMessage P res msg = .ok (pt, res') ∧ Synced P ini' res' := by
  have hini := hs.1
  obtain ⟨hfin, hturn⟩ := writeMessage_turn hw
  obtain ⟨w, w', hl, hstep⟩ := hs.step
  obtain ⟨hst, w'', hrest⟩ := hstep hfin
  rw [hturn] at hst
  have hl' : Link P (w.party ini.initiator) (w.party (!ini.initiator)) ini res := by
    rw [hini]; exact hl
  obtain ⟨res', hr, hini', hidx', hl''⟩ := message_agree hl' hst hw
  refine ⟨res', hr, by rw [hini', hini], w', w'', ?_, by rw [hidx']; exact hrest⟩
  rw [hini] at hl''; exact hl''

/-- The responder writes; the initiator reads the same payload and the two stay in step. -/
theorem Synced.responder_writes {P : Protocol} {ini res res' : HandshakeState} {pt msg : ByteArray}
    (hs : Synced P ini res) (hw : HandshakeState.writeMessage P res pt = .ok (msg, res')) :
    ∃ ini', HandshakeState.readMessage P ini msg = .ok (pt, ini') ∧ Synced P ini' res' := by
  have hini := hs.1
  obtain ⟨hfin, hturn⟩ := writeMessage_turn hw
  obtain ⟨w, w', hl, hstep⟩ := hs.step
  have hidx : res.msgIndex = ini.msgIndex := hl.idx.symm
  have hres : res.initiator = false := by rw [hl.roles, hini]; rfl
  have hfin' : HandshakeState.isFinished P ini = false := by
    rw [← hfin]; simp [HandshakeState.isFinished, hidx]
  obtain ⟨hst, w'', hrest⟩ := hstep hfin'
  rw [← hidx, hturn] at hst
  have hl' : Link P (w.party res.initiator) (w.party (!res.initiator)) res ini := by
    rw [hres]; exact hl.symm
  obtain ⟨ini', hr, hres', hidx', hl''⟩ := message_agree hl' hst hw
  have hl3 : Link P w'.init w'.resp ini' res' := by rw [hres] at hl''; exact hl''.symm
  refine ⟨ini', hr, by rw [hl3.symm.roles, hres', hres]; rfl, w', w'', hl3, ?_⟩
  have : ini'.msgIndex = ini.msgIndex + 1 := by rw [hl3.idx, hidx', hidx]
  rw [this]; exact hrest

/-- At the end of the handshake both parties hold the same handshake hash, and each one's sending
cipher state is the other's receiving one. -/
theorem Synced.finish {P : Protocol} {ini res : HandshakeState} (hs : Synced P ini res)
    (hfin : HandshakeState.isFinished P ini = true) :
    ∃ ti tr, TransportState.ofHandshake P ini = .ok ti ∧ TransportState.ofHandshake P res = .ok tr ∧
      ti.handshakeHash = tr.handshakeHash ∧ ti.send = tr.recv ∧ ti.recv = tr.send := by
  obtain ⟨hini, w, w', hl, -⟩ := hs
  have hres : res.initiator = false := by rw [hl.roles, hini]; rfl
  have hfin' : HandshakeState.isFinished P res = true := by
    rw [← hfin]; simp [HandshakeState.isFinished, hl.idx]
  refine ⟨{ send := some (ini.ss.split P.hash).1,
             recv := if P.pattern.oneWay then none else some (ini.ss.split P.hash).2,
             handshakeHash := ini.ss.h },
           { send := if P.pattern.oneWay then none else some (res.ss.split P.hash).2,
             recv := some (res.ss.split P.hash).1,
             handshakeHash := res.ss.h }, ?_, ?_, ?_, ?_, ?_⟩
  · simp [TransportState.ofHandshake, hfin, hini, pure, Except.pure]
  · simp [TransportState.ofHandshake, hfin', hres, pure, Except.pure]
  · simp [hl.ss]
  · simp [hl.ss]
  · simp [hl.ss]

/-! ## Starting in step -/

/-- Two configurations an honest initiator and responder could start from: the same prologue and
PSKs, honest keys, reliable randomness, and correct knowledge of each other's public keys. -/
structure HonestConfigs (P : Protocol) (ci cr : Config) : Prop where
  ini : ci.initiator = true
  res : cr.initiator = false
  prologue : ci.prologue = cr.prologue
  psks : ci.psks = cr.psks
  iS : ∀ kp, ci.s = some kp → P.SHonest kp
  iE : ∀ kp, ci.e = some kp → P.EHonest kp
  rS : ∀ kp, cr.s = some kp → P.SHonest kp
  rE : ∀ kp, cr.e = some kp → P.EHonest kp
  iSeeds : P.Reliable ci.seeds
  rSeeds : P.Reliable cr.seeds
  iRS : ∀ k, ci.rs = some k → ∃ kp, cr.s = some kp ∧ kp.pub = k
  iRE : ∀ k, ci.re = some k → ∃ kp, cr.e = some kp ∧ kp.pub = k
  rRS : ∀ k, cr.rs = some k → ∃ kp, ci.s = some kp ∧ kp.pub = k
  rRE : ∀ k, cr.re = some k → ∃ kp, ci.e = some kp ∧ kp.pub = k

/-- A pre-message changes only the symmetric state, and needs the key it hashes. -/
theorem preMessage_spec {P : Protocol} {sender : Bool} {st st' : HandshakeState} {t : Token}
    (h : preMessage P sender st t = .ok st') :
    st' = { st with ss := st'.ss } ∧ ∃ static, preKey t = some static ∧
      (sender = st.initiator → (ownKey st static).isSome) ∧
      (sender ≠ st.initiator → (peerKey st static).isSome) := by
  unfold preMessage at h
  split at h
  · cases h
  · rename_i static hk
    obtain ⟨key, hkey, h⟩ := Except.map_eq_ok.mp h
    subst h
    unfold preMessageKey at hkey
    refine ⟨by split <;> rfl, static, hk, ?_, ?_⟩
    · intro hs
      rw [if_pos (by simp [hs])] at hkey
      obtain ⟨kp, hkp, -⟩ := Except.map_eq_ok.mp hkey
      rw [need_ok hkp]; rfl
    · intro hs
      rw [if_neg (by simpa using hs)] at hkey
      rw [need_ok hkey]; rfl

theorem preMessages_spec {P : Protocol} {sender : Bool} :
    ∀ (ts : List Token) {st st' : HandshakeState}, preMessages P sender st ts = .ok st' →
      st' = { st with ss := st'.ss } ∧ ∀ t ∈ ts, ∃ static, preKey t = some static ∧
        (sender = st.initiator → (ownKey st static).isSome) ∧
        (sender ≠ st.initiator → (peerKey st static).isSome)
  | [], st, st', h => by
    simp only [preMessages, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, by simp⟩
  | t :: ts, st, st', h => by
    obtain ⟨st1, h1, h2⟩ := bind_ok.mp h
    obtain ⟨hf1, hk1⟩ := preMessage_spec h1
    obtain ⟨hf2, hk2⟩ := preMessages_spec ts h2
    rw [hf1] at hk2
    refine ⟨by rw [hf2, hf1], ?_⟩
    intro t' ht'
    rcases List.mem_cons.mp ht' with rfl | ht'
    · exact hk1
    · exact hk2 t' ht'

/-- The two sides hash the same pre-message keys: one its own, the other what it was told. -/
theorem preMessages_agree {P : Protocol} {sender : Bool} :
    ∀ (ts : List Token) {a b a' b' : HandshakeState},
      a.initiator = sender → b.initiator = !sender → a.ss = b.ss →
      (∀ k, b.re = some k → ∃ kp, a.e = some kp ∧ kp.pub = k) →
      (∀ k, b.rs = some k → ∃ kp, a.s = some kp ∧ kp.pub = k) →
      preMessages P sender a ts = .ok a' → preMessages P sender b ts = .ok b' → a'.ss = b'.ss
  | [], a, b, a', b', _, _, hss, _, _, ha, hb => by
    simp only [preMessages, pure, Except.pure, Except.ok.injEq] at ha hb
    subst ha hb; exact hss
  | t :: ts, a, b, a', b', hai, hbi, hss, hre, hrs, ha, hb => by
    obtain ⟨a1, ha1, ha2⟩ := bind_ok.mp ha
    obtain ⟨b1, hb1, hb2⟩ := bind_ok.mp hb
    obtain ⟨hfa, -⟩ := preMessage_spec ha1
    obtain ⟨hfb, -⟩ := preMessage_spec hb1
    refine preMessages_agree ts (by rw [hfa]; exact hai) (by rw [hfb]; exact hbi) ?_
      (by rw [hfa, hfb]; exact hre) (by rw [hfa, hfb]; exact hrs) ha2 hb2
    unfold preMessage at ha1 hb1
    split at ha1
    · cases ha1
    · rename_i static hk
      rw [hk] at hb1
      obtain ⟨ka, hka, ha1⟩ := Except.map_eq_ok.mp ha1
      obtain ⟨kb, hkb, hb1⟩ := Except.map_eq_ok.mp hb1
      unfold preMessageKey at hka hkb
      rw [if_pos (by simp [hai])] at hka
      rw [if_neg (by simp [hbi])] at hkb
      obtain ⟨kp, hkp, rfl⟩ := Except.map_eq_ok.mp hka
      have hkp := need_ok hkp
      have hkb := need_ok hkb
      have hsame : kp.pub = kb := by
        cases static
        · obtain ⟨kp', h1, h2⟩ := hre kb hkb; simp [ownKey] at hkp; rw [hkp] at h1; cases h1; exact h2
        · obtain ⟨kp', h1, h2⟩ := hrs kb hkb; simp [ownKey] at hkp; rw [hkp] at h1; cases h1; exact h2
      subst ha1 hb1
      rw [hsame]
      split <;> simp [HandshakeState.mixHash, HandshakeState.mixKey, hss]

theorem check_validate {P : Protocol} (h : HandshakeState.check P = .ok ()) :
    ∃ w', stepMessages P.pattern (Walk.initial P.pattern) 0 P.pattern.messages = .ok w' := by
  unfold HandshakeState.check at h
  split at h
  · cases h
  · rename_i hv
    unfold validate at hv
    obtain ⟨_, -, hv⟩ := bind_ok.mp hv
    obtain ⟨w', hw', -⟩ := bind_ok.mp hv
    exact ⟨w', hw'⟩

/-- Honest initiator and responder configurations initialize into states that are in step. -/
theorem initialize_synced {P : Protocol} {ci cr : Config} {ini res : HandshakeState}
    (hc : HonestConfigs P ci cr) (hi : HandshakeState.initialize P ci = .ok ini)
    (hr : HandshakeState.initialize P cr = .ok res) : Synced P ini res := by
  unfold HandshakeState.initialize at hi hr
  obtain ⟨_, hchk, hi⟩ := bind_ok.mp hi
  obtain ⟨_, -, hr⟩ := bind_ok.mp hr
  obtain ⟨i1, hi1, hi2⟩ := bind_ok.mp hi
  obtain ⟨r1, hr1, hr2⟩ := bind_ok.mp hr
  obtain ⟨w', hw'⟩ := check_validate hchk
  obtain ⟨fi1, -⟩ := preMessages_spec _ hi1
  obtain ⟨fi2, ki2⟩ := preMessages_spec _ hi2
  obtain ⟨fr1, kr1⟩ := preMessages_spec _ hr1
  obtain ⟨fr2, -⟩ := preMessages_spec _ hr2
  have hss1 : i1.ss = r1.ss :=
    preMessages_agree _ hc.ini (by simp [HandshakeState.ofConfig, hc.res])
      (by simp [HandshakeState.ofConfig, hc.prologue]) (fun k hk => hc.rRE k hk)
      (fun k hk => hc.rRS k hk) hi1 hr1
  have hss : res.ss = ini.ss := by
    refine preMessages_agree _ (a := r1) (b := i1) ?_ ?_ hss1.symm ?_ ?_ hr2 hi2
    · rw [fr1]; exact hc.res
    · rw [fi1]; simp [HandshakeState.ofConfig, hc.ini]
    · intro k hk; rw [fi1] at hk; rw [fr1]; exact hc.iRE k hk
    · intro k hk; rw [fi1] at hk; rw [fr1]; exact hc.iRS k hk
  rw [fi1] at fi2 ki2
  rw [fr1] at fr2
  have hini : ini.initiator = true := by rw [fi2]; exact hc.ini
  refine ⟨hini, Walk.initial P.pattern, w', ?_, ?_⟩
  · refine ⟨hss.symm, by rw [fi2, fr2]; exact hc.psks, by rw [fi2, fr2]; rfl,
      by rw [fi2, fr2]; simp [HandshakeState.ofConfig, hc.ini, hc.res], ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro k hk; rw [fr2] at hk; rw [fi2]; exact hc.rRE k hk
      · intro k hk; rw [fr2] at hk; rw [fi2]; exact hc.rRS k hk
      · intro hv
        obtain ⟨st, hst, -, hpeer⟩ := kr1 .e (by simpa [Walk.initial] using hv)
        cases hst
        obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp
          (hpeer (by simp [HandshakeState.ofConfig, hc.res]))
        obtain ⟨kp, h1, h2⟩ := hc.rRE k hk
        exact ⟨kp, by rw [fi2]; exact h1, by rw [fr2]; simp [HandshakeState.ofConfig, HandshakeState.peerKey] at hk ⊢; rw [hk, h2]⟩
      · intro hv
        obtain ⟨st, hst, -, hpeer⟩ := kr1 .s (by simpa [Walk.initial] using hv)
        cases hst
        obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp
          (hpeer (by simp [HandshakeState.ofConfig, hc.res]))
        obtain ⟨kp, h1, h2⟩ := hc.rRS k hk
        exact ⟨kp, by rw [fi2]; exact h1, by rw [fr2]; simp [HandshakeState.ofConfig, HandshakeState.peerKey] at hk ⊢; rw [hk, h2]⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro k hk; rw [fi2] at hk; rw [fr2]; exact hc.iRE k hk
      · intro k hk; rw [fi2] at hk; rw [fr2]; exact hc.iRS k hk
      · intro hv
        obtain ⟨st, hst, -, hpeer⟩ := ki2 .e (by simpa [Walk.initial] using hv)
        cases hst
        obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp
          (hpeer (by simp [HandshakeState.ofConfig, hc.ini]))
        obtain ⟨kp, h1, h2⟩ := hc.iRE k hk
        exact ⟨kp, by rw [fr2]; exact h1, by rw [fi2]; simp [HandshakeState.ofConfig, HandshakeState.peerKey] at hk ⊢; rw [hk, h2]⟩
      · intro hv
        obtain ⟨st, hst, -, hpeer⟩ := ki2 .s (by simpa [Walk.initial] using hv)
        cases hst
        obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp
          (hpeer (by simp [HandshakeState.ofConfig, hc.ini]))
        obtain ⟨kp, h1, h2⟩ := hc.iRS k hk
        exact ⟨kp, by rw [fr2]; exact h1, by rw [fi2]; simp [HandshakeState.ofConfig, HandshakeState.peerKey] at hk ⊢; rw [hk, h2]⟩
    · rw [fi2]; exact ⟨hc.iE, hc.iS, hc.iSeeds⟩
    · rw [fr2]; exact ⟨hc.rE, hc.rS, hc.rSeeds⟩
  · rw [fi2]; simpa [HandshakeState.ofConfig] using hw'

end Uproar
