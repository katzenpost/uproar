/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Uproar.Patterns

/-! # Pattern validity (Noise §7.3, §9.3; PQ Noise §2.3)

`validate` walks a pattern once, tracking which keys each party has sent, which DH tokens have
run, whether a key is in use and whether a `psk` has been mixed in. -/

namespace Uproar

structure PartyView where
  sentE : Bool := false
  sentS : Bool := false
  /-- Has contributed fresh randomness, as the PSK rule requires before encrypting. -/
  fresh : Bool := false

structure Walk where
  init : PartyView := {}
  resp : PartyView := {}
  dhDone : List Token := []
  pskSeen : Bool := false
  keyed : Bool := false

namespace Walk

def party (w : Walk) (initiator : Bool) : PartyView := if initiator then w.init else w.resp

def setParty (w : Walk) (initiator : Bool) (v : PartyView) : Walk :=
  if initiator then { w with init := v } else { w with resp := v }

def did (w : Walk) (t : Token) : Bool := w.dhDone.contains t

/-- §7.3 rules 3 and 4: a party may only encrypt once every static-key DH it took part in is
matched by the corresponding ephemeral DH. -/
def payloadSafe (w : Walk) (initiator : Bool) : Bool :=
  if initiator then (!w.did .se || w.did .ee) && (!w.did .ss || w.did .es)
  else (!w.did .es || w.did .ee) && (!w.did .ss || w.did .se)

/-- §9.3: no encrypted data after a `psk` until the sender has contributed randomness. -/
def pskSafe (w : Walk) (initiator : Bool) : Bool := !w.pskSeen || (w.party initiator).fresh

end Walk

abbrev Check := Except String

def preMessageOk : List Token → Bool
  | [] | [.e] | [.s] | [.e, .s] => true
  | _ => false

def dhKeysHeld (w : Walk) : Token → Bool
  | .ee => w.init.sentE && w.resp.sentE
  | .es => w.init.sentE && w.resp.sentS
  | .se => w.init.sentS && w.resp.sentE
  | .ss => w.init.sentS && w.resp.sentS
  | _ => true

def encrypting (w : Walk) (initiator : Bool) : Check Unit := do
  if w.keyed && !w.pskSafe initiator then throw "encrypted data after psk before fresh randomness"

/-- One token, sent by `initiator` (or by the responder); `kemSeen` tracks the PQ ordering rule
within the current message: `ekem` before `skem` before public keys. -/
def stepToken (hasPsk : Bool) (initiator : Bool) (w : Walk) (kemOrder : Nat) (t : Token) :
    Check (Walk × Nat) := do
  let me := w.party initiator
  let peer := w.party !initiator
  match t with
  | .e =>
    if me.sentE then throw "e sent twice"
    let w := w.setParty initiator { me with sentE := true, fresh := true }
    pure ({ w with keyed := w.keyed || hasPsk }, 3)
  | .s =>
    if me.sentS then throw "s sent twice"
    encrypting w initiator
    pure (w.setParty initiator { me with sentS := true }, 3)
  | .ee | .es | .se | .ss =>
    if w.did t then throw "DH token repeated"
    if !dhKeysHeld w t then throw "DH with a key not yet held"
    pure ({ w with dhDone := t :: w.dhDone, keyed := true }, kemOrder)
  | .psk =>
    pure ({ w with pskSeen := true, keyed := true }, kemOrder)
  | .ekem =>
    if kemOrder > 1 then throw "ekem after skem or a public key"
    if !peer.sentE then throw "ekem without the peer's ephemeral key"
    let w := w.setParty initiator { me with fresh := true }
    pure ({ w with keyed := true }, 1)
  | .skem =>
    if kemOrder > 2 then throw "skem after a public key"
    if !peer.sentS then throw "skem without the peer's static key"
    encrypting w initiator
    let w := if w.pskSeen then w else w.setParty initiator { me with fresh := true }
    pure ({ w with keyed := true }, 2)

def stepMessage (hasPsk : Bool) (initiator : Bool) (w : Walk) (msg : List Token) : Check Walk := do
  let (w, _) ← msg.foldlM (fun (w, k) t => stepToken hasPsk initiator w k t) (w, 0)
  if !w.payloadSafe initiator then throw "payload before the matching ephemeral DH"
  encrypting w initiator
  pure w

def validate (p : HandshakePattern) : Check Unit := do
  if !preMessageOk p.preInitiator || !preMessageOk p.preResponder then
    throw "pre-message must be e, s, or e, s"
  if p.preInitiator.contains .psk || p.preResponder.contains .psk then throw "psk in pre-message"
  if p.messages.any (·.any Token.isDH) && p.isKEM then throw "DH and KEM tokens mixed"
  if p.messages.isEmpty then throw "no messages"
  let w : Walk := {
    init := { sentE := p.preInitiator.contains .e, sentS := p.preInitiator.contains .s,
              fresh := p.preInitiator.contains .e }
    resp := { sentE := p.preResponder.contains .e, sentS := p.preResponder.contains .s,
              fresh := p.preResponder.contains .e }
    keyed := p.hasPsk && (p.preInitiator.contains .e || p.preResponder.contains .e) }
  let (w, _) ← p.messages.foldlM (fun (w, i) m => do
    pure (← stepMessage p.hasPsk (p.initiatorSends i) w m, i + 1)) (w, 0)
  if !w.payloadSafe true then throw "initiator transport before the matching ephemeral DH"
  if !p.oneWay && !w.payloadSafe false then
    throw "responder transport before the matching ephemeral DH"

def isValid (p : HandshakePattern) : Bool := (validate p).toBool

theorem named_valid :
    (Patterns.bases ++ Patterns.classicalPsk ++ Patterns.pqPsk).all isValid = true := by
  decide

end Uproar
