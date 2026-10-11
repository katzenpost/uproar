/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Uproar.SymmetricState
import Uproar.Validation

/-! # HandshakeState (Noise §5.3, PQ Noise §2)

One state machine for both: `e` and `s` carry DH or KEM public keys according to the protocol's
`Exchange`, DH tokens mix a Diffie-Hellman result into the chaining key, `ekem` mixes a
ciphertext into the hash and its shared secret into the chaining key, and `skem` encrypts its
ciphertext and mixes its shared secret into both. -/

namespace Uproar

structure Protocol where
  pattern : HandshakePattern
  exchange : Exchange
  cipher : Cipher
  hash : HashFn

def Protocol.name (P : Protocol) : String :=
  s!"Noise_{P.pattern.name}_{P.exchange.name}_{P.cipher.name}_{P.hash.name}"

/-- What a party brings to a handshake. `e` fixes the ephemeral key, which only test vectors
should do; otherwise ephemeral keys and encapsulation coins are drawn from `seeds`. -/
structure Config where
  initiator : Bool
  prologue : ByteArray := ByteArray.empty
  s : Option KeyPair := none
  e : Option KeyPair := none
  rs : Option ByteArray := none
  re : Option ByteArray := none
  psks : List ByteArray := []
  seeds : Nat → Vector UInt8 32

structure HandshakeState where
  initiator : Bool
  ss : SymmetricState
  s : Option KeyPair
  e : Option KeyPair
  rs : Option ByteArray
  re : Option ByteArray
  psks : List ByteArray
  seeds : Nat → Vector UInt8 32
  draws : Nat
  msgIndex : Nat

namespace HandshakeState

variable (P : Protocol)

def mixHash (st : HandshakeState) (data : ByteArray) : HandshakeState :=
  { st with ss := st.ss.mixHash P.hash data }

def mixKey (st : HandshakeState) (ikm : ByteArray) : HandshakeState :=
  { st with ss := st.ss.mixKey P.hash ikm }

def mixKeyAndHash (st : HandshakeState) (ikm : ByteArray) : HandshakeState :=
  { st with ss := st.ss.mixKeyAndHash P.hash ikm }

def encryptAndHash (st : HandshakeState) (pt : ByteArray) : Result (ByteArray × HandshakeState) := do
  let (ct, ss) ← st.ss.encryptAndHash P.cipher P.hash pt
  pure (ct, { st with ss })

def decryptAndHash (st : HandshakeState) (ct : ByteArray) : Result (ByteArray × HandshakeState) := do
  let (pt, ss) ← st.ss.decryptAndHash P.cipher P.hash ct
  pure (pt, { st with ss })

def drawn (st : HandshakeState) : HandshakeState := { st with draws := st.draws + 1 }

def ePubLen : Nat :=
  match P.exchange with
  | .dh d => d.pubLen
  | .kem e _ => e.pubLen

def sPubLen : Nat :=
  match P.exchange with
  | .dh d => d.pubLen
  | .kem _ s => s.pubLen

def generateE (st : HandshakeState) : Result (KeyPair × HandshakeState) :=
  match st.e with
  | some kp => pure (kp, st)
  | none =>
    match P.exchange with
    | .dh d => pure (d.ofSeed (st.seeds st.draws), st.drawn)
    | .kem e _ => (e.ofSeed (st.seeds st.draws)).map (·, st.drawn)

def need {α} (x : Option α) (which : String) : Result α :=
  match x with
  | some a => pure a
  | none => throw (.missingKey which)

/-- Whether a DH token combines this party's static (`true`) or ephemeral key with the peer's
static or ephemeral key. -/
def dhRoles (t : Token) (initiator : Bool) : Option (Bool × Bool) :=
  match t, initiator with
  | .ee, _ => some (false, false)
  | .ss, _ => some (true, true)
  | .es, true | .se, false => some (false, true)
  | .es, false | .se, true => some (true, false)
  | _, _ => none

def ownKey (st : HandshakeState) (static : Bool) : Option KeyPair := if static then st.s else st.e

def peerKey (st : HandshakeState) (static : Bool) : Option ByteArray :=
  if static then st.rs else st.re

def dhToken (st : HandshakeState) (t : Token) : Result HandshakeState :=
  match P.exchange, dhRoles t st.initiator with
  | .dh d, some (mine, theirs) => do
    let kp ← need (ownKey st mine) (if mine then "s" else "e")
    let pk ← need (peerKey st theirs) (if theirs then "rs" else "re")
    pure (mixKey P st (← d.dh kp.priv pk))
  | .dh _, none => throw (.invalidPattern "not a DH token")
  | .kem _ _, _ => throw .wrongExchange

/-- One token: the bytes it puts on the wire, and the state after. -/
def writeToken (st : HandshakeState) (t : Token) : Result (ByteArray × HandshakeState) := do
  match t with
  | .e =>
    let (kp, st) ← generateE P st
    let st := mixHash P { st with e := some kp } kp.pub
    pure (kp.pub, if P.pattern.hasPsk then mixKey P st kp.pub else st)
  | .s => encryptAndHash P st (← need st.s "s").pub
  | .ee | .es | .se | .ss => pure (ByteArray.empty, ← dhToken P st t)
  | .psk =>
    let psk :: psks := st.psks | throw .missingPsk
    pure (ByteArray.empty, mixKeyAndHash P { st with psks } psk)
  | .ekem =>
    let .kem ekem _ := P.exchange | throw .wrongExchange
    let (ct, k) ← ekem.encap (← need st.re "re") (st.seeds st.draws)
    pure (ct, mixKey P (mixHash P st.drawn ct) k)
  | .skem =>
    let .kem _ skem := P.exchange | throw .wrongExchange
    let (ct, k) ← skem.encap (← need st.rs "rs") (st.seeds st.draws)
    let (ect, st) ← encryptAndHash P st.drawn ct
    pure (ect, mixKeyAndHash P st k)

def writeTokens (st : HandshakeState) : List Token → Result (ByteArray × HandshakeState)
  | [] => pure (ByteArray.empty, st)
  | t :: ts => do
    let (o, st) ← writeToken P st t
    let (os, st) ← writeTokens st ts
    pure (o ++ os, st)

def take (msg : ByteArray) (n : Nat) : Result (ByteArray × ByteArray) :=
  if msg.size < n then throw .messageTooShort
  else pure (msg.extract 0 n, msg.extract n msg.size)

/-- One token read from the front of `msg`: the rest of the message, and the state after. -/
def readToken (st : HandshakeState) (msg : ByteArray) (t : Token) :
    Result (ByteArray × HandshakeState) := do
  match t with
  | .e =>
    let (re, msg) ← take msg (ePubLen P)
    let st := mixHash P { st with re := some re } re
    pure (msg, if P.pattern.hasPsk then mixKey P st re else st)
  | .s =>
    let (ct, msg) ← take msg (sPubLen P + if st.ss.cs.hasKey then 16 else 0)
    let (rs, st) ← decryptAndHash P st ct
    pure (msg, { st with rs := some rs })
  | .ee | .es | .se | .ss => pure (msg, ← dhToken P st t)
  | .psk =>
    let psk :: psks := st.psks | throw .missingPsk
    pure (msg, mixKeyAndHash P { st with psks } psk)
  | .ekem =>
    let .kem ekem _ := P.exchange | throw .wrongExchange
    let (ct, msg) ← take msg ekem.ctLen
    let k ← ekem.decap (← need st.e "e").priv ct
    pure (msg, mixKey P (mixHash P st ct) k)
  | .skem =>
    let .kem _ skem := P.exchange | throw .wrongExchange
    let (ect, msg) ← take msg (skem.ctLen + if st.ss.cs.hasKey then 16 else 0)
    let (ct, st) ← decryptAndHash P st ect
    let k ← skem.decap (← need st.s "s").priv ct
    pure (msg, mixKeyAndHash P st k)

def readTokens (st : HandshakeState) (msg : ByteArray) : List Token → Result (ByteArray × HandshakeState)
  | [] => pure (msg, st)
  | t :: ts => do
    let (msg, st) ← readToken P st msg t
    readTokens st msg ts

/-- Pre-messages carry public keys only: `e` the ephemeral (`false`), `s` the static (`true`). -/
def preKey : Token → Option Bool
  | .e => some false
  | .s => some true
  | _ => none

/-- A pre-message key is the sender's own when this party sent it, otherwise the remote one. -/
def preMessageKey (sender : Bool) (st : HandshakeState) (static : Bool) : Result ByteArray :=
  if sender == st.initiator then (need (ownKey st static) "pre-message key").map (·.pub)
  else need (peerKey st static) "pre-message key"

def preMessage (sender : Bool) (st : HandshakeState) (t : Token) : Result HandshakeState :=
  match preKey t with
  | none => throw (.invalidPattern "pre-message token")
  | some static => (preMessageKey sender st static).map fun key =>
    let st := mixHash P st key
    if !static && P.pattern.hasPsk then mixKey P st key else st

def isFinished (st : HandshakeState) : Bool := st.msgIndex ≥ P.pattern.messages.length

def currentMessage (st : HandshakeState) : Result (List Token) := do
  if isFinished P st then throw .handshakeFinished
  pure (P.pattern.messages.getD st.msgIndex [])

def writeMessage (st : HandshakeState) (payload : ByteArray) : Result (ByteArray × HandshakeState) := do
  let tokens ← currentMessage P st
  if P.pattern.initiatorSends st.msgIndex != st.initiator then throw .notMyTurn
  let (buf, st) ← writeTokens P st tokens
  let (ct, st) ← encryptAndHash P st payload
  let msg := buf ++ ct
  if msg.size > maxMessageLen then throw .messageTooLong
  pure (msg, { st with msgIndex := st.msgIndex + 1 })

def readMessage (st : HandshakeState) (msg : ByteArray) : Result (ByteArray × HandshakeState) := do
  let tokens ← currentMessage P st
  if P.pattern.initiatorSends st.msgIndex == st.initiator then throw .notMyTurn
  if msg.size > maxMessageLen then throw .messageTooLong
  let (rest, st) ← readTokens P st msg tokens
  let (pt, st) ← decryptAndHash P st rest
  pure (pt, { st with msgIndex := st.msgIndex + 1 })

def handshakeHash (st : HandshakeState) : ByteArray := st.ss.h

end HandshakeState

def protocolNameValid (name : String) : Bool :=
  name.utf8ByteSize ≤ 255 &&
    name.all fun c => c.isAlphanum || c == '_' || c == '+' || c == '/'

/-- What `initialize` refuses: an invalid pattern, a pattern of the wrong kind for the exchange,
or a protocol name outside Noise's rules. -/
def HandshakeState.check (P : Protocol) : Result Unit :=
  match validate P.pattern with
  | .error r => throw (.invalidPattern r)
  | .ok () => do
  match P.exchange with
  | .dh _ => if P.pattern.isKEM then throw .wrongExchange
  | .kem _ _ => if P.pattern.messages.any (·.any Token.isDH) then throw .wrongExchange
  if !protocolNameValid P.name then throw (.invalidPattern "protocol name")

def HandshakeState.ofConfig (P : Protocol) (cfg : Config) : HandshakeState :=
  { initiator := cfg.initiator,
    ss := (SymmetricState.init P.hash P.name.toUTF8).mixHash P.hash cfg.prologue,
    s := cfg.s, e := cfg.e, rs := cfg.rs, re := cfg.re, psks := cfg.psks, seeds := cfg.seeds,
    draws := 0, msgIndex := 0 }

def HandshakeState.preMessages (P : Protocol) (sender : Bool) (st : HandshakeState) :
    List Token → Result HandshakeState
  | [] => pure st
  | t :: ts => do preMessages P sender (← HandshakeState.preMessage P sender st t) ts

/-- Noise §5.3 `Initialize`: hash the protocol name, the prologue and the pre-message keys. -/
def HandshakeState.initialize (P : Protocol) (cfg : Config) : Result HandshakeState := do
  HandshakeState.check P
  let st ← HandshakeState.preMessages P true (HandshakeState.ofConfig P cfg) P.pattern.preInitiator
  HandshakeState.preMessages P false st P.pattern.preResponder

namespace Protocol

variable (P : Protocol)

/-- A static key pair from its private key: a DH key, or a key for the static KEM. -/
def staticFromPrivate (priv : ByteArray) : Result KeyPair :=
  match P.exchange with
  | .dh d => d.ofPrivate priv
  | .kem _ s => s.ofPrivate priv

def ephemeralFromPrivate (priv : ByteArray) : Result KeyPair :=
  match P.exchange with
  | .dh d => d.ofPrivate priv
  | .kem e _ => e.ofPrivate priv

end Protocol

end Uproar
