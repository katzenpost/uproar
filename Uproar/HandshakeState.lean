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

def nextSeed (st : HandshakeState) : Vector UInt8 32 × HandshakeState :=
  (st.seeds st.draws, { st with draws := st.draws + 1 })

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
    let (seed, st) := st.nextSeed
    match P.exchange with
    | .dh d => pure (d.ofSeed seed, st)
    | .kem e _ => do pure (← e.ofSeed seed, st)

def need {α} (x : Option α) (which : String) : Result α :=
  match x with
  | some a => pure a
  | none => throw (.missingKey which)

/-- The keys behind a DH token, from this party's side. -/
def dhToken (st : HandshakeState) (t : Token) : Result HandshakeState := do
  let .dh d := P.exchange | throw .wrongExchange
  let (mine, theirs) ← match t, st.initiator with
    | .ee, _ => pure ((← need st.e "e").priv, ← need st.re "re")
    | .ss, _ => pure ((← need st.s "s").priv, ← need st.rs "rs")
    | .es, true | .se, false => pure ((← need st.e "e").priv, ← need st.rs "rs")
    | .es, false | .se, true => pure ((← need st.s "s").priv, ← need st.re "re")
    | _, _ => throw (.invalidPattern "not a DH token")
  pure (mixKey P st (← d.dh mine theirs))

def writeToken (acc : ByteArray × HandshakeState) (t : Token) :
    Result (ByteArray × HandshakeState) := do
  let (buf, st) := acc
  match t with
  | .e =>
    let (kp, st) ← generateE P st
    let st := mixHash P { st with e := some kp } kp.pub
    let st := if P.pattern.hasPsk then mixKey P st kp.pub else st
    pure (buf ++ kp.pub, st)
  | .s =>
    let (ct, st) ← encryptAndHash P st (← need st.s "s").pub
    pure (buf ++ ct, st)
  | .ee | .es | .se | .ss => pure (buf, ← dhToken P st t)
  | .psk =>
    let psk :: psks := st.psks | throw .missingPsk
    pure (buf, mixKeyAndHash P { st with psks } psk)
  | .ekem =>
    let .kem ekem _ := P.exchange | throw .wrongExchange
    let (seed, st) := st.nextSeed
    let (ct, k) ← ekem.encap (← need st.re "re") seed
    pure (buf ++ ct, mixKey P (mixHash P st ct) k)
  | .skem =>
    let .kem _ skem := P.exchange | throw .wrongExchange
    let (seed, st) := st.nextSeed
    let (ct, k) ← skem.encap (← need st.rs "rs") seed
    let (ect, st) ← encryptAndHash P st ct
    pure (buf ++ ect, mixKeyAndHash P st k)

def take (msg : ByteArray) (n : Nat) : Result (ByteArray × ByteArray) :=
  if msg.size < n then throw .messageTooShort
  else pure (msg.extract 0 n, msg.extract n msg.size)

def readToken (acc : ByteArray × HandshakeState) (t : Token) :
    Result (ByteArray × HandshakeState) := do
  let (msg, st) := acc
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

/-- A pre-message key is the sender's own when this party sent it, otherwise the remote one. -/
def preMessage (sender : Bool) (st : HandshakeState) (t : Token) : Result HandshakeState := do
  let mine := sender == st.initiator
  let key ← match t, mine with
    | .e, true => pure (← need st.e "e").pub
    | .s, true => pure (← need st.s "s").pub
    | .e, false => need st.re "re"
    | .s, false => need st.rs "rs"
    | _, _ => throw (.invalidPattern "pre-message token")
  let st := mixHash P st key
  pure (if t == .e && P.pattern.hasPsk then mixKey P st key else st)

def isFinished (st : HandshakeState) : Bool := st.msgIndex ≥ P.pattern.messages.length

def currentMessage (st : HandshakeState) : Result (List Token) := do
  if isFinished P st then throw .handshakeFinished
  pure (P.pattern.messages.getD st.msgIndex [])

def writeMessage (st : HandshakeState) (payload : ByteArray) : Result (ByteArray × HandshakeState) := do
  let tokens ← currentMessage P st
  if P.pattern.initiatorSends st.msgIndex != st.initiator then throw .notMyTurn
  let (buf, st) ← tokens.foldlM (writeToken P) (ByteArray.empty, st)
  let (ct, st) ← encryptAndHash P st payload
  let msg := buf ++ ct
  if msg.size > maxMessageLen then throw .messageTooLong
  pure (msg, { st with msgIndex := st.msgIndex + 1 })

def readMessage (st : HandshakeState) (msg : ByteArray) : Result (ByteArray × HandshakeState) := do
  let tokens ← currentMessage P st
  if P.pattern.initiatorSends st.msgIndex == st.initiator then throw .notMyTurn
  if msg.size > maxMessageLen then throw .messageTooLong
  let (rest, st) ← tokens.foldlM (readToken P) (msg, st)
  let (pt, st) ← decryptAndHash P st rest
  pure (pt, { st with msgIndex := st.msgIndex + 1 })

def handshakeHash (st : HandshakeState) : ByteArray := st.ss.h

end HandshakeState

def protocolNameValid (name : String) : Bool :=
  name.utf8ByteSize ≤ 255 &&
    name.all fun c => c.isAlphanum || c == '_' || c == '+' || c == '/'

/-- Noise §5.3 `Initialize`: hash the protocol name, the prologue and the pre-message keys. -/
def HandshakeState.initialize (P : Protocol) (cfg : Config) : Result HandshakeState := do
  if let .error r := validate P.pattern then throw (.invalidPattern r)
  match P.exchange with
  | .dh _ => if P.pattern.isKEM then throw .wrongExchange
  | .kem _ _ => if P.pattern.messages.any (·.any Token.isDH) then throw .wrongExchange
  if !protocolNameValid P.name then throw (.invalidPattern "protocol name")
  let ss := (SymmetricState.init P.hash P.name.toUTF8).mixHash P.hash cfg.prologue
  let st : HandshakeState := {
    initiator := cfg.initiator, ss, s := cfg.s, e := cfg.e, rs := cfg.rs,
    re := cfg.re, psks := cfg.psks, seeds := cfg.seeds, draws := 0, msgIndex := 0 }
  let st ← P.pattern.preInitiator.foldlM (HandshakeState.preMessage P true) st
  P.pattern.preResponder.foldlM (HandshakeState.preMessage P false) st

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
