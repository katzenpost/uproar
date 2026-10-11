import Uproar.Suites
import Uproar.Session
import Uproar.IO

open Uproar

/-! PQ Noise self-test: pqXX under every KEM in CryptWalker's registry. Both parties are built from
fresh keys, run the handshake and a round of transport messages, and must agree on the handshake
hash; a flipped ciphertext bit must be rejected. -/

def seedsFrom (label : String) : Nat → Vector UInt8 32 := seedStream label.toUTF8

def needsStatic (p : HandshakePattern) (initiator : Bool) : Bool :=
  (if initiator then p.preInitiator else p.preResponder).contains .s ||
    (p.messages.zipIdx.any fun (m, i) => p.initiatorSends i == initiator && m.contains .s)

def configs (P : Protocol) (label : String) : Result (Config × Config) := do
  let p := P.pattern
  let iS ← if needsStatic p true then
    some <$> P.staticFromPrivate (← staticKey (label ++ "/is")) else pure none
  let rS ← if needsStatic p false then
    some <$> P.staticFromPrivate (← staticKey (label ++ "/rs")) else pure none
  let psks := (p.messages.flatten.filter (· == .psk)).zipIdx.map fun (_, i) =>
    CryptWalker.Util.Bytes.ofVector (seedsFrom (label ++ "/psk") i)
  pure ({ initiator := true, s := iS, rs := if p.preResponder.contains .s then rS.map (·.pub) else none,
          psks, prologue := "uproar".toUTF8, seeds := seedsFrom (label ++ "/i") },
        { initiator := false, s := rS, rs := if p.preInitiator.contains .s then iS.map (·.pub) else none,
          psks, prologue := "uproar".toUTF8, seeds := seedsFrom (label ++ "/r") })
where
  staticKey (l : String) : Result ByteArray :=
    match P.exchange with
    | .dh d => pure (d.ofSeed (seedsFrom l 0)).priv
    | .kem _ s => do pure (← s.ofSeed (seedsFrom l 0)).priv

def flipLast (b : ByteArray) : ByteArray :=
  if b.size = 0 then b else b.set! (b.size - 1) (b.get! (b.size - 1) ^^^ 1)

def keyed : Party → Bool
  | .hs st => st.ss.cs.hasKey
  | .tr _ => true

/-- One pass over the messages; before each delivery, a copy of the receiver must reject the
message with its last bit flipped whenever its payload is encrypted. -/
def roundTrip (P : Protocol) (label : String) : Except String Unit := do
  let lift {α} (x : Result α) : Except String α := x.mapError reprStr
  let (ci, cr) ← lift (configs P label)
  let mut ini := Party.hs (← lift (HandshakeState.initialize P ci))
  let mut res := Party.hs (← lift (HandshakeState.initialize P cr))
  for i in [0:P.pattern.messages.length + 3] do
    let payload := s!"message {i}".toUTF8
    let fromInit := initiatorSendsAt P.pattern i
    let (sender, receiver) := if fromInit then (ini, res) else (res, ini)
    let (ct, sender) ← lift (sender.write P payload)
    let (pt, receiver') ← lift (receiver.read P ct)
    if pt != payload then throw s!"message {i}: payload mismatch"
    if keyed receiver' then
      if let .ok _ := receiver.read P (flipLast ct) then throw s!"tampered message {i} accepted"
    (ini, res) := if fromInit then (sender, receiver') else (receiver', sender)
  if ini.handshakeHash != res.handshakeHash then throw "handshake hashes differ"

/-- pqXX over each KEM in CryptWalker's registry. Patterns, ciphers and hashes are covered by the
clatter vectors. -/
def kemProtocols : List Protocol :=
  Suites.kems.map fun k => ⟨Patterns.pqXX, .kem k k, Suites.chaChaPoly, Suites.blake2s⟩

def bad (preResponder : List Token) (messages : List (List Token)) : HandshakePattern :=
  { base := "bad", preInitiator := [], preResponder, messages }

/-- Patterns the validator must refuse. -/
def invalidPatterns : List (String × HandshakePattern) :=
  [("skem before ekem", bad [.s] [[.e], [.skem, .ekem]]),
   ("ekem after a public key", bad [] [[.e], [.s, .ekem]]),
   ("ekem without a peer ephemeral", bad [] [[.ekem]]),
   ("skem without a peer static", bad [] [[.e], [.ekem, .skem]]),
   ("DH and KEM mixed", bad [] [[.e], [.ekem, .e, .ee]]),
   ("e sent twice", bad [] [[.e], [.ekem], [.e]]),
   ("psk before fresh randomness", bad [.s] [[.psk, .s], [.e]]),
   ("DH repeated", bad [] [[.e], [.e, .ee, .ee]]),
   ("payload after se without ee", bad [] [[.e], [.s], [.s, .se]])]

def main : IO UInt32 := do
  let mut failed := 0
  let mut passed := 0
  for P in kemProtocols do
    match roundTrip P P.name with
    | .ok () => passed := passed + 1
    | .error e => failed := failed + 1; IO.println s!"  FAIL  {P.name}: {e}"
  IO.println s!"pq handshakes: {passed}/{passed + failed} passed"
  let mut rejected := 0
  for (why, p) in invalidPatterns do
    if isValid p then failed := failed + 1; IO.println s!"  FAIL  accepted invalid pattern: {why}"
    else rejected := rejected + 1
  IO.println s!"invalid patterns: {rejected}/{invalidPatterns.length} rejected"
  pure (if failed == 0 then 0 else 1)
