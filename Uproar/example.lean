import Uproar.Suites
import Uproar.Session
import Uproar.IO
import CryptWalker.Util.newhex

open Uproar

/-! pqXX end to end with randomness from the operating system: once over ML-KEM-768 and once over
CryptWalker's ML-KEM-768 + X25519 combination, then a round of transport messages each way. -/

def run (P : Protocol) : IO Unit := do
  let lift {α} (x : Result α) : IO α := IO.ofExcept (x.mapError reprStr)
  let .kem _ skem := P.exchange | throw (IO.userError "not a KEM protocol")
  let iS ← lift (skem.ofSeed ((← randomSeeds) 0))
  let rS ← lift (skem.ofSeed ((← randomSeeds) 0))
  let ini ← lift (HandshakeState.initialize P
    { initiator := true, s := some iS, seeds := ← randomSeeds })
  let res ← lift (HandshakeState.initialize P
    { initiator := false, s := some rS, seeds := ← randomSeeds })
  let payloads := ["hello", "from", "uproar", "transport to responder", "transport to initiator"]
  let (cts, ini, res) ← lift (exchange P (.hs ini) (.hs res) (payloads.map String.toUTF8))
  IO.println P.name
  for (p, c) in payloads.zip cts do
    IO.println s!"  {p}: {c.size} bytes"
  let same := ini.handshakeHash == res.handshakeHash
  IO.println s!"  handshake hash {CryptWalker.Util.newhex.byteArrayToHex ini.handshakeHash} (agree: {same})"
  if !same then throw (IO.userError "handshake hashes differ")

def main : IO Unit := do
  for name in ["MLKEM768", "MLKEM768X25519"] do
    match Suites.kemByName name with
    | some k => run ⟨Patterns.pqXX, .kem k k, Suites.chaChaPoly, Suites.blake2s⟩
    | none => throw (IO.userError s!"{name} is not registered")
