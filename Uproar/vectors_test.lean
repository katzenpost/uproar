import Lean.Data.Json

import Uproar.Suites
import Uproar.Session
import CryptWalker.Util.newhex

open Lean
open Uproar
open CryptWalker.Util.newhex

/-! Runs the cacophony and snow vector files: both parties are built from the vector's keys, every
message is written by its sender and checked against the expected ciphertext, read back by the
other party and checked against the payload, and the handshake hash is compared when given. -/

def hexOf (j : Json) (k : String) : Except String (Option ByteArray) :=
  match j.getObjVal? k with
  | .error _ => pure none
  | .ok v => do
    match hexStringToByteArray (← v.getStr?) with
    | some b => pure (some b)
    | none => throw s!"{k} is not valid hex"

def hexList (j : Json) (k : String) : Except String (List ByteArray) :=
  match j.getObjVal? k with
  | .error _ => pure []
  | .ok v => do
    (← v.getArr?).toList.mapM fun x => do
      match hexStringToByteArray (← x.getStr?) with
      | some b => pure b
      | none => throw s!"{k} is not valid hex"

def lift {α} : Result α → Except String α
  | .ok a => pure a
  | .error e => throw (reprStr e)

def config (P : Protocol) (j : Json) (side : String) (initiator : Bool) : Except String Config := do
  let s ← (← hexOf j s!"{side}_static").mapM (lift ∘ P.staticFromPrivate)
  let e ← (← hexOf j s!"{side}_ephemeral").mapM (lift ∘ P.ephemeralFromPrivate)
  pure {
    initiator, s, e
    prologue := (← hexOf j s!"{side}_prologue").getD ByteArray.empty
    rs := ← hexOf j s!"{side}_remote_static"
    psks := ← hexList j s!"{side}_psks"
    seeds := fun _ => Vector.replicate 32 0 }

def runVector (P : Protocol) (j : Json) : Except String Unit := do
  let mut ini := Party.hs (← lift (HandshakeState.initialize P (← config P j "init" true)))
  let mut res := Party.hs (← lift (HandshakeState.initialize P (← config P j "resp" false)))
  let msgs ← (← j.getObjVal? "messages").getArr?
  for h : i in [0:msgs.size] do
    let m := msgs[i]
    let some payload ← hexOf m "payload" | throw "payload missing"
    let some expected ← hexOf m "ciphertext" | throw "ciphertext missing"
    let fromInit := initiatorSendsAt P.pattern i
    let (sender, receiver) := if fromInit then (ini, res) else (res, ini)
    let (ct, sender) ← lift (sender.write P payload)
    if ct != expected then throw s!"message {i}: ciphertext mismatch"
    let (pt, receiver) ← lift (receiver.read P ct)
    if pt != payload then throw s!"message {i}: payload mismatch"
    (ini, res) := if fromInit then (sender, receiver) else (receiver, sender)
  if let some hh ← hexOf j "handshake_hash" then
    if ini.handshakeHash != hh || res.handshakeHash != hh then throw "handshake hash mismatch"

def runFile (path : String) : IO (Nat × Nat × Nat) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let vs ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "vectors")).getArr?)
  let mut passed := 0
  let mut skipped := 0
  let mut failed := 0
  for v in vs do
    let name := (v.getObjValD "protocol_name").getStr?.toOption.getD "?"
    match Suites.protocolByName name with
    | none => skipped := skipped + 1
    | some P =>
      match runVector P v with
      | .ok () => passed := passed + 1
      | .error e =>
        failed := failed + 1
        IO.println s!"  FAIL  {name}: {e}"
  IO.println s!"{path}: {passed}/{passed + failed} passed, {skipped} skipped (unsupported algorithms)"
  pure (passed, skipped, failed)

def main : IO UInt32 := do
  let (_, _, f1) ← runFile "testdata/cacophony.txt"
  let (_, _, f2) ← runFile "testdata/snow.txt"
  pure (if f1 + f2 == 0 then 0 else 1)
