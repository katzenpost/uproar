/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Uproar.Transport

/-! # Running both halves of a handshake in one place

`run` plays both parties of a protocol against each other: what the tests and the example need,
and the shape the correctness theorems are stated over. -/

namespace Uproar

inductive Party where
  | hs (st : HandshakeState)
  | tr (t : TransportState)

namespace Party

variable (P : Protocol)

def write (p : Party) (pt : ByteArray) : Result (ByteArray × Party) := do
  match p with
  | .hs st =>
    let (ct, st) ← HandshakeState.writeMessage P st pt
    if HandshakeState.isFinished P st then pure (ct, .tr (← TransportState.ofHandshake P st))
    else pure (ct, .hs st)
  | .tr t => do let (ct, t) ← t.writeMessage P.cipher pt; pure (ct, .tr t)

def read (p : Party) (ct : ByteArray) : Result (ByteArray × Party) := do
  match p with
  | .hs st =>
    let (pt, st) ← HandshakeState.readMessage P st ct
    if HandshakeState.isFinished P st then pure (pt, .tr (← TransportState.ofHandshake P st))
    else pure (pt, .hs st)
  | .tr t => do let (pt, t) ← t.readMessage P.cipher ct; pure (pt, .tr t)

def handshakeHash : Party → ByteArray
  | .hs st => st.handshakeHash
  | .tr t => t.handshakeHash

end Party

/-- Who sends message `i`: messages alternate from the initiator, and in a one-way pattern the
initiator sends everything, transport messages included. -/
def initiatorSendsAt (p : HandshakePattern) (i : Nat) : Bool := p.oneWay || i % 2 == 0

/-- Exchange `payloads` between the two parties, returning the ciphertexts and both parties. -/
def exchange (P : Protocol) (ini res : Party) (payloads : List ByteArray) :
    Result (List ByteArray × Party × Party) := do
  let mut ini := ini
  let mut res := res
  let mut cts := #[]
  for h : i in [0:payloads.length] do
    let payload := payloads[i]
    let fromInit := initiatorSendsAt P.pattern i
    let (sender, receiver) := if fromInit then (ini, res) else (res, ini)
    let (ct, sender) ← sender.write P payload
    let (pt, receiver) ← receiver.read P ct
    if pt != payload then throw .decryptFailed
    cts := cts.push ct
    (ini, res) := if fromInit then (sender, receiver) else (receiver, sender)
  pure (cts.toList, ini, res)

end Uproar
