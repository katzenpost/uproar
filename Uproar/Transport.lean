/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Uproar.HandshakeState

/-! # Transport messages after `Split`

In a one-way pattern only the initiator sends, so the responder gets no sending state. -/

namespace Uproar

structure TransportState where
  send : Option CipherState
  recv : Option CipherState
  handshakeHash : ByteArray

namespace TransportState

def ofHandshake (P : Protocol) (st : HandshakeState) : Result TransportState := do
  if !HandshakeState.isFinished P st then throw .handshakeUnfinished
  let (c1, c2) := st.ss.split P.hash
  let oneWay := P.pattern.oneWay
  pure {
    send := if st.initiator then some c1 else if oneWay then none else some c2
    recv := if st.initiator then (if oneWay then none else some c2) else some c1
    handshakeHash := st.ss.h }

def writeMessage (C : Cipher) (t : TransportState) (pt : ByteArray) : Result (ByteArray × TransportState) := do
  let some cs := t.send | throw .notMyTurn
  if pt.size + 16 > maxMessageLen then throw .messageTooLong
  let (ct, cs) ← cs.encryptWithAd C ByteArray.empty pt
  pure (ct, { t with send := some cs })

def readMessage (C : Cipher) (t : TransportState) (ct : ByteArray) : Result (ByteArray × TransportState) := do
  let some cs := t.recv | throw .notMyTurn
  if ct.size > maxMessageLen then throw .messageTooLong
  let (pt, cs) ← cs.decryptWithAd C ByteArray.empty ct
  pure (pt, { t with recv := some cs })

def rekeySend (C : Cipher) (t : TransportState) : TransportState :=
  { t with send := t.send.map (·.rekey C) }

def rekeyRecv (C : Cipher) (t : TransportState) : TransportState :=
  { t with recv := t.recv.map (·.rekey C) }

end TransportState

end Uproar
