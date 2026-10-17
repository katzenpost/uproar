/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Uproar.Crypto

/-! # CipherState and SymmetricState (Noise §5.1, §5.2) -/

namespace Uproar

open Cryptlib.Util.Bytes (toVecN)

/-- `2^64 - 1` is reserved: no message is ever sent under it. -/
def maxNonce : Nat := 2 ^ 64 - 1

structure CipherState where
  k : Option (Vector UInt8 32)
  n : Nat

namespace CipherState

def empty : CipherState := ⟨none, 0⟩

def init (k : Vector UInt8 32) : CipherState := ⟨some k, 0⟩

def hasKey (cs : CipherState) : Bool := cs.k.isSome

def encryptWithAd (C : Cipher) (cs : CipherState) (ad pt : ByteArray) :
    Result (ByteArray × CipherState) :=
  match cs.k with
  | none => pure (pt, cs)
  | some k =>
    if cs.n ≥ maxNonce then throw .nonceExhausted
    else pure (C.encrypt k cs.n ad pt, { cs with n := cs.n + 1 })

/-- A failed decryption leaves the nonce where it was. -/
def decryptWithAd (C : Cipher) (cs : CipherState) (ad ct : ByteArray) :
    Result (ByteArray × CipherState) :=
  match cs.k with
  | none => pure (ct, cs)
  | some k =>
    if cs.n ≥ maxNonce then throw .nonceExhausted
    else match C.decrypt k cs.n ad ct with
      | some pt => pure (pt, { cs with n := cs.n + 1 })
      | none => throw .decryptFailed

def rekey (C : Cipher) (cs : CipherState) : CipherState :=
  { cs with k := cs.k.map C.rekey }

end CipherState

structure SymmetricState where
  cs : CipherState
  ck : ByteArray
  h : ByteArray

namespace SymmetricState

variable (C : Cipher) (H : HashFn)

def init (protocolName : ByteArray) : SymmetricState :=
  let h := if protocolName.size ≤ H.hashLen then
      protocolName ++ ⟨Array.replicate (H.hashLen - protocolName.size) 0⟩
    else H.digest protocolName
  ⟨.empty, h, h⟩

def mixHash (ss : SymmetricState) (data : ByteArray) : SymmetricState :=
  { ss with h := H.digest (ss.h ++ data) }

/-- Outputs are truncated to 32 bytes when `HASHLEN` is 64. -/
def mixKey (ss : SymmetricState) (ikm : ByteArray) : SymmetricState :=
  match H.hkdf ss.ck ikm 2 with
  | [ck, k] => { ss with ck, cs := .init (toVecN 32 k) }
  | _ => ss

def mixKeyAndHash (ss : SymmetricState) (ikm : ByteArray) : SymmetricState :=
  match H.hkdf ss.ck ikm 3 with
  | [ck, th, k] => { (mixHash H { ss with ck } th) with cs := .init (toVecN 32 k) }
  | _ => ss

def encryptAndHash (ss : SymmetricState) (pt : ByteArray) : Result (ByteArray × SymmetricState) := do
  let (ct, cs) ← ss.cs.encryptWithAd C ss.h pt
  pure (ct, mixHash H { ss with cs } ct)

def decryptAndHash (ss : SymmetricState) (ct : ByteArray) : Result (ByteArray × SymmetricState) := do
  let (pt, cs) ← ss.cs.decryptWithAd C ss.h ct
  pure (pt, mixHash H { ss with cs } ct)

/-- The initiator-to-responder and responder-to-initiator cipher states. -/
def split (ss : SymmetricState) : CipherState × CipherState :=
  match H.hkdf ss.ck ByteArray.empty 2 with
  | [k1, k2] => (.init (toVecN 32 k1), .init (toVecN 32 k2))
  | _ => (.empty, .empty)

end SymmetricState

end Uproar
