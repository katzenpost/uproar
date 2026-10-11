/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import CryptWalker.Cipher.AEAD
import CryptWalker.Hash.Hash
import CryptWalker.KDF.HKDF
import CryptWalker.NIKE.NIKE
import CryptWalker.KEM.KEM
import CryptWalker.Util.Bytes

/-! # The primitives a Noise protocol is built from

Each is a CryptWalker structure plus the name the Noise protocol string gives it. Keys and
ciphertexts cross the handshake as byte strings and are decoded at the point of use. -/

namespace Uproar

open CryptWalker.Cipher.AEAD (AEAD)
open CryptWalker.Hash.Hash (Hash)
open CryptWalker.NIKE.NIKE (NIKE)
open CryptWalker.KEM.KEM (KEM)
open CryptWalker.Util.Bytes (ofVector toVecN)

inductive NoiseError where
  | decryptFailed
  | nonceExhausted
  | invalidPublicKey
  | invalidPrivateKey
  | invalidCiphertext
  | missingKey (which : String)
  | missingPsk
  | messageTooLong
  | messageTooShort
  | notMyTurn
  | handshakeFinished
  | handshakeUnfinished
  | invalidPattern (reason : String)
  | wrongExchange
  deriving Repr, DecidableEq, Inhabited

abbrev Result := Except NoiseError

def maxMessageLen : Nat := 65535

/-- A Noise cipher: an AEAD with 32-byte keys, 12-byte nonces and 16-byte tags, and the order in
which it lays out the 64-bit counter after four zero bytes. -/
structure Cipher where
  aead : AEAD
  name : String
  keySize_eq : aead.keySize = 32
  nonceSize_eq : aead.nonceSize = 12
  tagSize_eq : aead.tagSize = 16
  bigEndianNonce : Bool

namespace Cipher

variable (C : Cipher)

def nonce (n : Nat) : Vector UInt8 C.aead.nonceSize :=
  let ctr : Vector UInt8 8 := Vector.ofFn fun i : Fin 8 =>
    UInt8.ofNat (n >>> (8 * (if C.bigEndianNonce then 7 - i.val else i.val)))
  (Vector.replicate 4 (0 : UInt8) ++ ctr).cast (by rw [C.nonceSize_eq])

def key (k : Vector UInt8 32) : C.aead.Key := C.aead.keyFromBytes (k.cast C.keySize_eq.symm)

def encrypt (k : Vector UInt8 32) (n : Nat) (ad pt : ByteArray) : ByteArray :=
  C.aead.encrypt (C.key k) (C.nonce n) ad pt

def decrypt (k : Vector UInt8 32) (n : Nat) (ad ct : ByteArray) : Option ByteArray :=
  C.aead.decrypt (C.key k) (C.nonce n) ad ct

/-- Noise §4.2's default REKEY: the first 32 bytes of encrypting 32 zero bytes at the maximum
nonce. -/
def rekey (k : Vector UInt8 32) : Vector UInt8 32 :=
  toVecN 32 (C.encrypt k (2 ^ 64 - 1) ByteArray.empty ⟨Array.replicate 32 0⟩)

end Cipher

structure HashFn where
  hash : Hash
  name : String

namespace HashFn

variable (H : HashFn)

def hashLen : Nat := H.hash.digestSize

def digest (b : ByteArray) : ByteArray := ofVector (H.hash.hash b)

/-- Noise §4.3's `HKDF(ck, ikm, n)`: RFC 5869 with the chaining key as salt and empty info,
returning `n` outputs of `HASHLEN` bytes. -/
def hkdf (ck ikm : ByteArray) (n : Nat) : List ByteArray :=
  let prk := ofVector (CryptWalker.KDF.HKDF.extract H.hash ck ikm)
  let okm := CryptWalker.KDF.HKDF.expand H.hash prk ByteArray.empty (n * H.hashLen)
  (List.range n).map fun i => okm.extract (i * H.hashLen) ((i + 1) * H.hashLen)

end HashFn

structure KeyPair where
  priv : ByteArray
  pub : ByteArray
  deriving Inhabited

structure DH where
  nike : NIKE
  name : String

namespace DH

variable (D : DH)

def pubLen : Nat := D.nike.publicKeySize

def ofSeed (seed : Vector UInt8 32) : KeyPair :=
  let sk := D.nike.privateKeyFromSeed seed
  ⟨ofVector (D.nike.encodePrivateKey sk), ofVector (D.nike.encodePublicKey (D.nike.derivePublicKey sk))⟩

def decodePriv (b : ByteArray) : Result D.nike.PrivateKey :=
  if b.size = D.nike.privateKeySize then
    match D.nike.decodePrivateKey (toVecN _ b) with
    | some sk => pure sk
    | none => throw .invalidPrivateKey
  else throw .invalidPrivateKey

def ofPrivate (b : ByteArray) : Result KeyPair := do
  let sk ← D.decodePriv b
  pure ⟨b, ofVector (D.nike.encodePublicKey (D.nike.derivePublicKey sk))⟩

def decodePub (b : ByteArray) : Result {pk : D.nike.PublicKey // D.nike.Safe pk} :=
  if b.size = D.nike.publicKeySize then
    match D.nike.decodePublicKey (toVecN _ b) with
    | some pk =>
      haveI := D.nike.decSafe
      if h : D.nike.Safe pk then pure ⟨pk, h⟩ else throw .invalidPublicKey
    | none => throw .invalidPublicKey
  else throw .invalidPublicKey

/-- `DH(sk, pk)`, refusing a public key outside the NIKE's safe set. -/
def dh (sk pk : ByteArray) : Result ByteArray :=
  (D.decodePriv sk).bind fun sk => (D.decodePub pk).map fun pk =>
    ofVector (D.nike.encodeSharedSecret (D.nike.groupAction sk pk))

end DH

structure KEMFn where
  kem : KEM
  name : String

namespace KEMFn

variable (K : KEMFn)

def pubLen : Nat := K.kem.publicKeySize

def ctLen : Nat := K.kem.ciphertextSize

def run {α} (x : EStateM CryptWalker.KEM.KEM.KEMError K.kem.State α) (seed : Vector UInt8 32) :
    Result α :=
  match x (K.kem.stateFromSeed seed) with
  | .ok a _ => pure a
  | .error .unsafePublicKey _ => throw .invalidPublicKey
  | .error .badCiphertext _ => throw .invalidCiphertext

def ofSeed (seed : Vector UInt8 32) : Result KeyPair := do
  let ⟨pk, sk, _⟩ ← K.run K.kem.generate seed
  pure ⟨ofVector (K.kem.encodePrivateKey sk), ofVector (K.kem.encodePublicKey pk)⟩

def decodePriv (b : ByteArray) : Result K.kem.PrivateKey :=
  if b.size = K.kem.privateKeySize then
    match K.kem.decodePrivateKey (toVecN _ b) with
    | some sk => pure sk
    | none => throw .invalidPrivateKey
  else throw .invalidPrivateKey

def ofPrivate (b : ByteArray) : Result KeyPair := do
  let sk ← K.decodePriv b
  pure ⟨b, ofVector (K.kem.encodePublicKey (K.kem.derivePublicKey sk))⟩

/-- Encapsulate to `pk` with coins drawn from `seed`, returning `(ciphertext, shared secret)`. -/
def decodePub (b : ByteArray) : Result K.kem.PublicKey :=
  if b.size = K.kem.publicKeySize then
    match K.kem.decodePublicKey (toVecN _ b) with
    | some pk => pure pk
    | none => throw .invalidPublicKey
  else throw .invalidPublicKey

def decodeCt (b : ByteArray) : Result K.kem.Ciphertext :=
  if b.size = K.kem.ciphertextSize then
    match K.kem.decodeCiphertext (toVecN _ b) with
    | some c => pure c
    | none => throw .invalidCiphertext
  else throw .invalidCiphertext

/-- Encapsulate to `pk` with coins drawn from `seed`, returning `(ciphertext, shared secret)`. -/
def encap (pk : ByteArray) (seed : Vector UInt8 32) : Result (ByteArray × ByteArray) :=
  (K.decodePub pk).bind fun pk =>
    (K.run (K.kem.encap pk) seed).map fun (c, k) =>
      (ofVector (K.kem.encodeCiphertext c), ofVector (K.kem.encodePlaintext k))

def decap (sk ct : ByteArray) : Result ByteArray :=
  (K.decodePriv sk).bind fun sk => (K.decodeCt ct).bind fun c =>
    (K.run (K.kem.decap sk c) (Vector.replicate 32 0)).map fun k => ofVector (K.kem.encodePlaintext k)

end KEMFn

/-- What the handshake's asymmetric tokens run on: Diffie-Hellman for Noise, or an ephemeral and
a static KEM for PQ Noise. -/
inductive Exchange where
  | dh (d : DH)
  | kem (ekem skem : KEMFn)

def Exchange.name : Exchange → String
  | .dh d => d.name
  | .kem e s => if e.name = s.name then e.name else e.name ++ "+" ++ s.name

end Uproar
