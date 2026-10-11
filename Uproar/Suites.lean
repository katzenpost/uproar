/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Uproar.HandshakeState
import CryptWalker.Cipher.ChaChaPoly
import CryptWalker.Cipher.AESGCM
import CryptWalker.Hash.Sha2
import CryptWalker.Hash.Sha512
import CryptWalker.Hash.HKDF
import CryptWalker.Hash.Blake2s
import CryptWalker.NIKE.X25519_montgomery_ladder
import CryptWalker.KEM.MLKEM.MLKEM768
import CryptWalker.KEM.Schemes

/-! # Concrete primitives, under their Noise names -/

namespace Uproar.Suites

open Uproar

def chaChaPoly : Cipher :=
  { aead := CryptWalker.Cipher.ChaChaPoly.Scheme, name := "ChaChaPoly",
    keySize_eq := rfl, nonceSize_eq := rfl, tagSize_eq := rfl, bigEndianNonce := false }

def aesGCM : Cipher :=
  { aead := CryptWalker.Cipher.AESGCM.Scheme, name := "AESGCM",
    keySize_eq := rfl, nonceSize_eq := rfl, tagSize_eq := rfl, bigEndianNonce := true }

def sha256 : HashFn := ⟨CryptWalker.Hash.Sha2.Sha256.Scheme, "SHA256"⟩
def sha512 : HashFn := ⟨CryptWalker.Hash.Sha512.Scheme, "SHA512"⟩
def blake2b : HashFn := ⟨CryptWalker.Hash.HKDF.blake2b_hashScheme, "BLAKE2b"⟩
def blake2s : HashFn := ⟨CryptWalker.Hash.Blake2s.Scheme, "BLAKE2s"⟩

/-- X25519, which the Noise spec names `25519`. -/
def x25519 : DH := ⟨CryptWalker.NIKE.X25519_montgomery_ladder.LadderScheme, "25519"⟩

def mlkem768 : KEMFn := ⟨CryptWalker.KEM.MLKEM768.kemMLKEM768Seed, "MLKEM768"⟩

/-- CryptWalker's split-PRF combination of X25519 and ML-KEM-768: a KEM like any other. -/
def mlkem768X25519 : KEMFn := ⟨CryptWalker.KEM.kemMLKEM768X25519, "MLKEM768X25519"⟩

def ciphers : List Cipher := [chaChaPoly, aesGCM]
def hashes : List HashFn := [sha256, sha512, blake2b, blake2s]
def dhs : List DH := [x25519]
def kems : List KEMFn := [mlkem768, mlkem768X25519]

def exchangeByName (name : String) : Option Exchange :=
  match dhs.find? (·.name == name) with
  | some d => some (.dh d)
  | none =>
    match name.splitOn "+" with
    | [k] => (kems.find? (·.name == k)).map fun k => .kem k k
    | [e, s] =>
      match kems.find? (·.name == e), kems.find? (·.name == s) with
      | some e, some s => some (.kem e s)
      | _, _ => none
    | _ => none

/-- Parse `Noise_<pattern>_<exchange>_<cipher>_<hash>` into a protocol built from the primitives
above, or `none` when any part is unknown. -/
def protocolByName (name : String) : Option Protocol :=
  match name.splitOn "_" with
  | ["Noise", pat, ex, c, h] =>
    match Patterns.byName pat, exchangeByName ex, ciphers.find? (·.name == c),
        hashes.find? (·.name == h) with
    | some pattern, some exchange, some cipher, some hash => some { pattern, exchange, cipher, hash }
    | _, _, _, _ => none
  | _ => none

end Uproar.Suites
