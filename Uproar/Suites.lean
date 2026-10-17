/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Uproar.HandshakeState
import Cryptlib.Primitives.Cipher.ChaChaPoly
import Cryptlib.Primitives.Cipher.AESGCM
import Cryptlib.Primitives.Hash.Sha2
import Cryptlib.Primitives.Hash.Sha512
import Cryptlib.Primitives.Hash.HKDF
import Cryptlib.Primitives.Hash.Blake2s
import Cryptlib.Primitives.NIKE.X25519_montgomery_ladder
import Cryptlib.Primitives.KEM.Schemes

/-! # Concrete primitives, under their Noise names -/

namespace Uproar.Suites

open Uproar

def chaChaPoly : Cipher :=
  { aead := Cryptlib.Primitives.Cipher.ChaChaPoly.Scheme, name := "ChaChaPoly",
    keySize_eq := rfl, nonceSize_eq := rfl, tagSize_eq := rfl, bigEndianNonce := false }

def aesGCM : Cipher :=
  { aead := Cryptlib.Primitives.Cipher.AESGCM.Scheme, name := "AESGCM",
    keySize_eq := rfl, nonceSize_eq := rfl, tagSize_eq := rfl, bigEndianNonce := true }

def sha256 : HashFn := ⟨Cryptlib.Primitives.Hash.Sha2.Sha256.Scheme, "SHA256"⟩
def sha512 : HashFn := ⟨Cryptlib.Primitives.Hash.Sha512.Scheme, "SHA512"⟩
def blake2b : HashFn := ⟨Cryptlib.Primitives.Hash.HKDF.blake2b_hashScheme, "BLAKE2b"⟩
def blake2s : HashFn := ⟨Cryptlib.Primitives.Hash.Blake2s.Scheme, "BLAKE2s"⟩

/-- X25519, which the Noise spec names `25519`. -/
def x25519 : DH := ⟨Cryptlib.Primitives.NIKE.X25519_montgomery_ladder.LadderScheme, "25519"⟩

def ciphers : List Cipher := [chaChaPoly, aesGCM]
def hashes : List HashFn := [sha256, sha512, blake2b, blake2s]
def dhs : List DH := [x25519]
/-- Every KEM in Cryptlib's registry, under its registry name. -/
def kems : List KEMFn := Cryptlib.Primitives.KEM.registry.map fun e => ⟨e.scheme, e.name⟩

def kemByName (name : String) : Option KEMFn := kems.find? (·.name == name)

def exchangeByName (name : String) : Option Exchange :=
  match dhs.find? (·.name == name) with
  | some d => some (.dh d)
  | none =>
    match name.splitOn "+" with
    | [k] => (kemByName k).map fun k => .kem k k
    | [e, s] =>
      match kemByName e, kemByName s with
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
