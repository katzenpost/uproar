/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Uproar.Crypto

/-! # Honest key pairs

A key pair crosses the handshake as bytes. It is honest when its private key decodes and its
public key is the one that private key determines (for a NIKE), or one its private key
decapsulates for (for a KEM). Honest DH key pairs agree on their shared secret, and an honest KEM
key pair decapsulates whatever is encapsulated to it from a `Reliable` state. -/

namespace Except

theorem bind_eq_ok {ε α β} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x.bind f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [Except.bind]

theorem map_eq_ok {ε α β} {x : Except ε α} {f : α → β} {b : β} :
    x.map f = .ok b ↔ ∃ a, x = .ok a ∧ f a = b := by
  cases x <;> simp [Except.map]

end Except

namespace Uproar

open CryptWalker.Util.Bytes (ofVector toVecN size_ofVector toVecN_ofVector)

namespace DH

variable (D : DH)

def Honest (kp : KeyPair) : Prop :=
  ∃ sk, D.decodePriv kp.priv = .ok sk ∧
    kp.pub = ofVector (D.nike.encodePublicKey (D.nike.derivePublicKey sk))

theorem decodePriv_encode (sk : D.nike.PrivateKey) :
    D.decodePriv (ofVector (D.nike.encodePrivateKey sk)) = .ok sk := by
  unfold decodePriv
  rw [if_pos (size_ofVector _), toVecN_ofVector, D.nike.decode_encode_priv]
  rfl

theorem ofSeed_honest (seed : Vector UInt8 32) : D.Honest (D.ofSeed seed) :=
  ⟨_, D.decodePriv_encode _, rfl⟩

theorem ofPrivate_honest {b : ByteArray} {kp : KeyPair} (h : D.ofPrivate b = .ok kp) :
    D.Honest kp := by
  unfold ofPrivate at h
  cases hd : D.decodePriv b with
  | error e => rw [hd] at h; cases h
  | ok sk =>
    rw [hd] at h
    cases h
    exact ⟨sk, hd, rfl⟩

theorem size_pub {kp : KeyPair} (h : D.Honest kp) : kp.pub.size = D.pubLen := by
  obtain ⟨_, _, hp⟩ := h
  rw [hp, size_ofVector]; rfl

theorem decodePub_encode (sk : D.nike.PrivateKey) :
    D.decodePub (ofVector (D.nike.encodePublicKey (D.nike.derivePublicKey sk))) =
      .ok ⟨D.nike.derivePublicKey sk, D.nike.derive_safe sk⟩ := by
  unfold decodePub
  rw [if_pos (size_ofVector _), toVecN_ofVector, D.nike.decode_encode_pub]
  simp only
  rw [dif_pos (D.nike.derive_safe sk)]
  rfl

/-- `DH(a, B)` for an honest `B` is the group action of `a`'s scalar on `B`'s public key. -/
theorem dh_honest {a b : KeyPair} {ska skb : D.nike.PrivateKey}
    (ha : D.decodePriv a.priv = .ok ska)
    (hb : b.pub = ofVector (D.nike.encodePublicKey (D.nike.derivePublicKey skb))) :
    D.dh a.priv b.pub = .ok (ofVector (D.nike.encodeSharedSecret
      (D.nike.groupAction ska ⟨D.nike.derivePublicKey skb, D.nike.derive_safe skb⟩))) := by
  unfold dh
  rw [ha, hb, D.decodePub_encode]
  rfl

/-- Honest parties agree on `DH`. -/
theorem dh_comm {a b : KeyPair} (ha : D.Honest a) (hb : D.Honest b) :
    D.dh a.priv b.pub = D.dh b.priv a.pub := by
  obtain ⟨ska, hda, hpa⟩ := ha
  obtain ⟨skb, hdb, hpb⟩ := hb
  rw [D.dh_honest hda hpb, D.dh_honest hdb hpa, D.nike.commutes]

end DH

namespace KEMFn

variable (K : KEMFn)

/-- Round trip for a specific key pair, the shape `KEM.generate` guarantees. -/
def RoundTrips (pk : K.kem.PublicKey) (sk : K.kem.PrivateKey) : Prop :=
  ∀ s, K.kem.Reliable s → ∀ c k s', K.kem.encap pk s = .ok (c, k) s' →
    ∀ t, ∃ t', K.kem.decap sk c t = .ok k t'

def Honest (kp : KeyPair) : Prop :=
  ∃ sk pk, K.decodePriv kp.priv = .ok sk ∧ kp.pub = ofVector (K.kem.encodePublicKey pk) ∧
    K.RoundTrips pk sk

theorem decodePriv_encode (sk : K.kem.PrivateKey) :
    K.decodePriv (ofVector (K.kem.encodePrivateKey sk)) = .ok sk := by
  unfold decodePriv
  rw [if_pos (size_ofVector _), toVecN_ofVector, K.kem.decode_encode_priv]
  rfl

theorem ofSeed_honest {seed : Vector UInt8 32} {kp : KeyPair} (h : K.ofSeed seed = .ok kp) :
    K.Honest kp := by
  unfold ofSeed at h
  cases hg : K.run K.kem.generate seed with
  | error e => rw [hg] at h; cases h
  | ok r =>
    obtain ⟨pk, sk, hrt⟩ := r
    rw [hg] at h
    cases h
    exact ⟨sk, pk, K.decodePriv_encode sk, rfl, hrt⟩

theorem ofPrivate_honest {b : ByteArray} {kp : KeyPair} (h : K.ofPrivate b = .ok kp) :
    K.Honest kp := by
  unfold ofPrivate at h
  cases hd : K.decodePriv b with
  | error e => rw [hd] at h; cases h
  | ok sk =>
    rw [hd] at h
    cases h
    exact ⟨sk, _, hd, rfl, K.kem.honestRoundTrip sk⟩

theorem size_pub {kp : KeyPair} (h : K.Honest kp) : kp.pub.size = K.pubLen := by
  obtain ⟨_, _, _, hp, _⟩ := h
  rw [hp, size_ofVector]; rfl

theorem decodePub_encode (pk : K.kem.PublicKey) :
    K.decodePub (ofVector (K.kem.encodePublicKey pk)) = .ok pk := by
  unfold decodePub
  rw [if_pos (size_ofVector _), toVecN_ofVector, K.kem.decode_encode_pub]
  rfl

theorem decodeCt_encode (c : K.kem.Ciphertext) :
    K.decodeCt (ofVector (K.kem.encodeCiphertext c)) = .ok c := by
  unfold decodeCt
  rw [if_pos (size_ofVector _), toVecN_ofVector, K.kem.decode_encode_ct]
  rfl

theorem run_eq_ok {α} {x : EStateM CryptWalker.KEM.KEM.KEMError K.kem.State α}
    {seed : Vector UInt8 32} {a : α} (h : K.run x seed = .ok a) :
    ∃ s', x (K.kem.stateFromSeed seed) = .ok a s' := by
  unfold run at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨_, by assumption⟩
  · cases h
  · cases h

theorem size_encap {pk ct k : ByteArray} {seed : Vector UInt8 32}
    (h : K.encap pk seed = .ok (ct, k)) : ct.size = K.ctLen := by
  obtain ⟨_, -, h⟩ := Except.bind_eq_ok.mp h
  obtain ⟨⟨c, k'⟩, -, h⟩ := Except.map_eq_ok.mp h
  simp only [Prod.mk.injEq] at h
  rw [← h.1, size_ofVector]; rfl

/-- What is encapsulated to an honest key pair from a `Reliable` state decapsulates back. -/
theorem decap_encap {kp : KeyPair} {ct k : ByteArray} {seed : Vector UInt8 32}
    (hk : K.Honest kp) (hrel : K.kem.Reliable (K.kem.stateFromSeed seed))
    (h : K.encap kp.pub seed = .ok (ct, k)) : K.decap kp.priv ct = .ok k := by
  obtain ⟨sk, pk, hsk, hpk, hrt⟩ := hk
  obtain ⟨pk', hpk', h⟩ := Except.bind_eq_ok.mp h
  rw [hpk, K.decodePub_encode] at hpk'
  cases hpk'
  obtain ⟨⟨c, k'⟩, hrun, h⟩ := Except.map_eq_ok.mp h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s', hencap⟩ := K.run_eq_ok hrun
  obtain ⟨t', ht'⟩ := hrt _ hrel c k' s' hencap (K.kem.stateFromSeed (Vector.replicate 32 0))
  unfold decap
  rw [hsk]
  show (K.decodeCt (ofVector (K.kem.encodeCiphertext c))).bind _ = _
  rw [K.decodeCt_encode]
  show Except.map _ (K.run (K.kem.decap sk c) (Vector.replicate 32 0)) = _
  unfold run
  rw [ht']
  rfl

end KEMFn

end Uproar
