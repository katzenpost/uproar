/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Uproar.SymmetricState

/-! # Decryption undoes encryption, for `CipherState` and `SymmetricState`

Both rest on the AEAD's own `decrypt_encrypt` law: the reader holds the same key and nonce as the
writer, so it recovers the plaintext and advances to the same state. -/

namespace Uproar

theorem Cipher.decrypt_encrypt (C : Cipher) (k : Vector UInt8 32) (n : Nat) (ad pt : ByteArray) :
    C.decrypt k n ad (C.encrypt k n ad pt) = some pt :=
  C.aead.decrypt_encrypt _ _ _ _

theorem Cipher.size_encrypt (C : Cipher) (k : Vector UInt8 32) (n : Nat) (ad pt : ByteArray) :
    (C.encrypt k n ad pt).size = pt.size + 16 := by
  rw [Cipher.encrypt, C.aead.size_encrypt, C.tagSize_eq]

namespace CipherState

theorem decryptWithAd_encryptWithAd (C : Cipher) {cs cs' : CipherState} {ad pt ct : ByteArray}
    (h : cs.encryptWithAd C ad pt = .ok (ct, cs')) : cs.decryptWithAd C ad ct = .ok (pt, cs') := by
  obtain ⟨k, n⟩ := cs
  cases k with
  | none =>
    simp only [encryptWithAd, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | some k =>
    simp only [encryptWithAd] at h
    split at h
    · cases h
    · rename_i hn
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [decryptWithAd, if_neg hn, Cipher.decrypt_encrypt]
      rfl

/-- The ciphertext is the plaintext plus a 16-byte tag once a key is set, the plaintext itself
before. -/
theorem size_encryptWithAd (C : Cipher) {cs cs' : CipherState} {ad pt ct : ByteArray}
    (h : cs.encryptWithAd C ad pt = .ok (ct, cs')) :
    ct.size = pt.size + if cs.hasKey then 16 else 0 := by
  obtain ⟨k, n⟩ := cs
  cases k with
  | none =>
    simp only [encryptWithAd, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [hasKey]
  | some k =>
    simp only [encryptWithAd] at h
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hasKey, Cipher.size_encrypt]

theorem hasKey_encryptWithAd (C : Cipher) {cs cs' : CipherState} {ad pt ct : ByteArray}
    (h : cs.encryptWithAd C ad pt = .ok (ct, cs')) : cs'.hasKey = cs.hasKey := by
  obtain ⟨k, n⟩ := cs
  cases k with
  | none =>
    simp only [encryptWithAd, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
  | some k =>
    simp only [encryptWithAd] at h
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]; rfl

end CipherState

namespace SymmetricState

theorem decryptAndHash_encryptAndHash (C : Cipher) (H : HashFn) {ss ss' : SymmetricState}
    {pt ct : ByteArray} (h : ss.encryptAndHash C H pt = .ok (ct, ss')) :
    ss.decryptAndHash C H ct = .ok (pt, ss') := by
  unfold encryptAndHash at h
  unfold decryptAndHash
  cases he : ss.cs.encryptWithAd C ss.h pt with
  | error e => rw [he] at h; cases h
  | ok r =>
    obtain ⟨ct', cs⟩ := r
    rw [he] at h
    cases h
    rw [CipherState.decryptWithAd_encryptWithAd C he]
    rfl

theorem size_encryptAndHash (C : Cipher) (H : HashFn) {ss ss' : SymmetricState}
    {pt ct : ByteArray} (h : ss.encryptAndHash C H pt = .ok (ct, ss')) :
    ct.size = pt.size + if ss.cs.hasKey then 16 else 0 := by
  unfold encryptAndHash at h
  cases he : ss.cs.encryptWithAd C ss.h pt with
  | error e => rw [he] at h; cases h
  | ok r =>
    obtain ⟨ct', cs⟩ := r
    rw [he] at h
    cases h
    exact CipherState.size_encryptWithAd C he

end SymmetricState

end Uproar
