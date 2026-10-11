/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import CryptWalker.Hash.Blake2s
import CryptWalker.Util.Bytes

/-! # Randomness from the operating system

A handshake draws its ephemeral keys and encapsulation coins from a seed stream; here the stream
is keyed BLAKE2s over a counter, under a key read from the OS once. -/

namespace Uproar

def seedStream (key : ByteArray) (i : Nat) : Vector UInt8 32 :=
  CryptWalker.Hash.Blake2s.hashKeyed key ⟨Array.ofFn fun j : Fin 8 => UInt8.ofNat (i >>> (8 * j.val))⟩

def randomSeeds : IO (Nat → Vector UInt8 32) := do
  pure (seedStream (← IO.getRandomBytes 32))

end Uproar
