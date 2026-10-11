/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

/-! # Handshake patterns (Noise §7, PQ Noise §2)

`messages` alternate between the parties starting with the initiator, except in a one-way
pattern, whose single message is the initiator's. -/

namespace Uproar

inductive Token where
  | e | s | ee | es | se | ss | psk | ekem | skem
  deriving Repr, DecidableEq, Inhabited

def Token.isDH : Token → Bool
  | .ee | .es | .se | .ss => true
  | _ => false

def Token.isKEM : Token → Bool
  | .ekem | .skem => true
  | _ => false

structure HandshakePattern where
  base : String
  modifiers : List String := []
  preInitiator : List Token
  preResponder : List Token
  messages : List (List Token)
  oneWay : Bool := false
  deriving Repr, DecidableEq, Inhabited

namespace HandshakePattern

variable (p : HandshakePattern)

/-- The first modifier joins the base directly, later ones are separated by `+`. -/
def name : String :=
  match p.modifiers with
  | [] => p.base
  | m :: ms => p.base ++ m ++ String.join (ms.map ("+" ++ ·))

def hasPsk : Bool := p.messages.any (·.contains .psk)

def isKEM : Bool := p.messages.any (·.any Token.isKEM)

def initiatorSends (i : Nat) : Bool := p.oneWay || i % 2 == 0

/-- The `pskN` modifier: `psk` opens the first message for `N = 0` and closes message `N`
otherwise. -/
def addPsk (n : Nat) : HandshakePattern :=
  { p with
    modifiers := p.modifiers ++ [s!"psk{n}"]
    messages := if n = 0 then p.messages.modifyHead (.psk :: ·)
      else p.messages.modify (n - 1) (· ++ [.psk]) }

end HandshakePattern

end Uproar
