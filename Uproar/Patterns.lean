/-
SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
SPDX-License-Identifier: AGPL-3.0-only
-/

import Uproar.Pattern

/-! # The named patterns

The classical ones are generated from cacophony's `HandshakePatterns.hs` by
`scripts/gen_patterns_from_cacophony.py`; PSK variants come from `HandshakePattern.addPsk`. -/

namespace Uproar.Patterns

open Uproar

def NN : HandshakePattern :=
  { base := "NN", preInitiator := [], preResponder := [],
    messages := [[.e], [.e, .ee]] }

def KN : HandshakePattern :=
  { base := "KN", preInitiator := [.s], preResponder := [],
    messages := [[.e], [.e, .ee, .se]] }

def NK : HandshakePattern :=
  { base := "NK", preInitiator := [], preResponder := [.s],
    messages := [[.e, .es], [.e, .ee]] }

def KK : HandshakePattern :=
  { base := "KK", preInitiator := [.s], preResponder := [.s],
    messages := [[.e, .es, .ss], [.e, .ee, .se]] }

def NX : HandshakePattern :=
  { base := "NX", preInitiator := [], preResponder := [],
    messages := [[.e], [.e, .ee, .s, .es]] }

def KX : HandshakePattern :=
  { base := "KX", preInitiator := [.s], preResponder := [],
    messages := [[.e], [.e, .ee, .se, .s, .es]] }

def XN : HandshakePattern :=
  { base := "XN", preInitiator := [], preResponder := [],
    messages := [[.e], [.e, .ee], [.s, .se]] }

def IN : HandshakePattern :=
  { base := "IN", preInitiator := [], preResponder := [],
    messages := [[.e, .s], [.e, .ee, .se]] }

def XK : HandshakePattern :=
  { base := "XK", preInitiator := [], preResponder := [.s],
    messages := [[.e, .es], [.e, .ee], [.s, .se]] }

def IK : HandshakePattern :=
  { base := "IK", preInitiator := [], preResponder := [.s],
    messages := [[.e, .es, .s, .ss], [.e, .ee, .se]] }

def XX : HandshakePattern :=
  { base := "XX", preInitiator := [], preResponder := [],
    messages := [[.e], [.e, .ee, .s, .es], [.s, .se]] }

def IX : HandshakePattern :=
  { base := "IX", preInitiator := [], preResponder := [],
    messages := [[.e, .s], [.e, .ee, .se, .s, .es]] }

def N : HandshakePattern :=
  { base := "N", preInitiator := [], preResponder := [.s],
    messages := [[.e, .es]], oneWay := true }

def K : HandshakePattern :=
  { base := "K", preInitiator := [.s], preResponder := [.s],
    messages := [[.e, .es, .ss]], oneWay := true }

def X : HandshakePattern :=
  { base := "X", preInitiator := [], preResponder := [.s],
    messages := [[.e, .es, .s, .ss]], oneWay := true }

def NK1 : HandshakePattern :=
  { base := "NK1", preInitiator := [], preResponder := [.s],
    messages := [[.e], [.e, .ee, .es]] }

def NX1 : HandshakePattern :=
  { base := "NX1", preInitiator := [], preResponder := [],
    messages := [[.e], [.e, .ee, .s], [.es]] }

def X1N : HandshakePattern :=
  { base := "X1N", preInitiator := [], preResponder := [],
    messages := [[.e], [.e, .ee], [.s], [.se]] }

def X1K : HandshakePattern :=
  { base := "X1K", preInitiator := [], preResponder := [.s],
    messages := [[.e, .es], [.e, .ee], [.s], [.se]] }

def XK1 : HandshakePattern :=
  { base := "XK1", preInitiator := [], preResponder := [.s],
    messages := [[.e], [.e, .ee, .es], [.s, .se]] }

def X1K1 : HandshakePattern :=
  { base := "X1K1", preInitiator := [], preResponder := [.s],
    messages := [[.e], [.e, .ee, .es], [.s], [.se]] }

def X1X : HandshakePattern :=
  { base := "X1X", preInitiator := [], preResponder := [],
    messages := [[.e], [.e, .ee, .s, .es], [.s], [.se]] }

def XX1 : HandshakePattern :=
  { base := "XX1", preInitiator := [], preResponder := [],
    messages := [[.e], [.e, .ee, .s], [.es, .s, .se]] }

def X1X1 : HandshakePattern :=
  { base := "X1X1", preInitiator := [], preResponder := [],
    messages := [[.e], [.e, .ee, .s], [.es, .s], [.se]] }

def K1N : HandshakePattern :=
  { base := "K1N", preInitiator := [.s], preResponder := [],
    messages := [[.e], [.e, .ee], [.se]] }

def K1K : HandshakePattern :=
  { base := "K1K", preInitiator := [.s], preResponder := [.s],
    messages := [[.e, .es], [.e, .ee], [.se]] }

def KK1 : HandshakePattern :=
  { base := "KK1", preInitiator := [.s], preResponder := [.s],
    messages := [[.e], [.e, .ee, .se, .es]] }

def K1K1 : HandshakePattern :=
  { base := "K1K1", preInitiator := [.s], preResponder := [.s],
    messages := [[.e], [.e, .ee, .es], [.se]] }

def K1X : HandshakePattern :=
  { base := "K1X", preInitiator := [.s], preResponder := [],
    messages := [[.e], [.e, .ee, .s, .es], [.se]] }

def KX1 : HandshakePattern :=
  { base := "KX1", preInitiator := [.s], preResponder := [],
    messages := [[.e], [.e, .ee, .se, .s], [.es]] }

def K1X1 : HandshakePattern :=
  { base := "K1X1", preInitiator := [.s], preResponder := [],
    messages := [[.e], [.e, .ee, .s], [.se, .es]] }

def I1N : HandshakePattern :=
  { base := "I1N", preInitiator := [], preResponder := [],
    messages := [[.e, .s], [.e, .ee], [.se]] }

def I1K : HandshakePattern :=
  { base := "I1K", preInitiator := [], preResponder := [.s],
    messages := [[.e, .es, .s], [.e, .ee], [.se]] }

def IK1 : HandshakePattern :=
  { base := "IK1", preInitiator := [], preResponder := [.s],
    messages := [[.e, .s], [.e, .ee, .se, .es]] }

def I1K1 : HandshakePattern :=
  { base := "I1K1", preInitiator := [], preResponder := [.s],
    messages := [[.e, .s], [.e, .ee, .es], [.se]] }

def I1X : HandshakePattern :=
  { base := "I1X", preInitiator := [], preResponder := [],
    messages := [[.e, .s], [.e, .ee, .s, .es], [.se]] }

def IX1 : HandshakePattern :=
  { base := "IX1", preInitiator := [], preResponder := [],
    messages := [[.e, .s], [.e, .ee, .se, .s], [.es]] }

def I1X1 : HandshakePattern :=
  { base := "I1X1", preInitiator := [], preResponder := [],
    messages := [[.e, .s], [.e, .ee, .s], [.se, .es]] }

def all : List HandshakePattern :=
  [NN, KN, NK, KK, NX, KX, XN, IN, XK, IK, XX, IX, N, K, X, NK1, NX1, X1N, X1K, XK1, X1K1, X1X, XX1, X1X1, K1N, K1K, KK1, K1K1, K1X, KX1, K1X1, I1N, I1K, IK1, I1K1, I1X, IX1, I1X1]


/-! ## PQ Noise (Angel, Dowling, Hülsing, Schwabe, Weber, Figure 2) -/

def pqN : HandshakePattern :=
  { base := "pqN", preInitiator := [], preResponder := [.s],
    messages := [[.skem]], oneWay := true }

def pqNN : HandshakePattern :=
  { base := "pqNN", preInitiator := [], preResponder := [],
    messages := [[.e], [.ekem]] }

def pqNK : HandshakePattern :=
  { base := "pqNK", preInitiator := [], preResponder := [.s],
    messages := [[.skem, .e], [.ekem]] }

def pqNX : HandshakePattern :=
  { base := "pqNX", preInitiator := [], preResponder := [],
    messages := [[.e], [.ekem, .s], [.skem]] }

def pqKN : HandshakePattern :=
  { base := "pqKN", preInitiator := [.s], preResponder := [],
    messages := [[.e], [.ekem, .skem]] }

def pqKK : HandshakePattern :=
  { base := "pqKK", preInitiator := [.s], preResponder := [.s],
    messages := [[.skem, .e], [.ekem, .skem]] }

def pqKX : HandshakePattern :=
  { base := "pqKX", preInitiator := [.s], preResponder := [],
    messages := [[.e], [.ekem, .skem, .s], [.skem]] }

def pqXN : HandshakePattern :=
  { base := "pqXN", preInitiator := [], preResponder := [],
    messages := [[.e], [.ekem], [.s], [.skem]] }

def pqXK : HandshakePattern :=
  { base := "pqXK", preInitiator := [], preResponder := [.s],
    messages := [[.skem, .e], [.ekem], [.s], [.skem]] }

def pqXX : HandshakePattern :=
  { base := "pqXX", preInitiator := [], preResponder := [],
    messages := [[.e], [.ekem, .s], [.skem, .s], [.skem]] }

def pqIN : HandshakePattern :=
  { base := "pqIN", preInitiator := [], preResponder := [],
    messages := [[.e, .s], [.ekem, .skem]] }

def pqIK : HandshakePattern :=
  { base := "pqIK", preInitiator := [], preResponder := [.s],
    messages := [[.skem, .e, .s], [.ekem, .skem]] }

def pqIX : HandshakePattern :=
  { base := "pqIX", preInitiator := [], preResponder := [],
    messages := [[.e, .s], [.ekem, .skem, .s], [.skem]] }

def pq : List HandshakePattern :=
  [pqN, pqNN, pqNK, pqNX, pqKN, pqKK, pqKX, pqXN, pqXK, pqXX, pqIN, pqIK, pqIX]

/-- The PSK patterns of Noise §9.4. -/
def classicalPsk : List HandshakePattern :=
  [NN.addPsk 0, NN.addPsk 2, NK.addPsk 0, NK.addPsk 2, NX.addPsk 2, XN.addPsk 3, XK.addPsk 3,
   XX.addPsk 3, KN.addPsk 0, KN.addPsk 2, KK.addPsk 0, KK.addPsk 2, KX.addPsk 2, IN.addPsk 1,
   IN.addPsk 2, IK.addPsk 1, IK.addPsk 2, IX.addPsk 2, N.addPsk 0, K.addPsk 0, X.addPsk 1]

/-- The PQ patterns with the PSK placements of their classical counterparts. -/
def pqPsk : List HandshakePattern :=
  [pqNN.addPsk 2, pqNK.addPsk 2, pqNX.addPsk 2, pqXN.addPsk 3, pqXK.addPsk 3, pqXX.addPsk 3,
   pqKN.addPsk 2, pqKK.addPsk 2, pqKX.addPsk 2, pqIN.addPsk 1, pqIN.addPsk 2, pqIK.addPsk 1,
   pqIK.addPsk 2, pqIX.addPsk 2]

/-- Every base pattern, classical and PQ. -/
def bases : List HandshakePattern := all ++ pq

/-- Resolve a pattern name such as `XXpsk0+psk3` or `pqIKpsk2` into its base and modifiers. -/
def byName (name : String) : Option HandshakePattern := do
  let (base, mods) := match name.splitOn "psk" with
    | [b] => (b, [])
    | b :: _ => (b, ((name.drop b.length).toString.splitOn "+"))
    | [] => (name, [])
  let p ← bases.find? (·.base == base)
  mods.foldlM (fun p m => do
    let n ← (m.dropPrefix? "psk").bind (·.toString.toNat?)
    pure (p.addPsk n)) p

end Uproar.Patterns
