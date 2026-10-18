# uproar

The [Noise Protocol Framework](https://noiseprotocol.org/noise.html) and PQ Noise, written in Lean 4
on [cryptlib](https://github.com/katzenpost/cryptlib).

- Handshake patterns, `CipherState`, `SymmetricState`, `HandshakeState` and transport messages.
- PQ Noise patterns such as `pqXX`, over every KEM in cryptlib's registry.
- Suites: X25519; ChaChaPoly and AESGCM; SHA256, SHA512, BLAKE2b and BLAKE2s.
- Proofs that decryption undoes encryption and that honest parties stay in sync through a
  handshake (`Uproar/Correctness`).
- Tested against the cacophony and snow test vectors, and clatter's PQ vectors.

## Use

```toml
[[require]]
name = "uproar"
git = "https://github.com/katzenpost/uproar.git"
rev = "noise"
```

`Uproar/example.lean` runs `pqXX` end to end.

## Build and test

```
make build
make test
make axioms
```

## License

AGPL-3.0-only
