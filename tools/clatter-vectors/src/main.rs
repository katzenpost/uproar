//! Deterministic PQ Noise vectors from clatter, in the cacophony vector format.
//!
//! Every key is generated from fixed bytes and every encapsulation's coins are
//! `SHAKE256(seed || 0x00)[..32]`, the value Cryptlib's ML-KEM draws from a seed, so a
//! party built from the recorded `*_encap_seeds` makes exactly the same ciphertexts.

use std::cell::RefCell;
use std::collections::VecDeque;
use std::convert::Infallible;

use clatter::crypto::cipher::{AesGcm, ChaChaPoly};
use clatter::crypto::hash::{Blake2b, Blake2s, Sha256, Sha512};
use clatter::crypto::kem::rust_crypto_ml_kem::{MlKem512, MlKem768, MlKem1024};
use clatter::handshakepattern::*;
use clatter::traits::{Cipher, Handshaker, Hash, Kem};
use clatter::bytearray::ByteArray;
use clatter::{KeyPair, PqHandshakeCore};
use rand_core::{TryCryptoRng, TryRng};
use serde_json::{Value, json};
use sha3::Shake256;
use sha3::digest::{ExtendableOutput, Update, XofReader};

thread_local!(static QUEUE: RefCell<VecDeque<u8>> = RefCell::new(VecDeque::new()));

#[derive(Default, Clone)]
struct ScriptRng;

impl TryRng for ScriptRng {
    type Error = Infallible;
    fn try_next_u32(&mut self) -> Result<u32, Infallible> {
        unreachable!("scripted RNG only fills bytes")
    }
    fn try_next_u64(&mut self) -> Result<u64, Infallible> {
        unreachable!("scripted RNG only fills bytes")
    }
    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Infallible> {
        QUEUE.with(|q| {
            let mut q = q.borrow_mut();
            for b in dst.iter_mut() {
                *b = q.pop_front().expect("scripted RNG ran dry");
            }
        });
        Ok(())
    }
}

impl TryCryptoRng for ScriptRng {}

fn shake(parts: &[&[u8]], n: usize) -> Vec<u8> {
    let mut h = Shake256::default();
    for p in parts {
        h.update(p);
    }
    let mut out = vec![0u8; n];
    h.finalize_xof().read(&mut out);
    out
}

fn label(l: &str, n: usize) -> Vec<u8> {
    shake(&[b"uproar-pq-vectors/", l.as_bytes()], n)
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn push(bytes: &[u8]) {
    QUEUE.with(|q| q.borrow_mut().extend(bytes.iter().copied()));
}

/// A key pair from `d || z`, with its private key in the `ek || d || z` form Cryptlib reads.
fn keypair<K: Kem>(l: &str) -> (KeyPair<K::PubKey, K::SecretKey>, Vec<u8>) {
    push(&label(l, 64));
    let kp = K::genkey_rng(&mut ScriptRng).unwrap();
    let mut wire = kp.public.as_slice().to_vec();
    wire.extend_from_slice(kp.secret.as_slice());
    (kp, wire)
}

struct Party {
    seeds: Vec<Vec<u8>>,
    used: usize,
}

impl Party {
    /// Coins for every encapsulation this party may still make, consumed in order.
    fn load(&self) {
        QUEUE.with(|q| q.borrow_mut().clear());
        for s in &self.seeds[self.used..] {
            push(&shake(&[s, &[0u8]], 32));
        }
    }
    fn settle(&mut self) {
        let left = QUEUE.with(|q| q.borrow().len()) / 32;
        self.used = self.seeds.len() - left;
    }
}

fn vector<E: Kem, S: Kem, C: Cipher, H: Hash>(pattern: HandshakePattern, pname: &str) -> Value {
    let name = format!(
        "Noise_{pname}_{}_{}_{}",
        if E::name() == S::name() { E::name().to_string() } else { format!("{}+{}", E::name(), S::name()) },
        C::name(),
        H::name()
    );
    assert_eq!(pattern.get_name(), pname, "clatter's pattern name");
    let tag = |x: &str| format!("{name}/{x}");
    // pre-message statics are not exposed by clatter; PQ patterns name them in their second letter
    let pre_i_s = matches!(pname.as_bytes()[2], b'K');
    let pre_r_s = matches!(pname.as_bytes()[3], b'K');
    let tokens = |init: bool| -> Vec<Token> {
        if init {
            (0..pattern.get_initiator_pattern_len()).flat_map(|i| pattern.get_initiator_pattern(i).to_vec()).collect()
        } else {
            (0..pattern.get_responder_pattern_len()).flat_map(|i| pattern.get_responder_pattern(i).to_vec()).collect()
        }
    };
    let need_is = pre_i_s || tokens(true).contains(&Token::S);
    let need_rs = pre_r_s || tokens(false).contains(&Token::S);
    let psk_count = tokens(true).iter().chain(tokens(false).iter()).filter(|t| **t == Token::Psk).count();

    let (is_kp, is_wire) = keypair::<S>(&tag("is"));
    let (rs_kp, rs_wire) = keypair::<S>(&tag("rs"));
    let (ie_kp, ie_wire) = keypair::<E>(&tag("ie"));
    let psks: Vec<Vec<u8>> = (0..psk_count).map(|i| label(&tag(&format!("psk{i}")), 32)).collect();
    let prologue = b"uproar".to_vec();

    let mut alice = PqHandshakeCore::<E, S, C, H, ScriptRng>::new(
        pattern.clone(),
        &prologue,
        true,
        need_is.then(|| is_kp.clone()),
        Some(ie_kp.clone()),
        pre_r_s.then(|| rs_kp.public.clone()),
        None,
    )
    .unwrap();
    let mut bob = PqHandshakeCore::<E, S, C, H, ScriptRng>::new(
        pattern.clone(),
        &prologue,
        false,
        need_rs.then(|| rs_kp.clone()),
        None,
        pre_i_s.then(|| is_kp.public.clone()),
        None,
    )
    .unwrap();
    for p in &psks {
        alice.push_psk(p);
        bob.push_psk(p);
    }

    let mut pa = Party { seeds: (0..8).map(|i| label(&tag(&format!("i-encap{i}")), 32)).collect(), used: 0 };
    let mut pb = Party { seeds: (0..8).map(|i| label(&tag(&format!("r-encap{i}")), 32)).collect(), used: 0 };

    let mut messages = vec![];
    let mut buf = vec![0u8; 65535];
    let mut out = vec![0u8; 65535];
    let mut i = 0;
    while !(alice.is_finished() && bob.is_finished()) {
        let payload = format!("handshake {i}").into_bytes();
        let n = if i % 2 == 0 {
            pa.load();
            let n = alice.write_message(&payload, &mut buf).unwrap();
            pa.settle();
            bob.read_message(&buf[..n], &mut out).unwrap();
            n
        } else {
            pb.load();
            let n = bob.write_message(&payload, &mut buf).unwrap();
            pb.settle();
            alice.read_message(&buf[..n], &mut out).unwrap();
            n
        };
        messages.push(json!({"payload": hex(&payload), "ciphertext": hex(&buf[..n])}));
        i += 1;
    }
    let mut alice = alice.finalize().unwrap();
    let mut bob = bob.finalize().unwrap();
    for _ in 0..4 {
        let payload = format!("transport {i}").into_bytes();
        let n = if i % 2 == 0 {
            let n = alice.send(&payload, &mut buf).unwrap();
            bob.receive(&buf[..n], &mut out).unwrap();
            n
        } else {
            let n = bob.send(&payload, &mut buf).unwrap();
            alice.receive(&buf[..n], &mut out).unwrap();
            n
        };
        messages.push(json!({"payload": hex(&payload), "ciphertext": hex(&buf[..n])}));
        i += 1;
    }
    assert_eq!(alice.get_handshake_hash().as_slice(), bob.get_handshake_hash().as_slice());

    let psk_hex: Vec<String> = psks.iter().map(|p| hex(p)).collect();
    let mut v = json!({
        "protocol_name": name,
        "init_prologue": hex(&prologue),
        "resp_prologue": hex(&prologue),
        "init_ephemeral": hex(&ie_wire),
        "init_encap_seeds": pa.seeds[..pa.used].iter().map(|s| hex(s)).collect::<Vec<_>>(),
        "resp_encap_seeds": pb.seeds[..pb.used].iter().map(|s| hex(s)).collect::<Vec<_>>(),
        "init_psks": psk_hex,
        "resp_psks": psk_hex,
        "handshake_hash": hex(alice.get_handshake_hash().as_slice()),
        "messages": messages,
    });
    if need_is { v["init_static"] = json!(hex(&is_wire)); }
    if need_rs { v["resp_static"] = json!(hex(&rs_wire)); }
    if pre_r_s { v["init_remote_static"] = json!(hex(rs_kp.public.as_slice())); }
    if pre_i_s { v["resp_remote_static"] = json!(hex(is_kp.public.as_slice())); }
    v
}

fn patterns() -> Vec<(HandshakePattern, &'static str)> {
    vec![
        (noise_pqnn(), "pqNN"), (noise_pqnk(), "pqNK"), (noise_pqnx(), "pqNX"),
        // noise_pqkn() names itself "pqNK" in clatter, so its pqKN hashes the wrong protocol name
        (noise_pqkk(), "pqKK"), (noise_pqkx(), "pqKX"),
        (noise_pqxn(), "pqXN"), (noise_pqxk(), "pqXK"), (noise_pqxx(), "pqXX"),
        (noise_pqin(), "pqIN"), (noise_pqik(), "pqIK"), (noise_pqix(), "pqIX"),
        (noise_pqnn_psk2(), "pqNNpsk2"), (noise_pqnk_psk2(), "pqNKpsk2"), (noise_pqnx_psk2(), "pqNXpsk2"),
        (noise_pqxn_psk3(), "pqXNpsk3"), (noise_pqxk_psk3(), "pqXKpsk3"), (noise_pqxx_psk3(), "pqXXpsk3"),
        (noise_pqkn_psk2(), "pqKNpsk2"), (noise_pqkk_psk2(), "pqKKpsk2"), (noise_pqkx_psk2(), "pqKXpsk2"),
        (noise_pqin_psk1(), "pqINpsk1"), (noise_pqin_psk2(), "pqINpsk2"), (noise_pqik_psk1(), "pqIKpsk1"),
        (noise_pqik_psk2(), "pqIKpsk2"), (noise_pqix_psk2(), "pqIXpsk2"),
    ]
}

fn main() {
    let mut vs = vec![];
    for (p, n) in patterns() {
        vs.push(vector::<MlKem768, MlKem768, ChaChaPoly, Blake2s>(p.clone(), n));
        vs.push(vector::<MlKem512, MlKem1024, AesGcm, Sha512>(p, n));
    }
    for (p, n) in [(noise_pqxx(), "pqXX"), (noise_pqik(), "pqIK")] {
        vs.push(vector::<MlKem768, MlKem768, ChaChaPoly, Sha256>(p.clone(), n));
        vs.push(vector::<MlKem768, MlKem768, ChaChaPoly, Sha512>(p.clone(), n));
        vs.push(vector::<MlKem768, MlKem768, ChaChaPoly, Blake2b>(p.clone(), n));
        vs.push(vector::<MlKem768, MlKem768, AesGcm, Sha256>(p.clone(), n));
        vs.push(vector::<MlKem768, MlKem768, AesGcm, Blake2s>(p.clone(), n));
        vs.push(vector::<MlKem1024, MlKem1024, ChaChaPoly, Blake2s>(p, n));
    }
    let doc = json!({
        "source": "clatter (github.com/jmlepisto/clatter) driven by uproar's pq-vectors harness",
        "vectors": vs,
    });
    println!("{}", serde_json::to_string_pretty(&doc).unwrap());
}
