import re, sys

src = open(sys.argv[1]).read()
defs = re.findall(r'^noise(\w+) = handshakePattern "(\w+)" \$\n((?:  .*\n)+)', src, re.M)
out = []
for ident, name, body in defs:
    if "psk" in name:
        continue
    pre_i, pre_r, msgs, senders = [], [], [], []
    for kind, toks in re.findall(r'(preInitiator|preResponder|initiator|responder) \(?([a-z *>]+?)\)?\s*(?:\*>)?\s*$', body, re.M):
        ts = [t.strip() for t in toks.split("*>")]
        if kind == "preInitiator": pre_i = ts
        elif kind == "preResponder": pre_r = ts
        else:
            msgs.append(ts); senders.append(kind)
    one_way = name in ("N", "K", "X")
    for i, s in enumerate(senders):
        assert s == ("initiator" if one_way or i % 2 == 0 else "responder"), (name, senders)
    lst = lambda ts: "[" + ", ".join("." + t for t in ts) + "]"
    out.append(f'def {name} : HandshakePattern :=\n  {{ base := "{name}", preInitiator := {lst(pre_i)}, '
               f'preResponder := {lst(pre_r)},\n    messages := [{", ".join(lst(m) for m in msgs)}]'
               + (", oneWay := true" if one_way else "") + " }")
print("\n\n".join(out))
print("\ndef all : List HandshakePattern :=\n  [" + ", ".join(n for _, n, _ in defs if "psk" not in n) + "]")
