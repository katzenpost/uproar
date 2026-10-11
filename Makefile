# uproar
#
# Every target runs from the repository root: the suites load testdata/ by relative path.

SHELL := /bin/bash
LAKE  ?= lake
BIN   := .lake/build/bin

TESTS := \
	Uproar.vectors_test \
	Uproar.pq_test

EXES      := $(TESTS) Uproar.example
TEST_BINS := $(addprefix $(BIN)/,$(subst .,-,$(TESTS)))

.PHONY: all build test axioms verify-vectors

all: build

build:
	$(LAKE) build --log-level=warning Uproar $(EXES)

test: build verify-vectors
	@rc=0; \
	for bin in $(TEST_BINS); do \
	  name=$$(basename $$bin); \
	  printf '\n=== %s ===\n' "$$name"; \
	  out=$$("$$bin" 2>&1); status=$$?; \
	  printf '%s\n' "$$out"; \
	  if [ $$status -ne 0 ] || printf '%s' "$$out" | grep -q 'FAIL'; then \
	    rc=1; printf '  ^^ %s FAILED\n' "$$name"; \
	  fi; \
	done; \
	exit $$rc

verify-vectors:
	@cd testdata && sha256sum --quiet -c *.sha256

axioms: build
	@./scripts/check-axioms.sh
