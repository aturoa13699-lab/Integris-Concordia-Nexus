# Getting Started with Integris-Concordia

This guide will get you from zero to running verified policy applications in under 30 minutes.

-----

## Prerequisites

### Required Software

- **Coq 8.18+** - Proof verification
- **OCaml 4.14+** - Runtime
- **Dune 3.0+** - Build system
- **Git** - Version control

### Optional (for development)

- **opam** - OCaml package manager (recommended)
- **Docker** - For containerized deployment
- **GNU Make** - For convenience scripts

-----

## Installation

### Option 1: Quick Install (macOS/Linux)

```bash
# Install opam (OCaml package manager)
# macOS:
brew install opam

# Ubuntu/Debian:
sudo apt-get install opam

# Initialize opam
opam init
eval $(opam env)

# Install dependencies
opam install coq.8.18.0 dune.3.12.0 ocaml.4.14.1

# Verify installation
coqc --version  # Should show 8.18.0
ocaml --version # Should show 4.14.1
dune --version  # Should show 3.12.0
```

### Option 2: Docker (No Local Install Needed)

```bash
# Pull pre-built image (coming soon)
docker pull integris/concordia:latest

# Or build from source
git clone https://github.com/integris-concordia/integris-concordia.git
cd integris-concordia
docker build -t integris/concordia .

# Run interactive shell
docker run -it integris/concordia /bin/bash
```

-----

## Step 1: Clone & Verify Proofs (5 minutes)

```bash
# Clone repository
git clone https://github.com/integris-concordia/integris-concordia.git
cd integris-concordia

# Navigate to Coq proofs
cd coq

# Verify all proofs
make verify

# Expected output:
# Compiling Canonicalization.v... [OK]
# Compiling V2_Decision_Application.v... [OK]  
# Compiling V2_Rollback.v... [OK]
# All proofs verified. Zero lemmas admitted.
```

### What Just Happened?

- Coq checked every theorem, lemma, and proof step
- `[OK]` means the proof is mathematically sound
- If you see `Admitted`, something is wrong (open an issue!)

-----

## Step 2: Build Executables (5 minutes)

```bash
# Return to repository root
cd ..

# Build all components
dune build

# Verify build
ls _build/default/cli/bin/
# You should see:
# - integris_apply.exe
# - concordia_ingest.exe
# - integris_rollback.exe
```

### Troubleshooting

**Error: “dune: command not found”**

```bash
opam install dune
eval $(opam env)
```

**Error: “ocamlfind: Package X not found”**

```bash
opam install X  # Replace X with missing package
dune clean && dune build
```

-----

## Step 3: Your First Policy Application (10 minutes)

### Create a Test Policy

```bash
# Create example policy file
cat > policy.json << 'EOF'
{
  "policy_id": "test-001",
  "approval_threshold": 1000000,
  "approvers": ["alice@example.com", "bob@example.com"],
  "effective_date": "2025-11-01T00:00:00Z"
}
EOF
```

### Step 3a: Ingest Policy (Generate CID)

```bash
# Generate content identifier
dune exec cli/bin/concordia_ingest.exe -- policy.json

# Expected output:
# Canonicalizing input...
# CID: sha256:f4a3b2c1d5e6f7a8b9c0d1e2f3a4b5c6d7e8f9a0b1c2d3e4f5a6b7c8d9e0f1a2
# Evidence valid: true
```

**What happened?**

1. Concordia normalized the JSON (removed whitespace, sorted keys)
1. Generated cryptographic hash (CID)
1. Validated structure (no duplicate keys, valid UTF-8)

### Step 3b: Apply Policy (Update State)

```bash
# Create decision record
cat > decision.json << EOF
{
  "cid": "sha256:f4a3b2c1d5e6f7a8b9c0d1e2f3a4b5c6d7e8f9a0b1c2d3e4f5a6b7c8d9e0f1a2",
  "action": "apply",
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "operator": "admin@example.com"
}
EOF

# Apply decision
dune exec cli/bin/integris_apply.exe -- decision.json

# Expected output:
# Checking idempotence...
# CID not found in state. Proceeding with application.
# Policy applied successfully.
# Exit code: 0
```

### Step 3c: Test Idempotence (Replay Protection)

```bash
# Try to apply the SAME policy again
dune exec cli/bin/integris_apply.exe -- decision.json

# Expected output:
# Checking idempotence...
# CID already present in state. Skipping application (idempotent).
# Exit code: 0 (success, but no state change)
```

**What happened?**

- First application: CID added to state, policy executed
- Second application: CID found in state, no-op (proven safe)
- This is the idempotence proof in action!

-----

## Step 4: Audit Trail Reconstruction (5 minutes)

### Apply Multiple Policies

```bash
# Apply a few more policies
for i in {2..5}; do
  cat > policy_$i.json << EOF
{
  "policy_id": "test-00$i",
  "approval_threshold": $((1000000 + i * 100000))
}
EOF
  
  CID=$(dune exec cli/bin/concordia_ingest.exe -- policy_$i.json | grep CID | cut -d' ' -f2)
  
  cat > decision_$i.json << EOF
{
  "cid": "$CID",
  "action": "apply",
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
EOF
  
  dune exec cli/bin/integris_apply.exe -- decision_$i.json
done
```

### Rollback to Historical State

```bash
# View current state
dune exec cli/bin/integris_apply.exe -- --show-state

# Rollback to after first policy only
dune exec cli/bin/integris_rollback.exe -- --to-cid sha256:f4a3b2c1...

# Expected output:
# Rolling back state...
# Removed 4 decisions from state.
# State reconstructed to CID: sha256:f4a3b2c1...
# Rollback complete. State is now consistent.
```

**What happened?**

- Integris reconstructed the exact state after first policy
- Mathematical proof guarantees this matches original state
- No manual log parsing, no human error possible

-----

## Step 5: Try the Attack Demos (5 minutes)

### Demo 1: Unicode Attack Prevention

```bash
cd examples/unicode-attack-prevention
./demo.sh

# This will show:
# 1. Git accepting malicious Unicode
# 2. Integris rejecting it at canonicalization
```

### Demo 2: Replay Attack Prevention

```bash
cd ../replay-attack-prevention
./demo.sh

# This will show:
# 1. Traditional system applying policy twice (corrupted state)
# 2. Integris applying once (idempotence proof)
```

### Demo 3: Audit Trail Reconstruction

```bash
cd ../audit-trail-reconstruction
./demo.sh

# This will show:
# 1. Manual log parsing (error-prone, slow)
# 2. Integris automated rollback (instant, proven correct)
```

-----

## Next Steps

### For Developers

- **Read the architecture**: [ARCHITECTURE.md](../ARCHITECTURE.md)
- **Explore the proofs**: [coq/theories/](../coq/theories/)
- **Run benchmarks**: `cd benchmarks && make run`
- **Contribute**: [CONTRIBUTING.md](../CONTRIBUTING.md)

### For Enterprises

- **Review compliance mapping**: [docs/compliance-mapping.md](../docs/compliance-mapping.md)
- **Schedule a demo**: hello@integris-concordia.io
- **Pilot program**: [Apply here](https://integris-concordia.io/pilot)

### For Researchers

- **Read the proofs**: [coq/theories/V2_Decision_Application.v](../coq/theories/V2_Decision_Application.v)
- **Check extraction soundness**: [coq/theories/Extractor.v](../coq/theories/Extractor.v)
- **Review technical dossier**: [docs/technical-audit-dossier.md](../docs/technical-audit-dossier.md)

-----

## Troubleshooting

### “Proof verification failed”

```bash
# Clean and rebuild
cd coq
make clean
make verify
```

If still failing, this is a **critical bug**. Please open an issue immediately with:

- Your Coq version (`coqc --version`)
- Full error output
- Operating system

### “CLI tools not found”

```bash
# Rebuild executables
dune clean
dune build
dune install  # Installs to opam bin directory
```

### “Permission denied” errors

```bash
# Make scripts executable
chmod +x examples/**/*.sh
chmod +x scripts/*.sh
```

### Performance Issues

```bash
# Check system resources
dune clean
dune build --profile=release  # Optimized build
```

-----

## Getting Help

- **Documentation**: [docs/](../docs/)
- **GitHub Issues**: [Report bugs](https://github.com/integris-concordia/integris-concordia/issues)
- **Discussions**: [Ask questions](https://github.com/integris-concordia/integris-concordia/discussions)
- **Email**: hello@integris-concordia.io

-----

## Quick Reference

### Key Commands

```bash
# Verify proofs
cd coq && make verify

# Build everything
dune build

# Ingest policy
dune exec cli/bin/concordia_ingest.exe -- policy.json

# Apply decision
dune exec cli/bin/integris_apply.exe -- decision.json

# Rollback state
dune exec cli/bin/integris_rollback.exe -- --to-cid <CID>

# Show current state
dune exec cli/bin/integris_apply.exe -- --show-state

# Run tests
dune test

# Run benchmarks
cd benchmarks && make run
```

### File Locations

- **Proofs**: `coq/theories/*.v`
- **Extracted code**: `src/*.ml`
- **CLI tools**: `cli/bin/*.ml`
- **Examples**: `examples/*/`
- **Documentation**: `docs/`

-----

**You’re ready to go! Start with the examples or dive into the proofs.**
