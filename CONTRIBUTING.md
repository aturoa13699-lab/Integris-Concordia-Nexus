# Contributing to Integris-Concordia

Thank you for your interest in contributing! This document explains how to contribute code, proofs, documentation, and ideas.

-----

## Table of Contents

1. [Code of Conduct](#code-of-conduct)
1. [Ways to Contribute](#ways-to-contribute)
1. [Development Setup](#development-setup)
1. [Contribution Workflow](#contribution-workflow)
1. [Coq Proof Guidelines](#coq-proof-guidelines)
1. [Code Style](#code-style)
1. [Testing Requirements](#testing-requirements)
1. [Documentation Standards](#documentation-standards)
1. [Review Process](#review-process)

-----

## Code of Conduct

This project adheres to the [Contributor Covenant Code of Conduct](CODE_OF_CONDUCT.md). By participating, you agree to uphold this code. Please report unacceptable behavior to conduct@integris-concordia.io.

-----

## Ways to Contribute

### 1. **Coq Proof Review** (High Value)

- Verify existing proofs for correctness
- Suggest alternative proof strategies
- Identify gaps in specifications

### 2. **Code Contributions**

- Fix bugs in extracted OCaml code
- Improve CLI tool usability
- Add new features (V2 perimeter)

### 3. **Documentation**

- Improve clarity of existing docs
- Add examples and tutorials
- Translate to other languages

### 4. **Testing**

- Write unit tests for edge cases
- Add property-based tests (QuickCheck)
- Performance benchmarking

### 5. **Issue Triage**

- Reproduce reported bugs
- Clarify feature requests
- Label and categorize issues

### 6. **Community Support**

- Answer questions in Discussions
- Help newcomers get started
- Share use cases and feedback

-----

## Development Setup

### Prerequisites

```bash
# Install Coq, OCaml, and Dune
opam init
eval $(opam env)
opam install coq.8.18.0 dune.3.12.0 ocaml.4.14.1

# Additional development tools
opam install merlin ocaml-lsp-server ocp-indent
```

### Fork and Clone

```bash
# Fork the repository on GitHub, then:
git clone https://github.com/YOUR_USERNAME/integris-concordia.git
cd integris-concordia

# Add upstream remote
git remote add upstream https://github.com/integris-concordia/integris-concordia.git
```

### Build and Test

```bash
# Verify Coq proofs
cd coq
make verify

# Build OCaml code
cd ..
dune build

# Run tests
dune test

# Run benchmarks
cd benchmarks
make run
```

### Editor Setup

**VS Code**:

```bash
# Install extensions
code --install-extension maximedenes.vscoq
code --install-extension ocamllabs.ocaml-platform
```

**Emacs**:

```elisp
;; Install Proof General for Coq
(use-package proof-general)
(use-package company-coq)

;; Install Merlin for OCaml
(use-package merlin)
```

**Vim/Neovim**:

```vim
" Install Coquille for Coq
Plug 'the-lambda-church/coquille'

" Install Merlin for OCaml
Plug 'ocaml/merlin'
```

-----

## Contribution Workflow

### 1. **Check Existing Issues**

Before starting work:

- Search [existing issues](https://github.com/integris-concordia/integris-concordia/issues)
- Check [pull requests](https://github.com/integris-concordia/integris-concordia/pulls)
- Ask in [Discussions](https://github.com/integris-concordia/integris-concordia/discussions)

### 2. **Open an Issue (for non-trivial changes)**

For features or refactors, open an issue first to discuss:

- What problem does this solve?
- How will it be implemented?
- Are there alternative approaches?

### 3. **Create a Branch**

```bash
# Update your fork
git fetch upstream
git checkout main
git merge upstream/main

# Create feature branch
git checkout -b feature/your-feature-name
# or
git checkout -b fix/bug-description
```

### 4. **Make Changes**

- Write code following our [style guide](#code-style)
- Add tests for new functionality
- Update documentation as needed

### 5. **Commit with Clear Messages**

```bash
git add .
git commit -m "Add feature X that does Y

- Implements new Z capability
- Adds tests for edge case W
- Updates documentation in README.md

Closes #123"
```

**Commit message format**:

- **First line**: Short summary (50 chars max)
- **Body**: Detailed explanation (wrap at 72 chars)
- **References**: Link to issues (`Closes #123`)

### 6. **Push and Open Pull Request**

```bash
git push origin feature/your-feature-name
```

Then open a pull request on GitHub with:

- **Title**: Concise description
- **Description**: What changed and why
- **Testing**: How you verified it works
- **Screenshots**: If UI changes

### 7. **Respond to Feedback**

- Address reviewer comments promptly
- Push additional commits to same branch
- Mark conversations as resolved when done

### 8. **Merge**

Once approved, maintainers will merge your PR. Thanks!

-----

## Coq Proof Guidelines

### Proof Quality Standards

**✅ REQUIRED**:

- No `Admitted` lemmas (all proofs must be `Qed.`)
- No `admit` tactics (temporary scaffolding must be removed)
- All axioms documented in comments

**✅ ENCOURAGED**:

- Modular proofs (split large proofs into lemmas)
- Readable tactics (avoid `auto; auto; auto.` chains)
- Proof comments explaining strategy

### Example: Good vs. Bad

**❌ BAD** (Opaque proof):

```coq
Lemma apply_preserves_invariant : forall s d,
  invariant s ->
  invariant (apply_decision s d).
Proof.
  intros. unfold invariant. unfold apply_decision. 
  destruct (cid_mem _ _); simpl; auto; intuition; 
  eapply some_lemma; eauto; crush.
Qed.
```

**✅ GOOD** (Readable proof):

```coq
Lemma apply_preserves_invariant : forall s d,
  invariant s ->
  invariant (apply_decision s d).
Proof.
  intros s d Hinv.
  unfold apply_decision.
  
  (* Case 1: CID already applied (no-op) *)
  destruct (cid_mem (dr_cid d) (applied_cids s)) eqn:Hmem.
  { assumption. }  (* State unchanged, invariant preserved *)
  
  (* Case 2: CID not applied (state updated) *)
  unfold invariant in *.
  split.
  - (* applied_cids remains valid *)
    apply cid_set_add_preserves_validity; assumption.
  - (* active_policies remains consistent *)
    apply policy_map_add_preserves_consistency; assumption.
Qed.
```

### Proof Checklist

Before submitting proof changes:

```bash
# 1. Verify locally
coqc -R theories Integris theories/YourFile.v

# 2. Check for admitted lemmas
grep "Admitted" theories/YourFile.v
# Should return nothing

# 3. Check for dangerous tactics
grep -E "admit\.|Admitted\.|intuition\." theories/YourFile.v
# Review each usage carefully

# 4. Document axioms
grep "Axiom" theories/YourFile.v
# Add comment explaining why axiom is necessary
```

-----

## Code Style

### Coq Style

```coq
(* Module names: CamelCase *)
Module DecisionApplication.

(* Function names: snake_case *)
Definition apply_decision (s : state) (d : decision_record) : state := ...

(* Type names: snake_case *)
Record decision_record := {
  dr_cid : cid;
  dr_action : action
}.

(* Constants: UPPER_CASE *)
Definition MAX_POLICY_SIZE : nat := 1000000.

(* Comments: Full sentences with punctuation *)
(* This function applies a decision record to the current state.
   It returns the updated state or the original state if idempotent. *)
```

### OCaml Style

```ocaml
(* Module names: CamelCase *)
module ConcordiaCore = struct

(* Function names: snake_case *)
let generate_cid (artifact : json) : cid =
  ...

(* Type names: snake_case *)
type decision_record = {
  dr_cid : cid;
  dr_action : action;
}

(* Constants: snake_case (lowercase) *)
let max_policy_size = 1_000_000

(* Use pattern matching over if-else *)
let apply_decision state decision =
  match CidSet.mem decision.dr_cid state.applied_cids with
  | true -> state  (* Idempotent no-op *)
  | false -> update_state state decision
```

### General Principles

1. **Readability over cleverness**
- Prefer explicit code to implicit magic
- Avoid overly terse variable names (except `i`, `j` for indices)
1. **Modularity**
- Functions should do one thing well
- Maximum 50 lines per function (Coq or OCaml)
1. **Documentation**
- Every public function needs a comment
- Explain *why*, not just *what*
1. **Error Handling**
- Use `Result` types, not exceptions
- Provide helpful error messages

-----

## Testing Requirements

### Unit Tests

All new code must have unit tests:

```ocaml
(* tests/unit/test_apply_decision.ml *)
let test_idempotence () =
  let state = empty_state in
  let decision = { dr_cid = cid_of_string "sha256:abc123"; ... } in
  
  let state1 = apply_decision state decision in
  let state2 = apply_decision state1 decision in
  
  assert_equal state1 state2

let suite = "apply_decision" >::: [
  "idempotence" >:: test_idempotence;
  "single_writer" >:: test_single_writer;
  ...
]
```

### Property-Based Tests

For complex logic, add QuickCheck-style tests:

```ocaml
(* tests/property/test_canonicalization.ml *)
let prop_round_trip json =
  let canonical = canonicalize json in
  let serialized = serialize canonical in
  let parsed = parse serialized in
  canonical = canonicalize parsed

(* Generate 1000 random JSON values and test *)
let () = QCheck.Test.run (QCheck.Test.make prop_round_trip)
```

### Integration Tests

For CLI tools:

```bash
# tests/integration/test_cli.sh
#!/bin/bash
set -e

# Test 1: Ingest valid policy
CID=$(concordia-ingest policy.json | grep CID | cut -d' ' -f2)
[[ -n "$CID" ]] || exit 1

# Test 2: Apply decision
integris-apply decision.json
[[ $? -eq 0 ]] || exit 1

# Test 3: Idempotence
integris-apply decision.json
[[ $? -eq 0 ]] || exit 1

echo "All tests passed!"
```

### Running Tests

```bash
# Run all tests
dune test

# Run specific test suite
dune test tests/unit

# Run with coverage
dune test --instrument-with bisect_ppx
bisect-ppx-report html
```

-----

## Documentation Standards

### Code Documentation

**Coq**:

```coq
(** * Decision Application Module
    This module defines the core logic for applying policy decisions
    to the system state. It provides formal guarantees of idempotence
    and single-writer consistency.
    
    ** Key Theorems:
    - [apply_idempotent]: Applying the same decision twice is a no-op
    - [single_writer]: Only one version of a policy can be active
    
    ** Usage Example:
<<
  let state = empty_state in
  let decision = { dr_cid = ...; ... } in
  let state' = apply_decision state decision in
  ...
>>
*)
```

**OCaml**:

```ocaml
(** Generate a content identifier (CID) for an artifact.
    
    This function canonicalizes the input artifact and computes a
    SHA-256 hash with domain separation to prevent collision with
    other content-addressed systems.
    
    @param artifact The JSON artifact to hash
    @return A content identifier in format "sha256:..."
    
    @raise Invalid_json if artifact contains duplicate keys or invalid UTF-8
    
    Example:
    {[
      let policy = parse_json "{\"approval_threshold\": 1000000}" in
      let cid = generate_cid policy in
      (* cid = "sha256:f4a3b2c1..." *)
    ]}
*)
val generate_cid : json -> cid
```

### User Documentation

All new features need documentation in `docs/`:

1. **User guide**: How to use the feature
1. **API reference**: Function signatures and parameters
1. **Examples**: Working code samples
1. **Troubleshooting**: Common errors and solutions

-----

## Review Process

### What Reviewers Look For

1. **Correctness**
- Does the code do what it claims?
- Are edge cases handled?
- Are proofs sound?
1. **Tests**
- Is there adequate test coverage?
- Do tests actually verify correctness?
1. **Documentation**
- Are changes documented?
- Are examples clear?
1. **Style**
- Does code follow style guide?
- Is it readable?
1. **Performance**
- Are there obvious inefficiencies?
- Should benchmarks be run?

### Review Timeline

- **Initial response**: Within 48 hours (weekdays)
- **Detailed review**: Within 1 week
- **Final approval**: Depends on complexity

### Addressing Feedback

**Good response**:

```
Thanks for catching that! I've:
- Fixed the off-by-one error in line 42
- Added a test case for empty input
- Updated the documentation to clarify behavior

Ready for another look.
```

**Less helpful response**:

```
I don't agree with your comment. The code works fine.
```

### Merge Criteria

PRs are merged when:

- ✅ All CI checks pass (proofs verify, tests pass)
- ✅ At least one maintainer approves
- ✅ All review comments are addressed
- ✅ Documentation is updated
- ✅ No merge conflicts

-----

## Special Topics

### Adding a New Coq Theorem

1. **Write specification** in comments first
1. **State theorem** with clear assumptions
1. **Prove theorem** (can use `admit.` temporarily)
1. **Replace admits** with real proofs
1. **Add extraction** if needed for OCaml
1. **Update tests** to exercise new property

### Adding a New CLI Tool

1. **Design interface** (flags, arguments, output)
1. **Write OCaml implementation** using verified core
1. **Add help text** (`--help` output)
1. **Write integration tests**
1. **Update README.md** with usage examples
1. **Add man page** (if appropriate)

### Adding V2 Perimeter Feature

1. **Define interface** in `src/verification_nexus.ml`
1. **Write specification** documenting behavior
1. **Implement adapter** (e.g., Bitcoin SPV)
1. **Add integration tests** with mock ledger
1. **Document configuration** in `docs/`
1. **Update architecture diagram**

-----

## Getting Help

### Before Asking

1. Check [existing documentation](docs/)
1. Search [closed issues](https://github.com/integris-concordia/integris-concordia/issues?q=is%3Aissue+is%3Aclosed)
1. Review [pull request history](https://github.com/integris-concordia/integris-concordia/pulls?q=is%3Apr+is%3Aclosed)

### Where to Ask

- **General questions**: [GitHub Discussions](https://github.com/integris-concordia/integris-concordia/discussions)
- **Bug reports**: [GitHub Issues](https://github.com/integris-concordia/integris-concordia/issues)
- **Security issues**: security@integris-concordia.io (private)
- **Code review**: Comment on your pull request

### Communication Guidelines

- Be respectful and constructive
- Provide context and examples
- Be patient (maintainers are volunteers)
- Follow up if you resolve your own issue

-----

## Recognition

Contributors are recognized in:

- **README.md**: Listed in Acknowledgments section
- **Release notes**: Credited in changelog
- **Academic papers**: Co-authorship for significant proof contributions

For major contributions (new proofs, major features), we can discuss co-authorship on academic publications.

-----

## License

By contributing, you agree that your contributions will be licensed under the Apache License 2.0.

-----

**Thank you for making Integris-Concordia better!**

Questions? Open a [Discussion](https://github.com/integris-concordia/integris-concordia/discussions) or email hello@integris-concordia.io.
