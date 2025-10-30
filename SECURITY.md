# Security Policy

## Supported Versions

|Version           |Supported|Status                                        |
|------------------|---------|----------------------------------------------|
|1.x (Core Kernel) |✅ Yes    |Production-ready, actively maintained         |
|2.x (V2 Perimeter)|⚠️ Beta   |Interfaces defined, implementation in progress|
|0.x (Pre-release) |❌ No     |Historical versions, no longer supported      |

-----

## Reporting a Vulnerability

**We take security seriously.** If you discover a security vulnerability, please follow responsible disclosure:

### 1. **DO NOT** Open a Public Issue

Public disclosure before mitigation puts users at risk.

### 2. **DO** Email Us Privately

**Email**: security@integris-concordia.io  
**PGP Key**: [Download public key](https://integris-concordia.io/pgp-key.asc)  
**Fingerprint**: `ABCD 1234 EFGH 5678 IJKL 9012 MNOP 3456 QRST 7890`

### 3. What to Include

Please provide:

- **Description** of the vulnerability
- **Steps to reproduce** (as detailed as possible)
- **Affected versions** (if known)
- **Proof of concept** (if available)
- **Potential impact** (CVSS score if calculated)

### 4. What to Expect

|Timeline           |Action                                       |
|-------------------|---------------------------------------------|
|**Within 24 hours**|Acknowledgment of receipt                    |
|**Within 7 days**  |Initial assessment and severity rating       |
|**Within 30 days** |Patch development and testing                |
|**Within 60 days** |Public disclosure (coordinated with reporter)|

### 5. Disclosure Process

1. **Private Fix**: We develop and test a patch privately
1. **Coordinated Disclosure**: We notify you before public release
1. **CVE Assignment**: We request a CVE ID if warranted
1. **Public Announcement**: We publish:
- Security advisory
- Patched version
- Credit to reporter (with permission)

-----

## Security Architecture

### What We Formally Verify

✅ **Proven in Coq** (mathematically certain):

- Idempotence (replay attack immunity)
- Canonicalization (Unicode/normalization attacks)
- Rollback soundness (audit trail integrity)
- Single-writer invariant (state consistency)

### What We Don’t Verify (Trust Required)

❌ **Trusted Computing Base**:

- Coq proof assistant itself (decades of academic vetting)
- OCaml extraction process (formally verified by Coq team)
- SHA-256 collision resistance (cryptographic assumption)
- Operating system and hardware (standard hardening)

-----

## Threat Model

### In Scope (We Protect Against)

|Threat                   |Mitigation         |Assurance Level   |
|-------------------------|-------------------|------------------|
|**Unicode attacks**      |Canonicalization   |Coq proof ✅       |
|**Replay attacks**       |Idempotence        |Coq proof ✅       |
|**State corruption**     |Invariants         |Coq proof ✅       |
|**Audit tampering**      |Content addressing |Cryptographic hash|
|**Single ledger failure**|Multi-anchor quorum|N-1 redundancy    |
|**Key compromise**       |Threshold crypto   |K-of-N shares     |

### Out of Scope (We Don’t Protect Against)

|Threat                       |Reason                              |Mitigation Path                         |
|-----------------------------|------------------------------------|----------------------------------------|
|**Physical HSM compromise**  |Hardware security                   |Use tamper-evident HSMs, audit logs     |
|**All K operators colluding**|Social engineering                  |Background checks, separation of duties |
|**Coq proof bugs**           |Trusted computing base              |Peer review, academic scrutiny          |
|**Quantum computing**        |Post-quantum crypto not yet standard|NIST PQC migration roadmap (2030+)      |
|**SHA-256 collision**        |Cryptographic assumption            |Monitor NIST guidance, migrate if broken|

-----

## Security Best Practices

### For Developers

1. **Verify Proofs Locally**
   
   ```bash
   cd coq/theories
   coqc -R . Integris V2_Decision_Application.v
   # Must complete without "Admitted" lemmas
   ```
1. **Never Bypass Verification**
   
   ```ocaml
   (* BAD: Directly manipulating state *)
   state.applied_cids <- CIDSet.add new_cid state.applied_cids
   
   (* GOOD: Use verified function *)
   let state' = apply_decision state decision in
   ```
1. **Run Security Tests**
   
   ```bash
   dune test --profile=security
   # Includes: fuzzing, timing attacks, boundary conditions
   ```

### For Operators

1. **Key Management**
- Store threshold key shares on separate HSMs
- Require two-person rule for all key operations
- Rotate keys quarterly (or after suspected compromise)
1. **Monitoring**
- Alert on failed idempotence checks (potential replay)
- Alert on multi-anchor quorum failures
- Alert on unusual state size growth (potential DoS)
1. **Incident Response**
- Keep emergency runbooks accessible (docs/emergency-runbooks/)
- Practice key rotation annually
- Maintain off-site backups of audit trails

### For End Users

1. **Verify Evidence**
   
   ```bash
   # Check that CID matches policy content
   concordia-ingest your-policy.json
   # Compare output CID to what was applied
   ```
1. **Audit Regularly**
   
   ```bash
   # Reconstruct historical state
   integris-rollback --to-date 2025-06-15
   # Verify matches expected state
   ```
1. **Report Anomalies**
- Unexpected policy applications
- Rollback failures
- Missing audit trail entries

-----

## Known Security Considerations

### 1. Coq Extraction Trust

**Issue**: We trust Coq’s extraction to OCaml is sound.

**Assurance**:

- Extraction process itself is formally verified
- Used by critical systems (CompCert C compiler, etc.)
- Decades of academic scrutiny

**Residual Risk**: Low (but non-zero)

### 2. SHA-256 Collision Resistance

**Issue**: CID uniqueness depends on SHA-256 being collision-resistant.

**Assurance**:

- No known practical collisions (as of 2025)
- Would require ~2^128 operations to find collision
- NIST-approved algorithm

**Residual Risk**: Quantum computing could reduce to ~2^64 (still infeasible near-term)

**Mitigation**: Migration plan to SHA-3 or post-quantum hashes if SHA-256 broken

### 3. Timestamp Accuracy

**Issue**: Decision timestamps can be manipulated by operators.

**Assurance**:

- Multi-anchor verification provides independent timestamps
- Clock skew detection (warn if >5 minutes off)
- Audit trail includes anchor timestamps (immutable)

**Residual Risk**: Operator with root access could manipulate system clock

**Mitigation**: Use NTP with authenticated time sources, log all clock adjustments

-----

## Vulnerability Disclosure History

*(No vulnerabilities disclosed as of initial release)*

Future disclosures will be listed here with:

- CVE ID
- Severity (CVSS score)
- Affected versions
- Patch version
- Credit to reporter

-----

## Security Audit Status

|Audit Type         |Auditor                  |Date           |Status   |Report|
|-------------------|-------------------------|---------------|---------|------|
|Coq Proof Review   |TBD (Academic)           |Planned Q1 2026|🔄 Pending|-     |
|Code Security Audit|TBD (Trail of Bits / NCC)|Planned Q2 2026|🔄 Pending|-     |
|SOC 2 Type II      |TBD (Big 4 firm)         |Planned Q2 2026|🔄 Pending|-     |
|Penetration Testing|TBD                      |Planned Q3 2026|🔄 Pending|-     |

**Note**: We welcome academic institutions interested in reviewing our Coq proofs. Contact hello@integris-concordia.io if interested.

-----

## Cryptographic Dependencies

### Algorithms Used

|Algorithm  |Use Case                |Key Size  |Quantum Resistance  |
|-----------|------------------------|----------|--------------------|
|SHA-256    |Content addressing (CID)|N/A (hash)|~128-bit (Grover’s) |
|Ed25519    |Threshold signatures    |256-bit   |❌ Broken by Shor’s  |
|AES-256-GCM|State encryption at rest|256-bit   |✅ Secure (symmetric)|
|X25519     |Key exchange (DKG)      |256-bit   |❌ Broken by Shor’s  |

### Post-Quantum Migration Roadmap

**Timeline**: 2030-2035 (based on NIST PQC standardization)

**Planned Migrations**:

1. **Ed25519 → ML-DSA** (NIST FIPS 204 - Dilithium)
1. **X25519 → ML-KEM** (NIST FIPS 203 - Kyber)
1. **SHA-256 → SHA-3** (if quantum speedup discovered)

**Backward Compatibility**: Dual-signing mode during transition (both classical and PQC signatures)

-----

## Compliance & Certifications

### Current Status

|Framework    |Status       |Notes                               |
|-------------|-------------|------------------------------------|
|SOC 2 Type II|🔄 In Progress|Expected Q2 2026                    |
|ISO 27001    |⏳ Planned    |Post-SOC 2                          |
|FedRAMP      |⏳ Planned    |Requires SOC 2 + additional controls|
|FIPS 140-2   |⏳ Planned    |For HSM integration                 |

### Control Mappings

See <docs/compliance-mapping.md> for detailed mappings to:

- SOC 2 (CC6.1, CC7.2, etc.)
- ISO 27001 (A.9.4.2, A.12.3.1, etc.)
- GDPR (Article 25, Article 32, etc.)
- NIST CSF (PR.DS-6, DE.CM-1, etc.)

-----

## Security Contact

**Primary**: security@integris-concordia.io  
**PGP Key**: https://integris-concordia.io/pgp-key.asc  
**Bug Bounty**: Coming Q2 2026 (after initial audit)

**Response SLA**:

- **Critical** (CVSS 9.0-10.0): 24 hours
- **High** (CVSS 7.0-8.9): 72 hours
- **Medium** (CVSS 4.0-6.9): 7 days
- **Low** (CVSS 0.1-3.9): 30 days

-----

## Additional Resources

- [OWASP Top 10](https://owasp.org/www-project-top-ten/)
- [CWE Top 25](https://cwe.mitre.org/top25/)
- [NIST Cybersecurity Framework](https://www.nist.gov/cyberframework)
- [Coq Security Considerations](https://coq.inria.fr/refman/practical-tools/extraction.html#extraction-limitations)

-----

**Thank you for helping keep Integris-Concordia secure!**
