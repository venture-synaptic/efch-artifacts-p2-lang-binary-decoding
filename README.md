# EFCH Lang — research artifacts (EXP-004 to EXP-015)

Artifacts for the draft manuscript *Verified Binary Decoding with a Domain-Specific Language: An
Empirical Study of EFCH Lang against C, Rust–Kani, and Dafny* (`paper/`, version 0.2).

**Status:** draft, not peer reviewed, not submitted. EFCH is research software (0.1.0a1), not
production-ready. Most project documents are in Spanish; the manuscript is in English.

Author: Erik Fisher Cueva Huari, VentureSynaptic Labs — ORCID
[0000-0001-7268-5510](https://orcid.org/0000-0001-7268-5510).

## Contents

| Path | Content |
|---|---|
| `docs/experimentos/` | Preregistered protocols and recorded results: EXP-004, EXP-005, EXP-007, EXP-008, EXP-009, EXP-010, EXP-015 |
| `docs/lenguaje-efch-*.md` | Reference of the EFCH core and of EFCH Lang 0.1 |
| `efch/`, `experimentos/`, `ejemplos/`, `tests/` | Code, experiment scripts, corpus (EFCH specifications and programs, handwritten C, Rust, Go and Dafny comparators) and tests |
| `data/efch-lang-resultados.tar.gz` | Archived evidence of every experiment above, including the adversarial reviews (`resultados/`) |
| `paper/` | Manuscript draft and PDF |

The negative experiments (EXP-007, EXP-008, EXP-009) are included with the same visibility as the
positive ones.

## Provenance and an important limitation

Everything was exported unmodified from the private research repository
`venture-synaptic/efch-research`, `main` at `26315176c3e4d04e9a29612818e8f8b0e762a8bf`
(the project README was renamed to `README-efch-0.1.0a1.md`). The archived evidence
(`data/`) is the record produced when each experiment ran (21–24 October 2026).

**The code is the 1 November 2026 snapshot, not the exact code each experiment ran with.** The
repository history starts with an import on 28 October 2026, after these experiments, and earlier
code versions were not preserved. EXP-009 and EXP-010 recorded SHA-256 digests of `efch/`: 20 of
28 and 21 of 29 files still match; `__main__`, `backend_c`, `core`, `interp`, `lang`,
`pipeline`, `smt` and `store` have changed since. EXP-005 did not record code digests. A rerun is
therefore a re-execution with evolved code, not an exact reproduction; differences from the
archived results must be reported, not reconciled.

Only the tests that do not depend on components outside this package are included. With the
evidence extracted into `resultados/`, they pass: 178 tests, 8 skipped (run on 2 November 2026,
Python 3.14, Z3 from `scripts/vendor_z3.sh`).

## Verify and run

```bash
sha256sum -c SHA256SUMS
tar -xzf data/efch-lang-resultados.tar.gz          # creates resultados/
scripts/vendor_z3.sh                               # Z3 with pinned hash
python3 -m unittest discover -s tests
python3 experimentos/lang01.py --salida /tmp/exp004          # EXP-004
scripts/vendor_comparadores.sh                     # Kani, Dafny (EXP-005 to EXP-010)
python3 experimentos/exp005.py todo --salida /tmp/exp005
```

Requires Python ≥ 3.10 and `gcc`; the comparators also need Rust and Go. Timings depend on the
machine; the original environment is recorded in each `evidencia.json`.

## Contributors

Code, experiments and reports were produced by AI agents under the author's direction: Claude
(Anthropic) implemented and coordinated; Codex (OpenAI, "Sol") performed the adversarial reviews
of EXP-005 and EXP-007; Claude Sonnet reviewed EXP-008 and EXP-010. The author is responsible for
the decisions and interpretation.

## License

- **Code** (`efch/`, `experimentos/`, `scripts/`, `tests/`, and the programs in `ejemplos/`): [Apache-2.0](LICENSE).
- **Data, manuscript and documents** (`data/`, `docs/`, `paper/`, README files): [CC-BY-4.0](LICENSE-CC-BY-4.0).

Copyright 2026 Erik Fisher Cueva Huari (VentureSynaptic Labs). See [NOTICE](NOTICE).
