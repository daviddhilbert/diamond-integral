# Completed [18] source overlay

These source files reproduce the dependency state used by the Section 5 proofs.
The upstream repository is https://github.com/daviddhilbert/integration-in-ACVF.
The pinned base revision is `7d4acc730496b3bd05a22c268ffd89540ca694f9`.

The 250 completed Section 5 sources are copied exactly from
`section-5/contracting-to-rv` at
`73aa1e6c9218bcb01dd67e03cfbe3ec9115ac240`. The two additional Section 6 files
are the recorded hypothesis-scope adapters. They retain characteristic zero,
uncountable saturation and a positive named Gamma value at the two-order input
and its consuming call. The actual input is proved by the local
`completed_section5_input`; it is not supplied as a hypothesis.

`manifest.json` records the original and restored source hashes. The exact
upstream-overlay hashes and scope-adapter diff are in `../reference/`.
The earlier 39 library compatibility corrections are retained in the existing
Section 2 and Section 3 reuse manifests and patches. All existing upstream
source attribution is preserved.

Run `python3 'section 5/prepare-dependencies.py'` from the project root after
Lake fetches its pinned packages. It validates all payloads and revisions,
restores only original pinned files or missing new files, and refuses to
overwrite unexpected local edits. `--check` performs read-only validation.
