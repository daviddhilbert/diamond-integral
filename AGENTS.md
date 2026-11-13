# Working instructions

- Keep working toward the author's requested formalization until it is
  complete. Do not end a turn merely because an edit, build, audit, or other
  routine milestone has finished.
- Pause only for a critical blocker, such as essential mathematical input
  from the author or approval of a substantive, non-obvious manuscript edit.
  Continue independent authorized work while a review question is pending.
- The author reviews mathematical departures from the main text. Referee
  annotations are commentary, not part of the main text or authorization to
  change it. Apply already approved edits without asking again.
- Always check the paper's statement and proof independently first, using
  its conventions, earlier results and cited hypotheses. Only then read and
  assess the referee report. Do not treat a referee objection or proposed
  repair as established. Distinguish a mathematical error, an omitted
  justification and an optional expository expansion before proposing edits.
- Literal subsets of VF or RV are unary. The general tuple convention does
  not change that scope. Do not repeat a referee's request to specify one
  coordinate when the statement already says this.
- The author approves the combined manuscript-review and formalization
  workflow. Report manuscript progress, supporting Lean lemmas and complete
  numbered results separately; an export count does not certify full section
  formalization.
- Sections 1–3 of [18] are now formalized in daviddhilbert/integration-in-ACVF.
  Use section 2/verification/UPSTREAM-LINKS.md for exact exports and scope
  checks. Prefer checked bridges to those exports over re-proving them.
  Keep an explicit accepted input until its definability, atomicity and
  hypothesis bridge is actually compiled; a source link does not discharge it.
- Keep the revised PDF available in the right-side panel for manuscript
  review. Report a queued or failed display request accurately.
- Review one or two correction items at a time, in paper order. Show only
  a PDF in the right panel, with the proposed edits in a different color
  inside the manuscript context. Do not open the TeX editor or substitute
  a separate summary for the manuscript review. Wait for the author's
  reading and comments before moving to the next review batch. After
  approval, incorporate the change, gray out any corresponding referee
  item, and add a brief resolution note, following the section 2 records.
- Preserve uncommitted work. Do not commit or push without instruction.
- The author approved nontrivial Γ(S) as a standing assumption throughout
  the paper. Track whether any later argument actually needs triviality;
  report a genuine conflict before changing scope. The former exception
  was at the opening of §6, not §5.

- Author instruction, November 11: prove the HK coefficient embeddings and
  tensor comparisons locally. No HK result may be used as a given input.
  Consult HK proof ideas and Section 4.2 of arXiv:1509.07695, but prove
  every needed ACVF lemma here. Do not ask again to accept HK inputs.

- Author instruction, November 12: the supplementary unary-ray kernel
  refinement may be skipped. Check the newer Integration in ACVF exports,
  update the relevant records and pins, audit, then commit and push this
  section's work. This authorizes the push requested in this session; keep
  exact upstream hypotheses and unfinished-input boundaries explicit.
