# Gate file

The dated record of every gate evaluation: the date, the gate, the verdict, who evaluated it and
one line of reason. It is append-only. A line is added when a gate is evaluated; a recorded line
is never edited, reordered or removed, and a correction is a new line.

D+0 is the date of the first public pin commit, recorded below. G1 is the gate that asks whether,
within 180 days of publication, two independent third parties have cited the finding or asked for
the next dataset, and only once an outside party has regenerated the whole table.

## What counts as a citation

One definition, used by gate G1 and the success ladder alike: a bibliography entry or a
model-card line naming the ledger's release — the finding report or a published snapshot — with a
verb of adoption or validation, the field's observed idiom ("we adopt the revised version of X
released by Y", "verified against", "verified with"), made unprompted by a party with no prior
relationship to the operator. It counts in a paper's bibliography, a dataset or model card, and
in the same form in a repository, an issue, a forum thread or a dataset's own documentation. A
content hash is optional and never required. Contact initiated by the project's own notices and
announcements, at any date — the upstream notice, the announcement steps and the optional
pre-D+0 note included — never creates a prior relationship; only a relationship that predates D+0
excludes a citer. A private thank-you is not a citation. A reply that only discusses the finding
is not a citation. A request, unprompted, for the next dataset counts as demand — wherever it
appears, the announcement thread included. An answer to a question the operator posted, in that
thread or anywhere else, is solicited and never counts. The venue never decides; the content of
the ask does.

## Rules for a line

- `date` is the local calendar date, `YYYY-MM-DD`.
- `gate` is a slug from the closed list in `src/ledger/gatefile.py`. A parameterised slug takes a
  suffix.
- `verdict` is at most 120 characters. `reason` is at most 400 characters and may carry figures
  as `key=value` pairs separated by `; `. Neither contains `|` or a newline.
- `evaluator` is one of `pipeline`, `assistant`, `operator` or `stranger`. It is never a person's
  name.
- A line carries no host address, no absolute path on any host and no personal name. `https://`
  links are allowed: announcements, sweeps and outside reproductions.
- A line that breaks these rules is refused when it is appended.

## Gates

| date | gate | verdict | evaluator | reason |
|---|---|---|---|---|
| 2026-10-09 | prd-approved | recorded | operator | PRD v18 approved |
| 2026-10-09 | d-0-name | met | operator | public name Proof Dataset Audit; publisher Tahoma Research; organisation reserved 2026-10-02; name decided 2026-10-03 |
| 2026-10-09 | d-0-research | proceed | assistant | Q-254 answered 2026-09-22: proceed; reshape is framing only and is satisfied by v10; scope unchanged |
