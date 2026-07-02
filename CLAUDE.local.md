@~/personal/claude/lean-CLAUDE.md

## Handoff scheme for THIS repo (append-only, no pointer)

Each lap writes a NEW dated baton `HANDOFF-<date>-lap<N>.md` at the repo root. That's the
whole scheme:

- Do **NOT** create or maintain a `HANDOFF.md` file or symlink. There is no "current
  pointer" file. (A `HANDOFF.md` symlink is a footgun: a plain Write follows it and silently
  overwrites the dated file it points at.)
- The newest baton is found by **numeric** sort on the lap field, not `ls | tail`:
  `ls HANDOFF-*-lap*.md | sort -t p -k2 -n | tail -1`
  (lap numbers aren't zero-padded, so lexicographic `ls | tail` breaks at lap100).
- The durable resume baton remains `JUDGE-HANDOFF.md` + the newest dated `HANDOFF-*-lap*.md`
  + `STATUS.md` / `PENDING_WORK.md`.
