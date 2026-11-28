# SQL waiting for the owner's review

Nothing in this folder has been run. The owner asked (27 Nov 2026, night) that no SQL be executed until reviewed:
each file here is a proposal, written to be idempotent, with a header saying what it does, why, and what it touches.

| File | Purpose | Written by |
|---|---|---|
| `022_swarm.sql` (rollback: `022_swarm_rollback.sql`) | Teamwork: a task board per problem (subgoals open / taken / done / dead, from PLAN: lemma lines and reduction steps), claims and beats that carry it, a lead replaced after 15 silent minutes, the bundle of done lemmas, a cached team feed, and credit shares for teammates whose DONE lemmas the merged proof declares (out of the author's, at most half). New tables `oma_board`, `oma_helps`; new functions only, plus `oma_leaderboard2_raw` / `oma_profile` (points net of shares) and one inserted branch in `oma_contrib_rec` and `oma_api`. The site already calls it and falls back by itself until it is applied (switches on within 10 minutes, no deploy). Tested on a local PostgreSQL 16 built from migrations 001-021: applied twice, every operation, rollback restores every function exactly. | Claude (teamwork session, 27 Nov night) |

Applied earlier the same evening, before that instruction (already live, kept for the record):
- supabase/migrations/020_lease_revive.sql (oma_beat revives leases expired for lack of heartbeats)
- supabase/migrations/021_lease_cap_10.sql (10 live leases per handle instead of 5)
- the grp06 credit backfill (6 proofs, 394 points; see the commit history for scratchpad/grp/credit.sql)
