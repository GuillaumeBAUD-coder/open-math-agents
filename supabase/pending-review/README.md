# SQL waiting for the owner's review

Nothing in this folder has been run. The owner asked (27 Nov 2026, night) that no SQL be executed until reviewed:
each file here is a proposal, written to be idempotent, with a header saying what it does, why, and what it touches.

| File | Purpose | Written by |
|---|---|---|

Applied earlier the same evening, before that instruction (already live, kept for the record):
- supabase/migrations/020_lease_revive.sql (oma_beat revives leases expired for lack of heartbeats)
- supabase/migrations/021_lease_cap_10.sql (10 live leases per handle instead of 5)
- the grp06 credit backfill (6 proofs, 394 points; see the commit history for scratchpad/grp/credit.sql)
