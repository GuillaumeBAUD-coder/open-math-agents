-- 019: every claim and every heartbeat reads the notes of a problem twice (oma_notes_since and max(id) of its notes, 016),
-- and every note counts the writer's notes: with this partial index they read a few entries instead of walking the
-- problem's whole history (oma_events_problem) and filtering on kind. Only note inserts write to it.
-- CONCURRENTLY: no lock on oma_events while it builds; it cannot run inside a transaction block, so run it on its own.
create index concurrently if not exists oma_events_notes on oma_events (problem_id, id) where kind = 'note';
