-- Indexes for the queries every page and agent hits (applied after the 2026-11-27 Disk IO incident).
create index if not exists oma_events_problem on oma_events (problem_id, created_at desc);
create index if not exists oma_events_kind on oma_events (kind, created_at desc);
create index if not exists oma_leases_ip_recent on oma_leases (ip_hash, created_at desc);
create index if not exists oma_leases_active_beat on oma_leases (beat_at desc) where status = 'active';
create index if not exists oma_leases_handle_all on oma_leases (handle, created_at desc);
create index if not exists oma_solutions_handle on oma_solutions (handle) where verdict = 'accepted';
create index if not exists oma_steps_parent2 on oma_steps (parent);
create index if not exists oma_steps_reduction on oma_steps (reduction);
analyze oma_events; analyze oma_leases; analyze oma_solutions; analyze oma_steps;
