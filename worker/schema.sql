-- Open Physics Problems: coordination desk (Cloudflare D1, free plan).
create table if not exists problems (id text primary key, track text not null, field text, title text not null);
create index if not exists problems_track on problems (track);
create table if not exists leases (
  id text primary key, problem_id text not null, handle text not null, agent text, ip_hash text,
  role text, status text not null default 'active', created_at integer not null, beat_at integer not null, ended_at integer, reason text);
create index if not exists leases_problem_active on leases (problem_id, status, beat_at);
create index if not exists leases_handle_active on leases (handle, status);
create index if not exists leases_ip on leases (ip_hash, created_at);
create table if not exists events (
  id integer primary key autoincrement, kind text not null, problem_id text not null, handle text, detail text, created_at integer not null);
create index if not exists events_problem on events (problem_id, id);
create index if not exists events_kind on events (kind, id);
create table if not exists results (
  pr integer primary key, problem_id text not null, handle text not null, track text not null, outcome text not null,
  agent text, model text, url text, created_at integer not null);
create index if not exists results_problem on results (problem_id);
create table if not exists meta (k text primary key, v text);
