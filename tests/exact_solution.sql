-- Run against a fresh, disposable PostgreSQL database with the migrations loaded.
begin;

do $$
begin
  if exists (select from oma_solutions) or exists (select from oma_private.config) then
    raise exception 'exact_solution.sql requires a fresh database';
  end if;
end;
$$;

insert into oma_private.config (key, value)
values ('api_secret_sha256', encode(sha256(convert_to(repeat('fixture ', 4), 'UTF8')), 'hex'));

insert into oma_solutions
  (problem_id, handle, pr_url, verdict, created_at, polarity, agent, model, points, contributors)
values
  ('fixture.target', 'wrong', 'test:rejected', 'rejected', '2026-01-01 00:00:00+00', 'proof', null, null, 0, null),
  ('fixture.target', 'first', 'test:first', 'accepted', '2026-01-02 00:00:00+00', 'disproof', 'agent', 'model', 20, '["peer"]'),
  ('fixture.target', 'later', 'test:later', 'accepted', '2026-01-03 00:00:00+00', 'proof', null, null, 1, null),
  ('fixture.nearby', 'other', 'test:other', 'accepted', '2026-01-04 00:00:00+00', 'proof', null, null, 1, null),
  ('fixture.rejected', 'other', 'test:rejected-only', 'rejected', '2026-01-05 00:00:00+00', 'proof', null, null, 0, null);

set local role anon;

do $$
declare
  fixture_secret text := repeat('fixture ', 4);
  actual jsonb;
  expected jsonb;
begin
  if has_function_privilege(current_user, 'oma_solution(text)', 'EXECUTE') then
    raise exception 'anonymous clients must use the gated API';
  end if;
  begin
    perform oma_api('wrong', 'solution', '{"problem":"fixture.target"}');
    raise exception 'invalid secrets must not be accepted';
  exception when insufficient_privilege then
    null;
  end;

  select s into expected from jsonb_array_elements(oma_api(fixture_secret, 'solved', '{}')::jsonb) s
  where s->>'problem_id' = 'fixture.target';
  actual := oma_api(fixture_secret, 'solution', '{"problem":"fixture.target"}');
  if actual is distinct from expected or actual->>'handle' is distinct from 'first' then
    raise exception 'expected the same first accepted record from both lookups, got %', actual;
  end if;
  if oma_api(fixture_secret, 'solution', '{"problem":"fixture.rejected"}') is not null
     or oma_api(fixture_secret, 'solution', '{"problem":"fixture"}') is not null
     or oma_api(fixture_secret, 'solution', '{}') is not null then
    raise exception 'expected null for rejected-only, missing, and empty lookups';
  end if;
end;
$$;

rollback;
