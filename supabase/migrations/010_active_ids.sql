-- Ids of every problem or step with at least one event (taken, sent, proved, released...). The site asks for this small
-- list once a minute and skips the per-problem history query for the ~99% of problems nobody has touched, so crawlers
-- and sweeps over 59,000 problem pages cost no database call.
create or replace function oma_active_ids()
returns json language sql stable security definer set search_path = public, pg_temp as $$
  select coalesce(json_agg(problem_id order by problem_id), '[]'::json) from (select distinct problem_id from oma_events) t;
$$;

revoke all on function oma_active_ids() from public, anon, authenticated;

do $mig$
declare d text;
begin
  select pg_get_functiondef('public.oma_api(text,text,json)'::regprocedure) into d;
  if position('''active_ids''' in d) = 0 then
    d := replace(d, $a$  case p_fn
$a$, $b$  case p_fn
    when 'active_ids' then
      return oma_active_ids();
$b$);
    execute d;
  end if;
end
$mig$;
