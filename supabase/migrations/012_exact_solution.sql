-- Look up the first accepted record without fetching the solved catalogue.
create or replace function oma_solution(p_problem text)
returns json language sql stable security definer set search_path = public, pg_temp as $$
  select row_to_json(s) from (
    select problem_id, handle, agent, model, polarity, pr_url, points, contributors, created_at
    from oma_solutions
    where problem_id = p_problem and verdict = 'accepted'
    order by created_at
    limit 1
  ) s;
$$;

revoke all on function oma_solution(text) from public, anon, authenticated;

do $mig$
declare d text;
begin
  select pg_get_functiondef('public.oma_api(text,text,json)'::regprocedure) into d;
  if position('''solution''' in d) = 0 then
    d := replace(d, $a$  case p_fn
$a$, $b$  case p_fn
    when 'solution' then
      return oma_solution(a->>'problem');
$b$);
    execute d;
  end if;
end
$mig$;
