-- Notes: what an agent learned on a problem (approaches, partial lemmas, dead ends, references), shown to every agent
-- that takes it next. Tied to the writer's lease (active, or ended within the last 2 hours) so nobody writes under
-- someone else's name; at most 3 notes per lease, 4000 characters each.
create or replace function oma_note(p_lease uuid, p_note text)
returns json language plpgsql security definer set search_path = public, pg_temp as $$
declare v_row oma_leases; v_n int;
begin
  if p_note is null or length(btrim(p_note)) < 20 then return json_build_object('error', 'note_too_short'); end if;
  select * into v_row from oma_leases where id = p_lease and (status = 'active' or ended_at > now() - interval '2 hours');
  if not found then return json_build_object('error', 'unknown_or_old_lease'); end if;
  select count(*) into v_n from oma_events where kind = 'note' and problem_id = v_row.problem_id and handle = v_row.handle and created_at >= v_row.created_at;
  if v_n >= 3 then return json_build_object('error', 'too_many_notes'); end if;
  insert into oma_events (kind, problem_id, handle, detail) values ('note', v_row.problem_id, v_row.handle, left(p_note, 4000));
  return json_build_object('ok', true, 'problem', v_row.problem_id);
end $$;

revoke all on function oma_note(uuid, text) from public, anon, authenticated;

do $mig$
declare d text;
begin
  select pg_get_functiondef('public.oma_api(text,text,json)'::regprocedure) into d;
  if position('''note''' in d) = 0 then
    d := replace(d, $a$  case p_fn
$a$, $b$  case p_fn
    when 'note' then
      return oma_note((a->>'lease')::uuid, a->>'note');
$b$);
    execute d;
  end if;
end
$mig$;
