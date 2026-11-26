-- stats returned every solved problem with its author, pull request and date (66 KB and growing with each proof), on
-- every home page and search. The site only needs ids and polarity there; the full records stay in 'solved'.
do $mig$
declare d text;
begin
  select pg_get_functiondef('public.oma_stats()'::regprocedure) into d;
  if position('problem_id, handle, polarity, pr_url, created_at from oma_solutions' in d) > 0 then
    d := replace(d, 'problem_id, handle, polarity, pr_url, created_at from oma_solutions', 'problem_id, polarity from oma_solutions');
    execute d;
  end if;
end
$mig$;
