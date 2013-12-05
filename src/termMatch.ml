type pattern =
| Glob of Term.constr Lazy.t
| App of pattern * pattern
| Lam of string * pattern * pattern
| Get of string
| Ref of string
| Ignore

exception Match_failure

let rec match_pattern p e ctx s =
  match p with
  | Ignore -> s
  | Glob name ->
    begin
      if Term.eq_constr (Lazy.force name) e
      then
	s
      else
	raise Match_failure
    end
  | App _ ->
    begin
      match Term.kind_of_term e with
      | Term.App (f, args) ->
	  match_app f args (Array.length args - 1) p ctx s
      | _ -> raise Match_failure
    end
  | Lam (nm, pty, pbody) ->
    begin
      match Term.kind_of_term e with
      | Term.Lambda (n, t, c) ->
	assert false
      | _ -> raise Match_failure
    end
  | Get nm ->
    begin
      try
	let v = Hashtbl.find s nm in
	if Term.eq_constr e v then
	  s
	else
	  raise Match_failure
      with
	Not_found ->
	  let _ = Hashtbl.add s nm e in
	  s
    end
  | Ref n ->
    assert false
and match_app f args i p ctx s =
  if i < 0
  then match_pattern p f ctx s
  else
    match p with
      App (fp , arg_p) ->
	let s = match_app f args (i - 1) fp ctx s in
	match_pattern arg_p args.(i) ctx s
    | _ ->
      match_pattern p (Term.mkApp (f, Array.sub args 0 (i + 1))) ctx s

let matches gl ls e =
  let x = Hashtbl.create 5 in
  let rec recur ls =
    match ls with
    | [] -> raise Match_failure
    | (p,f) :: ls ->
      try
	f (match_pattern p e gl x)
      with
	Match_failure ->
	  let _ = Hashtbl.clear x in
	  recur ls
  in
  recur ls


let dbg msg =
  Format.printf "%s\n" msg
