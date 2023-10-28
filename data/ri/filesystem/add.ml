let add (path : int) (bytes : int) : bool =
  if exists path then false
  else
    let parent_path = parent path in
    if not (exists parent_path) then false
    else
      let (bytes' : int) = get parent_path in
      if isDir bytes' then (
        put path content;
        put parent_path (addChild bytes' path);
        true)
      else false
