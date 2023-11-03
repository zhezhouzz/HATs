open Core
open Commands

let () =
  Command_unix.run
    (Command.group ~summary:"Poirot" (Ctest.test_cmds @ Cri.typecheck_cmds))
