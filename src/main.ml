open Cmdliner

let read_policy policy_file =
  match policy_file with
  | None -> fun _ -> []
  | Some p -> fun _ -> []

let (let*) (opt, e) f =
  match opt with
  | Some x -> f x
  | None -> Error e

let default_u63 int default =
  Option.fold ~none:(Uint63.of_int default) ~some:Uint63.of_int int

let default_bti = 0x2000_0000
let default_ai = 0x1fff_0000

let main input output pol bi' bti ai =
  let* elf = Packager.load input, "Error reading input" in
  let* code, va = Packager.get_text elf, "Error getting text content" in

  let bi = Uint63.l_sr va (Uint63.of_int 2) in
  let bi' = match bi' with | Some bi' -> Uint63.of_int bi' | None -> Packager.get_after elf in
  let bti = default_u63 bti default_bti in
  let ai = default_u63 ai default_ai in

  let* (code', tbl), rel = CFI.Rewriter.rw pol code bi bi' bti ai, "Error rewriting code" in
  Packager.set_nx elf;
  Packager.set_entrypoint elf (Packager.get_entrypoint elf |> rel);
  Packager.add_segment elf (List.concat code') bi';
  Packager.add_segment elf (List.concat tbl) bti;
  Packager.add_segment elf ([]) ai;
  Packager.save_and_close elf output;
  Printf.printf "Wrote %s\n" output;
  Ok ()

let run input output pol bi' bti ai =
  let output = Option.value output ~default:input ^ "_rw" in
  let pol = read_policy pol in
  main input output pol bi' bti ai

let input =
  let doc = "The input ELF to rewrite." in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"INPUT" ~doc)

let output =
  let doc = "The output path of the rewritten ELF." in
  let absent = "INPUT_rw" in
  Arg.(value & pos 1 (some string) None & info [] ~docv:"OUTPUT" ~doc ~absent)

let policy =
  let doc = "The policy file to use." in
  let absent = "use permissive policy" in
  Arg.(value & opt (some string) None & info ["p"; "policy"] ~docv:"POLICY" ~doc ~absent)

let bi' =
  let doc = "The index where the new code segment should be placed." in
  let absent = "place after the last original segment" in
  Arg.(value & opt (some int) None & info ["c"; "code"] ~docv:"INDEX" ~doc ~absent)

let bti =
  let doc = "The index where the policy table segment should be placed." in
  let absent = Printf.sprintf "use 0x%x" default_bti in
  Arg.(value & opt (some int) None & info ["t"; "table"] ~docv:"INDEX" ~doc ~absent)

let ai =
  let doc = "The index where the abort segment should be placed." in
  let absent = Printf.sprintf "use 0x%x" default_ai in
  Arg.(value & opt (some int) None & info ["a"; "abort"] ~docv:"INDEX" ~doc ~absent)

let cmd =
  let term = Term.(const run $ input $ output $ policy $ bi' $ bti $ ai) in
  let info = Cmd.info "a64-cfi" ~doc:"CFI rewriter for AArch64" in
  Cmd.v info term

let () = exit (Cmd.eval_result cmd)
