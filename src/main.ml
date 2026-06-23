open Cmdliner

let read_policy policy_file =
  match policy_file with
  | None -> fun _ -> []
  | Some p -> fun _ -> []

let (let*) (opt, e) f =
  match opt with
  | Some x -> f x
  | None -> Error e

let (let@) (int, e) f =
  match int with
  | 0 -> f ()
  | _ -> Error e

let main input output pol =
  let* elf = Packager.load input, "Error reading input" in
  let* code = Packager.get_text elf, "Error getting text content" in
  Printf.printf "size: %d\n" (List.length code);
  let x = Uint63.of_int 0 in
  let* ((code', tbl), rel) = CFI.Rewriter.rw pol code x x x x, "Error rewriting code" in
  let@ _ = Packager.set_entrypoint elf x, "Error setting entrypoint" in
  let@ _ = Packager.add_segment elf (List.concat code') x, "Error adding new code segment" in
  let@ _ = Packager.add_segment elf (List.concat tbl) x, "Error adding policy table segment" in
  let@ _ = Packager.add_segment elf ([]) x, "Error adding abort segment" in
  Ok (Packager.save_and_close elf output)

let run input output pol =
  let output = Option.value output ~default:input ^ "_rw" in
  let pol = read_policy pol in
  match main input output pol with
  | Error e -> print_endline e; exit 1
  | _ -> Printf.printf "Wrote %s\n" output

let input_arg =
  let doc = "The input ELF to rewrite" in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"INPUT" ~doc)

let output_arg =
  let doc = "The output path of the rewritten ELF (defaults to INPUT_rw)." in
  Arg.(value & pos 1 (some string) None & info [] ~docv:"OUTPUT" ~doc)

let config_arg =
  let doc = "The policy file to use" in
  let absent = "permissive policy" in
  Arg.(value & opt (some string) None & info ["p"; "policy"] ~docv:"POLICY" ~doc ~absent)

let cmd =
  let term = Term.(const run $ input_arg $ output_arg $ config_arg) in
  let info = Cmd.info "a64-cfi" ~doc:"CFI rewriter for AArch64" in
  Cmd.v info term

let () = exit (Cmd.eval cmd)
