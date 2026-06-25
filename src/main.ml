open Cmdliner

type ityp_pp =
[%import: CFI.Rewriter.ityp
          [@with Uint63.t := Uint63.t [@printer (fun x y -> Format.pp_print_string x (Uint63.to_string y))]]]
[@@deriving show]

let debug_hook (i: CFI.Rewriter.i_data) x =
  match x with
  | Ignore -> x
  | _ ->
      let n = Uint63.to_int64 i.n in
      let i = Uint63.to_int64 i.i in
      Printf.printf "@%Lx: [%Lx] %s\n" (Int64.mul i 4L) n (show_ityp_pp x); x
(* let debug_hook _ x = x *)

let read_policy policy_file =
  match policy_file with
  | None -> (fun _ -> Uint63.zero), []
  | Some p -> (fun _ -> Uint63.zero), []

let (let*) (opt, e) f =
  match opt with
  | Some x -> f x
  | None -> Error e

let default_u63 int default =
  Option.fold ~none:(Uint63.of_int default) ~some:Uint63.of_int int

let default_bti = 0x2000_0000
let default_ai = 0x1fff_0000

let main input output pol dsets bi' bti ai =
  let* elf = Packager.load input, "Error reading input" in
  let* code, va = Packager.get_text elf, "Error getting text content" in

  let bi = Uint63.l_sr va (Uint63.of_int 2) in
  let bi' = match bi' with | Some bi' -> Uint63.of_int bi' | None -> Packager.get_after elf in
  let bti = default_u63 bti default_bti in
  let ai = default_u63 ai default_ai in

  let* (code', tbl), rel = CFI.Rewriter.rw debug_hook pol dsets code bi bi' bti ai, "Error rewriting code" in
  Packager.set_nx elf;
  Packager.set_entrypoint elf (Packager.get_entrypoint elf |> rel);
  Packager.add_segment elf (List.concat code') bi';
  Packager.add_segment elf (List.concat tbl) bti;
  Packager.add_segment elf ([]) ai;
  Packager.save_and_close elf output;
  Printf.printf "Wrote %s\n" output;
  Ok ()

let run input output pol bi' bti ai abort =
  let output = Option.value output ~default:(input ^ "_rw") in
  let pol, dsets = read_policy pol in
  let res = main input output pol dsets bi' bti ai in
  Stdlib.flush Stdlib.stdout;
  res

let input =
  let doc = "The input ELF to rewrite." in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"INPUT" ~doc)

let output =
  let doc = "The output path of the rewritten ELF." in
  let absent = "save to INPUT_rw" in
  Arg.(value & pos 1 (some string) None & info [] ~docv:"OUTPUT" ~doc ~absent)

let policy =
  let doc = "The policy file to use." in
  let absent = "use permissive policy" in
  Arg.(value & opt (some string) None & info ["p"; "policy"] ~docv:"POLICY" ~doc ~absent)

let bi' =
  let doc = "The index where the new code segment should be placed." in
  let absent = "place after the last original segment" in
  Arg.(value & opt (some int) None & info ["c"; "code"] ~docv:"CODE_IDX" ~doc ~absent)

let bti =
  let doc = "The index where the policy table segment should be placed." in
  let absent = Printf.sprintf "use 0x%x" default_bti in
  Arg.(value & opt (some int) None & info ["t"; "table"] ~docv:"TBL_IDX" ~doc ~absent)

let ai =
  let doc = "The index where the abort segment should be placed." in
  let absent = Printf.sprintf "use 0x%x" default_ai in
  Arg.(value & opt (some int) None & info ["a"; "abort-index"] ~docv:"ABT_IDX" ~doc ~absent)

let abort =
  let doc = "The file containing the content of the abort segment." in
  let absent = "abort prints an error and exits" in
  Arg.(value & opt (some string) None & info ["A"; "abort"] ~docv:"ABORT" ~doc ~absent)

let cmd =
  let term = Term.(const run $ input $ output $ policy $ bi' $ bti $ ai $ abort) in
  let info = Cmd.info "a64-cfi" ~doc:"CFI rewriter for AArch64" in
  Cmd.v info term

let () = exit (Cmd.eval_result cmd)
