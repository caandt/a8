open Cmdliner

let lsr2 x = Uint63.l_sr x (Uint63.of_int 2)
let lsl2 x = Uint63.l_sl x (Uint63.of_int 2)
let u = Uint63.to_int64
let ( % ) = Fun.compose
let hex = Printf.sprintf "%Lx" % u

module Uint63 = struct
  include Uint63
  let pp fmt x = Format.pp_print_string fmt (hex x)
end
type ityp = [%import: CFI.Rewriter.ityp] [@@deriving show]
type eident = [%import: CFI.Rewriter.eident] [@@deriving show]
type ehdr = [%import: CFI.Rewriter.ehdr] [@@deriving show]
type phdr = [%import: CFI.Rewriter.phdr] [@@deriving show]

let read_policy policy_file =
  (fun _ -> Uint63.zero), []

let (let*) (opt, e) f =
  match opt with
  | Some x -> f x
  | None -> Error e

let vdso = List.map (lsr2 % Uint63.of_int) [0x7ff7ffe320;0x7ff7ffe820;0x7ff7ffe5c0;0x7ff7ffe808;0x7ff7ffe770]

type config = {
  update_symbols: bool;
  polhook: bool;
}
let main input output pol runtime config =
  let bin = In_channel.with_open_bin input In_channel.input_all in
  let bin = [Pstring.unsafe_of_string bin] in
  let runtime = [Pstring.unsafe_of_string runtime] in
  let* bin', dat = (
    if config.polhook then
      CFI.Rewriter.elf_rw_polhook bin runtime, "error rewriting"
    else
      let pol, dsets =
        match pol with
        | None -> (fun x -> x), []
        | Some p -> read_policy pol in
      CFI.Rewriter.elf_rw bin pol dsets runtime, "error rewriting"
    ) in
  if config.update_symbols then (
    let* elf' = Packager.load_mem (String.concat "" (List.map Pstring.to_string bin')), "Error reading input" in
    Packager.update_symbols elf' dat.rel;
    Ok (Packager.save_and_close elf' output)
  ) else
    Ok (Out_channel.with_open_bin output (fun oc -> List.iter (Out_channel.output_string oc) (List.map Pstring.to_string bin')))

let run input output pol runtime config =
  let output = Option.value output ~default:(input ^ "_rw") in
  let runtime = Option.fold ~some:(fun x -> In_channel.with_open_bin x In_channel.input_all) ~none:Runtime.data runtime in
  let res = main input output pol runtime config in
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

let abort =
  let doc = "The file containing the content of the abort segment." in
  let absent = "abort prints an error and exits" in
  Arg.(value & opt (some string) None & info ["A"; "abort"] ~docv:"ABORT" ~doc ~absent)

let update_symbols =
  let doc = "Enable updating symbols" in
  Arg.(value & flag & info ["s"; "symbols"] ~doc)
let polhook =
  let doc = "Use polhook" in
  Arg.(value & flag & info ["P"; "polhook"] ~doc)
let config =
  let make update_symbols polhook = { update_symbols; polhook } in
  Term.(const make $ update_symbols $ polhook)
let cmd =
  let term = Term.(const run $ input $ output $ policy $ abort $ config) in
  let info = Cmd.info "a64-cfi" ~doc:"CFI rewriter for AArch64" in
  Cmd.v info term

let () = exit (Cmd.eval_result cmd)
