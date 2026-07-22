open Cmdliner
open Util
open Uint63

type config = {
  update_symbols: bool;
  polhook: bool;
  input: string;
  output: string;
  pol: string option;
  runtime: string;
  json: string option;
  onlyjson: bool;
}

let serialize_dat (d:CFI.Rewriter.data) : Yojson.Basic.t =
  let ji x = `Int (toint x) in
  `Assoc [
    ("bi", ji d.bi);
    ("bi'", ji d.bi');
    ("bti", ji d.bti);
    ("ai", ji d.ai);
    ("len", `Int (List.length d.code));
    ("devs", `List (List.map ji d.devs));
    ("dsets", `List (List.map (fun d -> `List (List.map ji d)) d.dsets));
    ("tc", `List (List.map (fun ((h, tbl), ti) -> `Assoc [
      ("hash", match h with H_UBFX (a, b) -> `List [ji a; ji b]);
      ("tbl", `List (List.map ji tbl));
      ("ti", ji ti);
    ]) d.tc));
    ("pol", `List (List.init (List.length d.code) ((+) (toint d.bi)) |>
      List.filter_map (fun i ->
        let lbl = d.pol (of_int i) in
        if lt lbl (List.length d.tc |> of_int)
        then Some (`List [`Int i; ji lbl])
        else None)));
    ("rets", `List (List.map ji d.rets));
  ]

let save args bin' (dat: CFI.Rewriter.data) =
  Option.iter (fun file -> Yojson.Basic.to_file file (serialize_dat dat)) args.json;
  if args.update_symbols then (
    let* elf' = Packager.load_mem (String.concat "" (List.map Pstring.to_string bin')), "Error reading input" in
    Packager.update_symbols elf' dat.rel;
    Ok (Packager.save_and_close elf' args.output)
  ) else
    Ok (Out_channel.with_open_bin args.output (fun oc -> List.iter (Out_channel.output_string oc) (List.map Pstring.to_string bin')))

let main args =
  let bin = In_channel.with_open_bin args.input In_channel.input_all in
  let bin = [Pstring.unsafe_of_string bin] in
  let runtime = [Pstring.unsafe_of_string args.runtime] in
  let getpol () = (match args.pol with
    | None -> Some (Fun.id, [])
    | Some p -> Policy.read_policy args.input p), "Error reading policy" in

  if args.onlyjson then
    let* pol, dsets = getpol () in
    let* dat = global_data ~pol ~dsets args.input, "Error getting data" in
    Ok (Option.iter (fun file -> Yojson.Basic.to_file file (serialize_dat dat)) args.json)
  else if args.polhook then
    let* bin', dat = CFI.Rewriter.elf_rw_polhook bin runtime, "Error rewriting" in
    save args bin' dat
  else
    let* pol, dsets = getpol () in
    let* bin', dat = CFI.Rewriter.elf_rw (fun _ _ x -> x) bin pol dsets runtime, "Error rewriting" in
    save args bin' dat

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
  let doc = "Use policy collection hook" in
  Arg.(value & flag & info ["P"; "polhook"] ~doc)
let json =
  let doc = "Dump JSON data to $(docv), or dump to OUTPUT and exit if $(docv) is \"only\"" in
  Arg.(value & opt (some string) None & info ["j"; "json"] ~docv:"FILE" ~doc)
let config =
  let make input output runtime pol update_symbols polhook json =
    let output = Option.value output ~default:(input ^ "_rw") in
    let runtime = Option.fold runtime
      ~some:(fun x -> In_channel.with_open_bin x In_channel.input_all)
      ~none:(if polhook then Runtime.polhook else Runtime.base) in
    let onlyjson = json = Some "only" in
    let json = if json = Some "only" then Some output else json in
    { input; output; update_symbols; polhook; runtime; pol; json; onlyjson; } in
  Term.(const make $ input $ output $ abort $ policy $ update_symbols $ polhook $ json)
let cmd =
  let term = Term.(const main $ config) in
  let info = Cmd.info "a64-cfi" ~doc:"CFI rewriter for AArch64" in
  Cmd.v info term

let () = exit (Cmd.eval_result cmd)
