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
type ityp_pp = [%import: CFI.Rewriter.ityp] [@@deriving show]

let debug_hook (dat: CFI.Rewriter.data) (id: CFI.Rewriter.i_data) chunk =
  (* if (lsl2 id.i |> u <> 0x400908L) then chunk else *)
  if (id.i |> u % lsl2 % dat.rel <> 0x4a7d04L) then chunk else
  match id.t0 with
  (* | Ignore -> chunk *)
  | _ ->
      let c = Option.fold ~some:(String.concat ";" % List.map hex) ~none:"none" chunk in
      Printf.printf "[%Lx]@%Lx: %s => [%s]\n" (u id.n) (lsl2 id.i|>u) (show_ityp_pp id.t0) c;
      Stdlib.flush Stdlib.stdout;
      chunk
(* let debug_hook _ _ x = x *)

let read_policy policy_file =
  (fun _ -> Uint63.zero), []

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

  let bi = lsr2 va in
  let bi' = Option.map Uint63.of_int bi' |> Option.value ~default:(Packager.get_after elf |> lsr2) in
  let bti = default_u63 bti default_bti in
  let ai = default_u63 ai default_ai in

  Printf.printf "bi:%Lx\nbi':%Lx\nbti:%Lx\nai:%Lx\n" (Uint63.to_int64 bi) (Uint63.to_int64 bi') (Uint63.to_int64 bti) (Uint63.to_int64 ai);
  let pol, dsets =
    match pol with
    | None -> (fun _ -> Uint63.zero), [List.init (List.length code) (fun x -> Uint63.add bi (Uint63.of_int x))]
    | Some p -> read_policy pol in

  let* (code', tbls), rel = CFI.Rewriter.rw debug_hook pol dsets code bi bi' bti ai, "Error rewriting code" in
  Packager.set_nx elf;
  let entry' = (Packager.get_entrypoint elf |> lsr2 |> rel |> lsl2) in
  Packager.set_entrypoint elf entry';
  let* _ = Packager.add_segment elf (List.concat code') (lsl2 bi'), "Error adding code segment" in
  let* _ = Packager.add_segment elf (List.concat tbls |> List.concat_map (fun x -> [Uint63.l_and x (Uint63.of_int 0xffff_ffff); Uint63.l_sr x (Uint63.of_int 32)])) (lsl2 bti), "Error adding table segment" in
  let* _ = Packager.add_segment elf (List.map Uint63.of_int [1;2;3]) (lsl2 ai), "Error adding abort segment" in
  Packager.save_and_close elf output;
  Printf.printf "Wrote %s\n" output;
  Ok ()

let run input output pol bi' bti ai abort =
  let output = Option.value output ~default:(input ^ "_rw") in
  let res = main input output pol bi' bti ai in
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
