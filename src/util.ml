open Uint63

let lsr2 x = l_sr x (of_int 2)
let lsl2 x = l_sl x (of_int 2)
let ( % ) = Fun.compose
let to64 = Uint63.to_int64
let toint = Int64.to_int % to64
let hex = Printf.sprintf "%Lx" % to64

let (let*) (opt, e) f =
  match opt with
  | Some x -> f x
  | None -> Error e
let (let^) = Option.bind

module Uint63 = struct
  include Uint63
  let pp fmt x = Format.pp_print_string fmt (hex x)
end
type ityp = [%import: CFI.Rewriter.ityp] [@@deriving show]
type eident = [%import: CFI.Rewriter.eident] [@@deriving show]
type ehdr = [%import: CFI.Rewriter.ehdr] [@@deriving show]
type phdr = [%import: CFI.Rewriter.phdr] [@@deriving show]
type hash = [%import: CFI.Rewriter.hash] [@@deriving show]

let global_data ?(pol=Fun.id) ?(dsets=[]) ?(runtime=Runtime.base) path =
  let^ elf = Packager.load path in
  let^ code, va = Packager.get_text elf in
  let bi = lsr2 va in
  let bi' = Packager.get_after elf |> lsr2 in
  CFI.Rewriter.global_data code bi bi' pol dsets (String.length runtime |> Uint63.of_int)
