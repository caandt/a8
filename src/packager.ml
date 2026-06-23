open Ctypes
open Foreign
open Unsigned

let u63_of_u32 x = x |> UInt32.to_int64 |> Uint63.of_int64
let u32_of_u63 x = x |> Uint63.to_int64 |> UInt32.of_int64
let u64_of_u63 x = x |> Uint63.to_int64 |> UInt64.of_int64

let to_u63_list (arr: uint32 CArray.t) =
  arr |> CArray.to_list |> List.map u63_of_u32

let of_u63_list (lst: Uint63.t list) =
  lst |> List.map u32_of_u63 |> CArray.of_list uint32_t

let load (filepath: string) =
  let handle = Lief.parse filepath in
  if is_null handle then None else Some handle

let get_text (elf: Lief.elf) =
  let elements_ptr = allocate size_t (Size_t.of_int 0) in
  let data_ptr = Lief.get_text elf elements_ptr in

  if is_null data_ptr then None
  else
    let elements = Size_t.to_int (!@ elements_ptr) in
    let arr = CArray.from_ptr data_ptr elements in
    Some (to_u63_list arr)

let set_entrypoint (elf: Lief.elf) (entry: Uint63.t) =
  let entry = u64_of_u63 entry in
  Lief.set_entrypoint elf entry

let add_segment (elf: Lief.elf) (data: Uint63.t list) (addr: Uint63.t) =
  let arr = of_u63_list data in
  let ptr = CArray.start arr in
  let len = CArray.length arr |> Size_t.of_int in
  let addr = addr |> Uint63.to_int64 |> UInt64.of_int64 in
  Lief.add_segment elf ptr len addr

let save_and_close (elf: Lief.elf) (out_path: string) =
  Lief.write_and_free elf out_path;
  Unix.chmod out_path 0o755
