open Ctypes
open Foreign

type elf = unit ptr
let elf: elf typ = ptr void

let parse =
  foreign "lief_parse"
    (string @-> returning elf)

let get_text =
  foreign "lief_get_text"
    (elf @-> ptr size_t @-> returning (ptr uint32_t))

let set_entrypoint =
  foreign "lief_set_entrypoint"
    (elf @-> uint64_t @-> returning int)

let add_segment =
  foreign "lief_add_segment"
    (elf @-> ptr uint32_t @-> size_t @-> uint64_t @-> returning int)

let write_and_free =
  foreign "lief_write_and_free"
    (elf @-> string @-> returning void)
