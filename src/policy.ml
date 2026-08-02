open Util
open Uint63

let read_policy path =
  let res = Hashtbl.create 16 in
  let chan = open_in_bin path in
  try
    let header = Bytes.create 24 in
    really_input chan header 0 24;
    let nrets = Bytes.get_int64_ne header 8 |> Int64.to_int in

    for n = 0 to pred nrets do
      let start = ref (24 + n * 64) in
      let vals = ref [] in
      while !start <> 0 do
        seek_in chan !start;
        let block = Bytes.create 64 in
        really_input chan block 0 64;
        for i = 0 to 6 do
          let v = Bytes.get_int64_ne block (i * 8) in
          if v <> 0L then vals := v :: !vals
        done;
        start := Bytes.get_int64_ne block 56 |> Int64.to_int
      done;
      if !vals <> [] then
        Hashtbl.add res (Int64.of_int n) !vals;
    done;
    close_in chan;
    let keys_and_lists = Hashtbl.fold (fun k v acc -> (k, v) :: acc) res [] in
    let lists = List.map snd keys_and_lists in
    let lookup = Hashtbl.create (List.length keys_and_lists) in
    List.iteri (fun idx (k, _) -> Hashtbl.add lookup k idx) keys_and_lists;
    ((fun k -> Option.value ~default:99999999 (Hashtbl.find_opt lookup k)), lists)
  with exn ->
    close_in_noerr chan;
    raise exn

let inv lst t =
  let rec aux i sum = function
    | [] -> i
    | x :: xs ->
        let next_sum = add sum x in
        if lt t next_sum then i
        else aux (add one i) next_sum xs
  in aux zero zero lst

let irel d i' =
  let lens = List.map CFI.Rewriter.chunksize d.chunks in
  add d.arg.bi (inv lens (sub i' d.arg.bi'))

let read_policy bpath ppath =
  let^ d = global_data ~runtime:Runtime.polhook ~hook:CFI.Rewriter.polhook bpath in
  let pol, dsets = read_policy ppath in
  let irel = irel d in
  let pol' x =
    let ret = Option.value ~default:999999999 (List.find_index ((=) x) d.rets) in
    ret |> Int64.of_int |> pol |> of_int in
  let dsets = List.map (List.map (fun x -> x |> of_int64 |> lsr2 |> irel)) dsets in
  Some (pol', dsets)
