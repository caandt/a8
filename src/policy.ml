open Util
open Uint63

let read_policy path =
  let res = Hashtbl.create 16 in

  let update_list key values =
    let current_list =
      match Hashtbl.find_opt res key with
      | Some l -> l
      | None -> []
    in
    let new_list = List.fold_left (fun acc v -> v :: acc) current_list values in
    Hashtbl.replace res key new_list
  in

  let chan = open_in_bin path in
  try
    let header = Bytes.create 24 in
    really_input chan header 0 24;
    let nrets = Bytes.get_int64_ne header 8 |> Int64.to_int in

    for n = 0 to pred nrets do
      let start = ref (24 + n * 64) in
      while !start <> 0 do
        seek_in chan !start;
        let block = Bytes.create 64 in
        really_input chan block 0 64;

        let vals = ref [] in
        for i = 0 to 6 do
          let v = Bytes.get_int64_ne block (i * 8) in
          if v <> 0L then vals := v :: !vals
        done;

        if !vals <> [] then
          update_list (Int64.of_int n) !vals;

        start := Bytes.get_int64_ne block 56 |> Int64.to_int
      done
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

let devs_array lst =
  let rec aux acc = function
    | i :: c :: rest -> aux ((i, c) :: acc) rest
    | _ -> Array.of_list (List.rev acc)
  in aux [] lst
let irel devs x =
  let len = Array.length devs in
  let rec bsearch low high ans =
    if low > high then ans
    else
      let mid = low + (high - low) / 2 in
      let (i_mid, _) = devs.(mid) in
      let c_prev = if mid > 0 then snd devs.(mid - 1) else 0 in
      let s_mid = i_mid + c_prev in
      if s_mid <= x then
        bsearch (mid + 1) high mid
      else
        bsearch low (mid - 1) ans
  in
  let ans = bsearch 0 (len - 1) (-1) in
  if ans = -1 then x
  else
    let (i_ans, c_ans) = devs.(ans) in
    let e_ans = i_ans + c_ans in
    if x <= e_ans then i_ans
    else x - c_ans

let read_policy bpath ppath =
  let^ d = global_data bpath in
  let pol, dsets = read_policy ppath in
  let devs = devs_array (List.map toint d.devs) in
  let irel = irel devs in
  let pol' x =
    let ret = Option.value ~default:(of_int 999999999) (CFI.Rewriter.index (=) d.rets x zero) in
    ret |> to_int64 |> pol |> of_int in
  let dsets = List.map (List.map (fun x ->
    (Int64.sub (Int64.shift_right x 2) (to_int64 d.bi')) |> Int64.to_int |> irel |> of_int |> add d.bi
  )) dsets in
  Some (pol', dsets)
