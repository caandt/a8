let rec process = function
  | var_name::file_path::rest ->
      let data = In_channel.with_open_bin file_path In_channel.input_all in
      Printf.printf "let %s = %S\n" var_name data;
      process rest
  | _ -> ()

let () = process (List.tl (Array.to_list Sys.argv))
