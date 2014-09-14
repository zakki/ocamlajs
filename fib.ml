module List = struct
  let rec map f = function
    | [] -> []
    | a::l -> let r = f a in r :: map f l
end

let rec fib x =
  if x <= 1 then 1
  else fib (x - 1) + fib (x -2)

let rec ffib x =
  if x <= 1.0 then 1.0
  else ffib (x -. 1.) +. ffib (x -. 2.)

let fcl l x =
  let n = x * 2 in
  List.map (fun v -> v + n) l

let _ =
  (* print_int (fib 1); *)
  (* print_int (fib 2); *)
  for i = 0 to 10 do
    print_int (fib 40)
  done;
  print_endline "";
  (* for i = 0 to 100 do *)
  (*   print_float (ffib 32.0) *)
  (* done; *)
  (* print_endline ""; *)
  ()


