include Stdlib.Uchar

let to_string =
  let rec aux acc = function
    | 0 -> acc
    | n ->
        let byte = Char.chr @@ (n land 0xFF) in
        let n = n lsr 8 in
        aux (Seq.cons byte acc) n
  in
  fun c -> String.of_seq (aux Seq.empty (to_int c))

let pp fmt u = Format.fprintf fmt "%s" (to_string u)
