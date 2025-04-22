include Stdlib.Uchar

let dec_invalid n = (n lsl 24) lor 0xFFFD
let[@inline] dec_ret n u = ((8 lor n) lsl n) lor u
let[@inline] not_in_x80_to_xBF b = b lsr 6 <> 0b10
let[@inline] not_in_xA0_to_xBF b = b lsr 5 <> 0b101
let[@inline] not_in_x80_to_x9F b = b lsr 5 <> 0b100
let[@inline] not_in_x90_to_xBF b = b < 0x90 || 0xBF < b
let[@inline] not_in_x80_to_x8F b = b lsr 4 <> 0x8
let[@inline] utf_8_uchar_2 b0 b1 = ((b0 land 0x1F) lsl 6) lor (b1 land 0x3F)

let[@inline] utf_8_uchar_3 b0 b1 b2 =
  ((b0 land 0x0F) lsl 12) lor ((b1 land 0x3F) lsl 6) lor (b2 land 0x3F)

let[@inline] utf_8_uchar_4 b0 b1 b2 b3 =
  ((b0 land 0x07) lsl 18)
  lor ((b1 land 0x3F) lsl 12)
  lor ((b2 land 0x3F) lsl 6)
  lor (b3 land 0x3F)

let get_utf_8_uchar b i =
  let b0 = Bytes.get_uint8 b i in
  (* raises if [i] is not a valid index. *)
  let get = Bytes.get_uint8 in
  let max = Bytes.length b - 1 in
  match Char.unsafe_chr b0 with
  (* See The Unicode Standard, Table 3.7 *)
  | '\x00' .. '\x7F' -> dec_ret 1 b0
  | '\xC2' .. '\xDF' ->
      let i = i + 1 in
      if i > max then dec_invalid 1
      else
        let b1 = get b i in
        if not_in_x80_to_xBF b1 then dec_invalid 1
        else dec_ret 2 (utf_8_uchar_2 b0 b1)
  | '\xE0' ->
      let i = i + 1 in
      if i > max then dec_invalid 1
      else
        let b1 = get b i in
        if not_in_xA0_to_xBF b1 then dec_invalid 1
        else
          let i = i + 1 in
          if i > max then dec_invalid 2
          else
            let b2 = get b i in
            if not_in_x80_to_xBF b2 then dec_invalid 2
            else dec_ret 3 (utf_8_uchar_3 b0 b1 b2)
  | '\xE1' .. '\xEC' | '\xEE' .. '\xEF' ->
      let i = i + 1 in
      if i > max then dec_invalid 1
      else
        let b1 = get b i in
        if not_in_x80_to_xBF b1 then dec_invalid 1
        else
          let i = i + 1 in
          if i > max then dec_invalid 2
          else
            let b2 = get b i in
            if not_in_x80_to_xBF b2 then dec_invalid 2
            else dec_ret 3 (utf_8_uchar_3 b0 b1 b2)
  | '\xED' ->
      let i = i + 1 in
      if i > max then dec_invalid 1
      else
        let b1 = get b i in
        if not_in_x80_to_x9F b1 then dec_invalid 1
        else
          let i = i + 1 in
          if i > max then dec_invalid 2
          else
            let b2 = get b i in
            if not_in_x80_to_xBF b2 then dec_invalid 2
            else dec_ret 3 (utf_8_uchar_3 b0 b1 b2)
  | '\xF0' ->
      let i = i + 1 in
      if i > max then dec_invalid 1
      else
        let b1 = get b i in
        if not_in_x90_to_xBF b1 then dec_invalid 1
        else
          let i = i + 1 in
          if i > max then dec_invalid 2
          else
            let b2 = get b i in
            if not_in_x80_to_xBF b2 then dec_invalid 2
            else
              let i = i + 1 in
              if i > max then dec_invalid 3
              else
                let b3 = get b i in
                if not_in_x80_to_xBF b3 then dec_invalid 3
                else dec_ret 4 (utf_8_uchar_4 b0 b1 b2 b3)
  | '\xF1' .. '\xF3' ->
      let i = i + 1 in
      if i > max then dec_invalid 1
      else
        let b1 = get b i in
        if not_in_x80_to_xBF b1 then dec_invalid 1
        else
          let i = i + 1 in
          if i > max then dec_invalid 2
          else
            let b2 = get b i in
            if not_in_x80_to_xBF b2 then dec_invalid 2
            else
              let i = i + 1 in
              if i > max then dec_invalid 3
              else
                let b3 = get b i in
                if not_in_x80_to_xBF b3 then dec_invalid 3
                else dec_ret 4 (utf_8_uchar_4 b0 b1 b2 b3)
  | '\xF4' ->
      let i = i + 1 in
      if i > max then dec_invalid 1
      else
        let b1 = get b i in
        if not_in_x80_to_x8F b1 then dec_invalid 1
        else
          let i = i + 1 in
          if i > max then dec_invalid 2
          else
            let b2 = get b i in
            if not_in_x80_to_xBF b2 then dec_invalid 2
            else
              let i = i + 1 in
              if i > max then dec_invalid 3
              else
                let b3 = get b i in
                if not_in_x80_to_xBF b3 then dec_invalid 3
                else dec_ret 4 (utf_8_uchar_4 b0 b1 b2 b3)
  | _ -> dec_invalid 1

let get_utf_8_uchar b i = of_int @@ get_utf_8_uchar b i

let pp fmt u =
  if is_char u then Format.fprintf fmt "'%c'" (to_char u)
  else Format.fprintf fmt "'\\x%04i'" (to_int u)

let to_string u = Format.asprintf "%a" pp u
