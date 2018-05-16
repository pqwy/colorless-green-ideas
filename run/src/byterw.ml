(* module R2 = struct *)

(*   type t = { buf: bytes; miss: 'a. unit -> 'a; mutable i: int; mutable n: int } *)

(*   exception Miss *)
(*   exception Err of string *)

(*   open Bytes *)

(*   let run f buf = *)
(*     let t = { buf; i = 0; n = length buf; miss = fun _ -> raise Miss } in *)
(*     match f t with *)
(*     | res             -> Ok (Some (res, sub buf t.i (length buf - t.i))) *)
(*     | exception Miss  -> Ok None *)
(*     | exception Err e -> Format.printf "* parse err: %s\n%!" e; Error () *)

(*   let err fmt = Format.kasprintf (fun msg -> raise (Err msg)) fmt *)

(*   let isolate ({i; n} as t) k f = *)
(*     if k <= n then *)
(*       let t1  = { t with n = k; miss = fun _ -> err "isolate: underflow" } in *)
(*       let res = f t1 in *)
(*       if t1.n = 0 then ( t.i <- i + k; res) else err "isolate: overflow" *)
(*     else t.miss() *)

(*   open EndianBytes.BigEndian *)

(*   let u8 ({i; n} as t) = *)
(*     if n < 1 then t.miss() else (t.i <- i + 1; t.n <- n - 1; get_uint8 t.buf i) *)
(*   and u16 ({i; n} as t) = *)
(*     if n < 2 then t.miss() else (t.i <- i + 2; t.n <- n - 2; get_uint16 t.buf i) *)
(*   and i32 ({i; n} as t) = *)
(*     if n < 4 then t.miss() else (t.i <- i + 4; t.n <- n - 4; get_int32 t.buf i) *)
(*   and i64 ({i; n} as t) = *)
(*     if n < 8 then t.miss() else (t.i <- i + 8; t.n <- n - 8; get_int64 t.buf i) *)
(* end *)

module R = struct

  type r = { mutable i : int; buf : bytes }
  type 'a t = r -> 'a

  exception Err of string

  open Bytes

  let run f buf =
    let rd = { i = 0; buf } in
    match f rd with
    | res -> Ok (Some (res, sub buf rd.i (length buf - rd.i)))
    | exception Invalid_argument _ -> Ok None
    | exception Err e -> Format.printf "* parse error: %s\n%!" e; Error ()

  let err fmt = Format.kasprintf (fun msg -> raise (Err msg)) fmt

  let const ~or_err t v rd = if (t rd <> v) then err or_err

  let isolate n f ({i} as rd) =
    if i + n <= length rd.buf then
      let r1  = { i = 0; buf = sub rd.buf rd.i n } in
      let res = try f n r1 with Invalid_argument _ -> err "isolate: access" in
      if r1.i = n then (rd.i <- i + n; res) else err "isolate: leftovers"
    else invalid_arg "miss"

  let vec_ rd_n f rd = isolate (rd_n rd) f rd

  open EndianBytes.BigEndian

  let u8  ({i} as rd) = rd.i <- i + 1; get_uint8 rd.buf i
  let u16 ({i} as rd) = rd.i <- i + 2; get_uint16 rd.buf i
  let u24 ({i} as rd) = rd.i <- i + 3;
                        (get_uint16 rd.buf i lsl 8) lor (get_uint8 rd.buf (i + 2))
  let i32 ({i} as rd) = rd.i <- i + 4; get_int32 rd.buf i
  let i64 ({i} as rd) = rd.i <- i + 8; get_int64 rd.buf i
  let bytes n ({i} as rd) = rd.i <- i + n; sub rd.buf i n

  let sz_type = function
    n when n <= 0xff     -> u8
  | n when n <= 0xffff   -> u16
  | n when n <= 0xffffff -> u24
  | _                    -> assert false

  let vec ?s (a, b) f rd =
    let rd_n = match s with Some s -> s | None -> sz_type b in
    let n = rd_n rd in
    if a <= n && n <= b then isolate n f rd else err "vec: %d /= %d..%d" n a b

  let list ?s ab f rd =
    let rec go acc n rd =
      if rd.i < length rd.buf then go (f rd :: acc) n rd else List.rev acc in
    vec ?s ab (go []) rd
end

module W = struct

  open Buffer

  type w = Buffer.t
  type t = w -> unit

  let run f = let buf = Buffer.create 23 in (f buf; to_bytes buf)

  let (@+) a b wr = a wr; b wr
  let vec wn f w =
    let buf = run f in wn (Bytes.length buf) w; add_bytes w buf
  let list wn f xs = vec wn @@ fun w -> List.iter (fun x -> f x w) xs

  open EndianBytes.BigEndian

  let scratch = Bytes.create 8

  let u8 x w = set_int8 scratch 0 x; add_subbytes w scratch 0 1
  let u16 x w = set_int16 scratch 0 x; add_subbytes w scratch 0 2
  let u24 x w = set_int16 scratch 0 (x lsr 8); set_int8 scratch 2 (x land 0xff);
                add_subbytes w scratch 0 3
  let i32 x w = set_int32 scratch 0 x; add_subbytes w scratch 0 4
  let i64 x w = set_int64 scratch 0 x; add_subbytes w scratch 0 8
  let bytes b w = add_bytes w b
end
