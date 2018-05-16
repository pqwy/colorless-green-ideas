open Rresult

let _ = Nocrypto_entropy_unix.initialize ()

let xdb = Nocrypto.Uncommon.xdb ~address:true ~ascii:true ()

let pmsg tag = Format.printf "%s: @[%a@]\n\n%!" tag xdb
let pkeys tag (k1, k2) =
  Format.printf "%s: @[k1 = %a@,k2 = %a@]\n\n%!" tag xdb k1 xdb k2

open Tls.Proto.Record

let rec chat a b = match Lazy.(force a, force b) with
  Err e       , _           -> Error (`Left e)
| _           , Err e       -> Error (`Right e)
| Tick a      , _           -> chat a b
| _           , Tick b      -> chat a b
| Data (x, a) , _           -> pmsg "A DATA" x; chat a b
| _           , Data (x, b) -> pmsg "B DATA" x; chat a b
| Send (x, a) , Cont k      -> pmsg "A SEND" x; chat a (recv k x)
| Cont k      , Send (x, b) -> pmsg "B SEND" x; chat (recv k x) b
| Cont k1     , Cont k2     -> Ok (k1, k2)
| _ -> assert false

let rec transfer (k1, k2) = function
  []    -> Ok (k1, k2)
| x::xs -> chat (send k1 x) (lazy (Cont k2)) >>= fun ks -> transfer ks xs

module Sock = struct

  open Lwt.Infix

  type t = { s : Lwt_unix.file_descr; mutable k : bytes evt -> bytes resp }

  let rec drain data s (lazy x) = match x with
    Err e       -> Lwt.fail_with (Bytes.to_string e)
  | Data (d, x) -> drain (d::data) s x
  | Tick x      -> drain data s x
  | Cont k      -> Lwt.return (k, List.rev data)
  | Send (m, x) -> let n = Bytes.length m in
                   Lwt_unix.write s m 0 n >>= fun n' ->
                     assert (n = n'); drain data s x

  let readk =
    let b = Bytes.make 8192 '\000' in fun s k ->
      Lwt_unix.read s b 0 8192 >>= fun n ->
        drain [] s (recv k (Bytes.sub b 0 n))

  let don't_receive = function (k, []) -> Lwt.return k | _ -> assert false

  let addr host port = Unix.(ADDR_INET (inet_addr_of_string host, port))

  let cert () =
    let f = Unix.(openfile "../rondom/cert/server.pem.asn" [O_RDONLY] 0)
    and b = Bytes.make 8192 '\000' in
    let res = Bytes.sub b 0 (Unix.read f b 0 8192) in
    Unix.close f; res


  let client ?(g = Rand.create())  (host, port) =
    let open Lwt_unix in
    let s = socket PF_INET SOCK_STREAM 0 in
    connect s (addr host port) >>= fun () ->
      drain [] s (client g) >>= fun (k, _) ->
        readk s k >>= don't_receive >|= fun k -> { s; k }

  let server ?(g = Rand.create()) ?(cert = cert()) port =
    let open Lwt_unix in
    let ss = socket PF_INET SOCK_STREAM 0 in
    bind ss (addr "127.0.0.1" port) >>= fun _ ->
    listen ss 1;
    accept ss >>= fun (s, _) ->
    (* close ss >>= fun () -> *)
    drain [] s (server g cert) >>= fun (k, _) ->
    readk s k >>= don't_receive >>= fun k ->
    readk s k >>= don't_receive >|= fun k -> { s; k }

  let send t raw =
    drain [] t.s (send t.k raw) >>= don't_receive >|= fun k -> t.k <- k

  let recv t = readk t.s t.k >|= fun (k, d) -> t.k <- k; d
end


(* module W = struct *)

(*   open Generated.Coroutine *)
(*   open Tls.Proto.Handshake *)

(*   let hs_chat = *)
(*     let rec go a b = match a, b with *)
(*       Err _, _ | _, Err _ -> a, b *)
(*     | Send (RqSend msg, a), Recv k -> pmsg "A" msg; go a (k msg) *)
(*     | Send (RqKeys (_, ks), a), b  -> pkeys "A" ks; go a b *)
(*     | Recv k, Send (RqSend msg, b) -> pmsg "B" msg; go (k msg) b *)
(*     | a, Send (RqKeys (_, ks), b)  -> pkeys "B" ks; go a b *)
(*     | a, b -> a, b in *)
(*     go *)
(* end *)


(* module X = struct *)

(*   open Tls.Proto.Record.V1 *)

(*   let rec chat a b = match Lazy.(force a, force b) with *)
(*     Err e       , _           -> Error (`Left e) *)
(*   | _           , Err e       -> Error (`Right e) *)
(*   | Tick a      , _           -> chat a b *)
(*   | _           , Tick b      -> chat a b *)
(*   | Data (x, a) , _           -> pmsg "A DATA" x; chat a b *)
(*   | _           , Data (x, b) -> pmsg "B DATA" x; chat a b *)
(*   | Send (x, a) , Cont k      -> pmsg "A SEND" x; chat a (recv k x) *)
(*   | Cont k      , Send (x, b) -> pmsg "B SEND" x; chat (recv k x) b *)
(*   | Cont k1     , Cont k2     -> Ok (k1, k2) *)
(*   | _ -> assert false *)

(*   let rec transfer (k1, k2) = function *)
(*     []    -> Ok (k1, k2) *)
(*   | x::xs -> chat (send k1 x) (lazy (Cont k2)) >>= fun ks -> transfer ks xs *)

(* end *)
(* module Y = struct *)

(*   open Tls.Proto.Record.V2 *)

(*   let rec chat a b = match a, b with *)
(*     Err e       , _           -> Error (`Left e) *)
(*   | _           , Err e       -> Error (`Right e) *)
(*   | Data (x, a) , _           -> pmsg "A DATA" x; chat a b *)
(*   | _           , Data (x, b) -> pmsg "B DATA" x; chat a b *)
(*   | Send (x, a) , State b     -> pmsg "A SEND" x; chat a (recv b x) *)
(*   | State a     , Send (x, b) -> pmsg "B SEND" x; chat (recv a x) b *)
(*   | State a     , State b     -> Ok (a, b) *)
(*   | _ -> assert false *)

(*   let rec transfer (s1, s2) = function *)
(*     []    -> Ok (s1, s2) *)
(*   | x::xs -> chat (send s1 x) (State s2) >>= fun ss -> transfer ss xs *)
(* end *)
