type id = int option
and src_id = id
and dst_id = id

type info = ..
type info += Terminate | Resume | Pause | Sleep of int

module MDebug = Debug.Make ((val Debug.Config.disable))
open Core
open Domainslib

exception Terminated

type message =
  | Broadcast of src_id * id Hash_set.Poly.t * info
  | Request of src_id * dst_id * info
  | Response of src_id * dst_id * info

type t = { queue : message Chan.t; length : int Atomic.t; max_client : int }

let is_terminate = function Terminate -> true | _ -> false
let is_resume = function Resume -> true | _ -> false
let is_pause = function Pause -> true | _ -> false
let is_sleep = function Sleep _ -> true | _ -> false
let str_of_id = function Some id -> sprintf "#%d" id | None -> "#N/A"

let str_of_info = function
  | Terminate -> "terminate"
  | Resume -> "resume"
  | Pause -> "pause"
  | Sleep s -> sprintf "sleep %d's" s
  | _ -> "unknown_info"

let str_of_message_context (src, dst, info) =
  sprintf "%s -> %s : %s" (str_of_id src) (str_of_id dst) (str_of_info info)

let str_of_message = function
  | Broadcast (src, _, info) ->
      sprintf "[Boardcast] %s" @@ str_of_message_context (src, None, info)
  | Request (src, dst, info) ->
      sprintf "[Request] %s" @@ str_of_message_context (src, dst, info)
  | Response (src, dst, info) ->
      sprintf "[Response] %s" @@ str_of_message_context (src, dst, info)

let update_max_client t max_client = { t with max_client }
let mk_broadcast src_id info = Broadcast (src_id, Hash_set.Poly.create (), info)
let mk_request src_id dst_id info = Request (src_id, dst_id, info)
let mk_response src_id dst_id info = Response (src_id, dst_id, info)

let create max_client =
  { queue = Chan.make_unbounded (); length = Atomic.make 0; max_client }

let send t message =
  Atomic.incr t.length;
  Chan.send t.queue message

let receive t =
  if Atomic.get t.length > 0 then Atomic.decr t.length;
  let ret = Chan.recv_poll t.queue in
  ret

let iter messenger ~f =
  let rec inner i infos =
    if i <= 0 then ()
    else
      match receive messenger with
      | Some msg ->
          f msg;
          send messenger msg;
          inner (i - 1) infos
      | None -> ()
  in
  inner (Atomic.get messenger.length)

let map messenger ~f =
  let rec inner i infos =
    if i <= 0 then ()
    else
      match receive messenger with
      | Some msg ->
          send messenger (f msg);
          inner (i - 1) infos
      | None -> ()
  in
  inner (Atomic.get messenger.length)

let filter messenger ~f =
  let rec inner i rets =
    if i <= 0 then rets
    else
      match receive messenger with
      | Some msg ->
          if f msg then inner (i - 1) (msg :: rets)
          else (
            send messenger msg;
            inner (i - 1) rets)
      | None -> rets
  in
  inner (Atomic.get messenger.length) []

let find messenger ~f =
  let rec inner i =
    if i <= 0 then None
    else
      match receive messenger with
      | Some msg ->
          if f msg then Some msg
          else (
            send messenger msg;
            inner (i - 1))
      | None -> None
  in
  inner (Atomic.get messenger.length)

let send_boardcast messenger src_id info =
  if messenger.max_client > 1 then send messenger (mk_broadcast src_id info)

let receive_boardcast messenger my_id =
  match receive messenger with
  | Some (Broadcast (src_id, received, info))
    when Stdlib.(src_id <> my_id) && Fn.non (Hash_set.mem received) my_id ->
      Hash_set.add received my_id;
      if Hash_set.length received < messenger.max_client - 1 then
        send messenger @@ Broadcast (src_id, received, info);
      Some (src_id, info)
  | Some msg ->
      send messenger msg;
      None
  | None -> None

let receive_all_infos_with messenger my_id ~filter =
  let rec inner i infos =
    if i <= 0 then infos
    else
      match receive messenger with
      | Some (Broadcast (src_id, received, info))
        when Stdlib.(src_id <> my_id)
             && (not @@ Hash_set.mem received my_id)
             && filter info ->
          Hash_set.add received my_id;
          if Hash_set.length received < messenger.max_client - 1 then
            send messenger @@ Broadcast (src_id, received, info);
          inner (i - 1) @@ ((src_id, info) :: infos)
      | Some (Request (src_id, dst_id, info))
        when Stdlib.(my_id = dst_id) && filter info ->
          inner (i - 1) @@ ((src_id, info) :: infos)
      | Some (Response (src_id, dst_id, info))
        when Stdlib.(my_id = dst_id) && filter info ->
          inner (i - 1) @@ ((src_id, info) :: infos)
      | Some msg ->
          send messenger msg;
          inner (i - 1) infos
      | None -> infos
  in
  inner (Atomic.get messenger.length) []

let receive_all_infos = receive_all_infos_with ~filter:(fun _ -> true)

let send_request messenger src dst info =
  let message = mk_request src dst info in
  MDebug.print @@ lazy ("** Send " ^ str_of_message message);
  send messenger message

let receive_request ?(src = None) messenger dst =
  find messenger ~f:(function
    | Request (src0, dst0, _) when Stdlib.(dst0 = dst) -> (
        match src with Some src -> Stdlib.(src0 = src) | _ -> true)
    | _ -> false)
  |> function
  | Some (Request (src0, dst0, info) as message) ->
      MDebug.print @@ lazy ("** receive " ^ str_of_message message);
      Some (src0, dst0, info)
  | _ -> None

let wait_request ?(src = None) messenger dst ~f =
  let request = ref None in
  while Option.is_none !request do
    request :=
      find messenger ~f:(function
        | Request (src0, dst0, info) when Stdlib.(dst0 = dst) && f info -> (
            match src with Some src -> Stdlib.(src0 = src) | _ -> true)
        | _ -> false);
    ignore @@ Core_unix.nanosleep 0.1
  done;
  match !request with
  | Some (Request (src0, dst0, info) as message) ->
      MDebug.print @@ lazy ("** receive " ^ str_of_message message);
      (src0, dst0, info)
  | _ -> assert false

let exec_request messenger (src, dst, info) =
  match info with
  | Terminate ->
      send messenger (mk_response dst src Terminate);
      raise Terminated
  | Sleep s ->
      send messenger (mk_response dst src (Sleep s));
      Core_unix.sleep s
  | Pause ->
      send messenger (mk_response dst src Pause);
      ignore
      @@ wait_request messenger ~src:(Some src) dst ~f:(function
           | Resume -> true
           | _ -> false);
      send messenger (mk_response dst src Resume)
  | Resume -> send messenger (mk_response dst src Resume)
  | _ -> ()

let receive_request messenger_opt id =
  match messenger_opt with
  | None -> ()
  | Some messenger -> (
      match receive_request messenger id with
      | None -> ()
      | Some request -> exec_request messenger request)

let wait_response messenger src dst ~f =
  while
    Option.is_none
    @@ find messenger ~f:(function
         | Response (src0, dst0, info) as message
           when Stdlib.(src0 = dst) && Stdlib.(dst0 = src) && f info ->
             MDebug.print @@ lazy ("** receive " ^ str_of_message message);
             true
         | _ -> false)
  do
    ignore @@ Core_unix.nanosleep 0.1
  done
