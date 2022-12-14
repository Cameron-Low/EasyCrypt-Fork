(* -------------------------------------------------------------------- *)

(* Global / mutable EasyCrypt state that can be attached to an
 * environment - and shared by all the decendant of such an
 * environment. This state can be used to register notification
 * functions or global flags (e.g. profiling / tracing) *)
type gstate

(* -------------------------------------------------------------------- *)
val create : unit -> gstate
val copy   : gstate -> gstate

val from_flags : (string * bool) list -> gstate

(* -------------------------------------------------------------------- *)
type value = [ `Int of int ]

val asint : default:int -> value option -> int

val getvalue : string -> gstate -> value option
val setvalue : string -> value -> gstate -> unit

(* -------------------------------------------------------------------- *)
val getflag : ?default:bool -> string -> gstate -> bool
val setflag : string -> bool -> gstate -> unit

(* --------------------------------------------------------------------- *)
val old_mem_restr : string
val get_old_mem_restr : gstate -> bool

(* --------------------------------------------------------------------- *)
type nid_t
type loglevel = [`Debug | `Info | `Warning | `Critical]

val string_of_loglevel : loglevel -> string
val max_loglevel : loglevel -> loglevel -> loglevel

val accept_log   : level:loglevel -> wanted:loglevel -> bool
val add_notifier : (loglevel -> string Lazy.t -> unit) -> gstate -> nid_t
val rem_notifier : nid_t -> gstate -> unit
val loglevel     : gstate-> loglevel
val set_loglevel : loglevel -> gstate -> unit
val notify       : loglevel -> string Lazy.t -> gstate -> unit
