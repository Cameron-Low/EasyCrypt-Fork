(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcFol
open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* FIXME: add t_low* to all these tactics                               *)

(* -------------------------------------------------------------------- *)
val t_equivF_conseq       : form -> form -> FApi.backward
val t_equivS_conseq       : form -> form -> FApi.backward
val t_eagerF_conseq       : form -> form -> FApi.backward
val t_hoareF_conseq       : form -> form -> FApi.backward
val t_hoareS_conseq       : form -> form -> FApi.backward
val t_cHoareF_conseq      : form -> form -> FApi.backward
val t_cHoareS_conseq      : form -> form -> FApi.backward
val t_bdHoareF_conseq     : form -> form -> FApi.backward
val t_bdHoareS_conseq     : form -> form -> FApi.backward

val t_cHoareF_conseq_c    : cost -> FApi.backward
val t_cHoareS_conseq_c    : cost -> FApi.backward
val t_cHoareF_conseq_full : form -> form -> cost -> FApi.backward
val t_cHoareS_conseq_full : form -> form -> cost -> FApi.backward
val t_bdHoareS_conseq_bd  : hoarecmp -> form -> FApi.backward
val t_bdHoareF_conseq_bd  : hoarecmp -> form -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_equivF_conseq_nm    : form -> form -> FApi.backward
val t_equivS_conseq_nm    : form -> form -> FApi.backward
val t_hoareF_conseq_nm    : form -> form -> FApi.backward
val t_hoareS_conseq_nm    : form -> form -> FApi.backward
val t_cHoareF_conseq_nm   : form -> form -> FApi.backward
val t_cHoareS_conseq_nm   : form -> form -> FApi.backward
val t_bdHoareF_conseq_nm  : form -> form -> FApi.backward
val t_bdHoareS_conseq_nm  : form -> form -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_equivS_conseq_bd : side -> EcFol.form -> EcFol.form ->FApi.backward

(* -------------------------------------------------------------------- *)
val t_conseq : form -> form -> FApi.backward

(* -------------------------------------------------------------------- *)
val process_conseq   : bool -> conseq_ppterm option tuple3 -> FApi.backward
val process_bd_equiv : side -> pformula pair -> FApi.backward

(* -------------------------------------------------------------------- *)
val process_conseq_opt :
  pcqoptions -> conseq_ppterm option tuple3 -> FApi.backward

(* -------------------------------------------------------------------- *)
val t_conseqauto : ?delta:bool -> ?tsolve:FApi.backward -> FApi.backward
