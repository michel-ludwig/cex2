(***********************************************************)
(*  Copyright (C) 2009                                     *)
(*  Yevgeny Kazakov <yevgeny.kazakov@comlab.ox.ac.uk>      *)
(*  University of Oxford                                   *)
(*                                                         *)
(*  This library is free software; you can redistribute it *)
(*  and/or modify it under the terms of the GNU Lesser     *)
(*  General Public License as published by the Free        *)
(*  Software Foundation; either version 2.1 of the         *)
(*  License, or (at your option) any later version.        *)
(*                                                         *)
(*  This library is distributed in the hope that it will   *)
(*  be useful, but WITHOUT ANY WARRANTY; without even the  *)
(*  implied warranty of MERCHANTABILITY or FITNESS FOR A   *)
(*  PARTICULAR PURPOSE. See the GNU Lesser General Public  *)
(*  License for more details.                              *)
(*                                                         *)
(*  You should have received a copy of the GNU Lesser      *)
(*  General Public License along with this library; if     *)
(*  not write to the Free Software Foundation, Inc., 51    *)
(*  Franklin Street, Fifth Floor, Boston, MA  02110-1301   *)
(*  USA                                                    *)
(***********************************************************)

(* the necessary information for RBox reasoning from the ontology is kept  *)
(* in index                                                                *)

open Owl2
open Consed.T
module O = Ontology
module H = ObjectProperty.HMap
module S = ObjectProperty.Set
module M = ObjectProperty.Map
module RS = Brole.Set
module RM = Brole.Map
module RC = ObjectPropertyExpression.Constructor
module AC = ObjectPropertyAxiom.Constructor

(* information stored for every role [r] *)
type role_record = {
  (* the set of subproperties *)
  mutable subprop : RS.t;
(*|  (*| - a map from roles [r] to the set of role [S] so that [r o S => a]      *)*)
(*|  mutable subcomp : RS.t RM.t;                                                  *)
(*|  (*| - a map from roles [r] to the set of role [S] so that [r o S => (inv a)]*)*)
(*|  mutable subcompi : RS.t RM.t;                                                 *)
}

type t = {
  hrr : role_record H.t;
  (* the set of transitive atomic roles *)
  mutable trans_roles : S.t;
  (* the set of functional roles *)
  mutable funct_roles : S.t;
  (* the set of inverse functional roles *)
  mutable inv_funct_roles : S.t;
}

let create_role_record () = {
  subprop = RS.empty;
(*|  subcomp = RM.empty; *)
(*|  subcompi = RM.empty;*)
}

let create i = {
  hrr = H.create i;
  trans_roles = S.empty;
  funct_roles = S.empty;
  inv_funct_roles = S.empty;
}

let estimated_role_index_size ont =
  Polarity.Counter.get_pos (O.count_ObjectSomeValuesFrom ont)

let init ont =
  let index = create (estimated_role_index_size ont) in
  (* initialize told predecessors adding implications between roles if     *)
  (* [imp = true], or, otherwise, inverse implication to the index         *)
  let add_subrole r s imp =
    let add_subr a r =
      let rr = try H.find index.hrr a
        with Not_found ->
            let rr = create_role_record () in H.add index.hrr a rr; rr
      in rr.subprop <- Brole.Set.add r rr.subprop
    in
    match r.data, s.data with
    | RC.ObjectProperty a, RC.ObjectProperty b -> add_subr a (b, imp)
    | RC.ObjectProperty a, RC.InverseObjectProperty b -> add_subr a (b, not imp)
    | RC.InverseObjectProperty a, RC.ObjectProperty b -> add_subr a (b, not imp)
    | RC.InverseObjectProperty a, RC.InverseObjectProperty b -> add_subr a (b, imp)
  in
  
  let add_trans_role r =
    match r.data with
    | RC.ObjectProperty a ->
        index.trans_roles <- S.add a index.trans_roles
    | RC.InverseObjectProperty a ->
        index.trans_roles <- S.add a index.trans_roles
  in
  
  let add_funct_role r =
    match r.data with
    | RC.ObjectProperty a ->
        index.funct_roles <- S.add a index.funct_roles
    | RC.InverseObjectProperty a ->
        index.inv_funct_roles <- S.add a index.inv_funct_roles
  in
  
  let add_inv_funct_role r =
    match r.data with
    | RC.ObjectProperty a ->
        index.inv_funct_roles <- S.add a index.inv_funct_roles
    | RC.InverseObjectProperty a ->
        index.funct_roles <- S.add a index.funct_roles
  in
  
  O.iter_record_ObjectPropertyAxiom (fun ax -> match ax.data with
          | AC.SubObjectPropertyOf ([r], s) ->
              add_subrole s r true
          | AC.EquivalentObjectProperties op_lst ->
              begin match op_lst with
                | op_c :: op_rest ->
                    List.iter (fun op ->
                            add_subrole op op_c true;
                            add_subrole op_c op true
                      ) op_rest
                | _ -> invalid_arg "IndexRBox.add_inv_funct_role"
              end
          | AC.InverseObjectProperties (r, s) ->
              add_subrole s r false;
              add_subrole r s false
          | AC.FunctionalObjectProperty r ->
              add_funct_role r
          | AC.InverseFunctionalObjectProperty r ->
              add_inv_funct_role r
          | AC.TransitiveObjectProperty r ->
              add_trans_role r
          | _ -> ()
    ) ont;
  (*|  Gc.compact ();  (* <- slow but useful in the long run *)*)
  index
;;
