(***********************************************************)
(*  Copyright (C) 2010                                     *)
(*  Michel Ludwig (michel.ludwig@liverpool.ac.uk)          *)
(*  University of Liverpool                                *)
(*                                                         *)
(*  This program is free software; you can redistribute    *)
(*  it and/or modify it under the terms of the GNU         *)
(*  General Public License as published by the Free        *)
(*  Software Foundation; either version 3 of the License,  *)
(*  or (at your option) any later version.                 *)
(*                                                         *)
(*  This program is distributed in the hope that it will   *)
(*  be useful, but WITHOUT ANY WARRANTY; without even      *)
(*  the implied warranty of MERCHANTABILITY or FITNESS     *)
(*  FOR A PARTICULAR PURPOSE.  See the GNU General Public  *)
(*  License for more details.                              *)
(*                                                         *)
(*  You should have received a copy of the GNU General     *)
(*  Public License along with this program; if not, see    *)
(*  <http://www.gnu.org/licenses/>.                        *)
(***********************************************************)

open Owl2
open Types

type t

val create : unit -> t

val normalise_subsumption_axiom : t -> Ontology.t -> Ontology.occurrence_hash -> StringSet.t ref -> string -> ClassExpression.t -> ClassExpressionAxiom.Constructor.t list

val normalise_equivalence_axiom : t -> Ontology.t -> Ontology.occurrence_hash -> StringSet.t ref -> string -> ClassExpression.t -> ClassExpressionAxiom.Constructor.t list

val normalise_domain_axiom : t -> Ontology.t -> Ontology.occurrence_hash -> StringSet.t ref -> ObjectPropertyExpression.t -> ClassExpression.t -> ClassExpressionAxiom.Constructor.t list

val normalise_range_axiom : t -> Ontology.t -> Ontology.occurrence_hash -> StringSet.t ref -> ObjectPropertyExpression.t -> ClassExpression.t -> ClassExpressionAxiom.Constructor.t list


val new_symbols_introduced : t -> int

(* kate: replace-tabs on; indent-width 2; *)