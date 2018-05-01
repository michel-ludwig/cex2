(***********************************************************)
(*  Copyright (C) 2010                                     *)
(*  Michel Ludwig (michel.ludwig@gmail.com)                *)
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
open Consed.T
open Ontology
open Utilities

module C = Class.Constructor
module OP = ObjectProperty.Constructor 
module CE = ClassExpression.Constructor
module CEA = ClassExpressionAxiom.Constructor
module OPE = ObjectPropertyExpression.Constructor

type renaming_type = ConceptEquality | ConceptSubsumption

type t = { mutable symbol_counter : int;
          (* Records bindings 'renaming type * 'renamed expression' -> 'renaming concept name' *)
           mutable renamingHash : (Ontology.t * renaming_type * ClassExpression.t, string) Hashtbl.t}

let create () = { symbol_counter = -1; renamingHash = Hashtbl.create 50 }

(* WARNING: We assume that the character ':' cannot occur in regular concept names! *)
let new_concept_name normalisationInformation = 
  let counter = normalisationInformation.symbol_counter + 1
  in
  normalisationInformation.symbol_counter <- counter;
  ":RN" ^ (string_of_int counter)

let find_renaming_class_expression normalisationInformation ont typ exp =
  try
    let conceptName = Hashtbl.find normalisationInformation.renamingHash (ont, typ, exp) in
    (conceptName, concept_name_class_expression ont conceptName)
  with Not_found ->
    let newConceptName = new_concept_name normalisationInformation in
    Hashtbl.add normalisationInformation.renamingHash (ont, typ, exp) newConceptName;
    (newConceptName, concept_name_class_expression ont newConceptName)

let addToLeftHandSideSet leftHandSideSet cname =
  leftHandSideSet := Types.StringSet.add !leftHandSideSet cname

(* Splits expression of the form A = some r. Top into A \sqsubseteq some r. Top and dom(r) \sqsubseteq A *)
let splitDomainExistsExpression ont leftHandSideSet r newTotalCName newExpression =
  addToLeftHandSideSet leftHandSideSet newTotalCName;
  let newTotalCNameExpression = concept_name_class_expression ont newTotalCName in
  [(subsumption_axiom ont newTotalCNameExpression newExpression).data;
   domain_subsumption_axiom ont (role_name_object_property_expression ont r) newTotalCNameExpression]

let rename_expression normalisationInformation ont occurrenceHash leftHandSideSet typ newExpression =
  let (newTotalCName, newTotalCNameExpression) = find_renaming_class_expression normalisationInformation ont typ newExpression in
  let newAxiom = match typ with
                  ConceptEquality -> (match is_domain_exists_expression newExpression with (* we don't want to have expressions of the form A = some r. Top in the *)
                                        None -> begin                                      (* terminology *)
                                                insert_in_occurrence_hash occurrenceHash (singleton_list_to_element (concept_names_in_class_expression newTotalCNameExpression))
                                                                                         (concept_names_in_class_expression newExpression);
                                                addToLeftHandSideSet leftHandSideSet newTotalCName;
                                                [(definition_axiom ont newTotalCNameExpression newExpression).data]
                                                end
                                      | Some r -> splitDomainExistsExpression ont leftHandSideSet r newTotalCName newExpression)
                | ConceptSubsumption -> addToLeftHandSideSet leftHandSideSet newTotalCName;
                                        [(subsumption_axiom ont newTotalCNameExpression newExpression).data]
  in
  (newTotalCNameExpression, newAxiom)

let rec rename normalisationInformation ont occurenceHash leftHandSideSet typ exp renameExists renameAnd =
    match exp.data with
      CE.Class _ -> (exp, [])
    | CE.ObjectIntersectionOf (exp1, exp2) ->
          (* there is no need to rename 'and' below this 'and' *)
          let (newExp1, newAxiomList1) = rename normalisationInformation ont occurenceHash leftHandSideSet typ exp1 true false in
          let (newExp2, newAxiomList2) = rename normalisationInformation ont occurenceHash leftHandSideSet typ exp2 true false in
          let newAxiomList = List.rev_append newAxiomList1 newAxiomList2 in
          let newExpression = (cons_ClassExpression ont (construct_ObjectIntersectionOf(newExp1, newExp2)))
          in
            if renameAnd then
              let (newTotalCNameExpression, newAxioms) = rename_expression normalisationInformation ont occurenceHash leftHandSideSet typ newExpression
              in
              (newTotalCNameExpression, List.rev_append newAxioms newAxiomList)
            else
              (newExpression, newAxiomList)
    | CE.ObjectSomeValuesFrom (r, e) ->
        let (newE, newAxioms1) = rename normalisationInformation ont occurenceHash leftHandSideSet typ e true true in
        let newExpression = exists_rC_class_expression ont r newE
        in
        if is_atomic newE && (not renameExists) then
          (newExpression, newAxioms1)
        else (* rename 'newExpression' *)
          let (newTotalCNameExpression, newAxioms2) = rename_expression normalisationInformation ont occurenceHash leftHandSideSet typ newExpression
          in
          (newTotalCNameExpression, List.rev_append newAxioms1 newAxioms2)
    | _ -> failwith "Wrong constructor encountered."


(* 'rename_complex_exists_rC t occurrenceHash exp' renames expressions of the form (some r C)  *)
(* in 'exp' if they don't occur on the top-most level. If C is not a concept name or Top, then *)
(* it is renamed as well.                                                                      *)
(* The expression that should replace 'exp' is returned, together with a list of axioms        *)
(* which define the newly introduced concept names. The new concept names are also inserted    *)
(* into 'occurenceHash'.                                                                       *)
let rename_complex_exists_rC normalisationInformation ont occurrenceHash leftHandSideSet typ exp =
  rename normalisationInformation ont occurrenceHash leftHandSideSet typ exp false false

let rename_complex normalisationInformation ont occurrenceHash leftHandSideSet typ exp =
  rename normalisationInformation ont occurrenceHash leftHandSideSet typ exp true true

let normalise_subsumption_axiom normalisationInformation  ont occurrenceHash leftHandSideSet conceptName exp =
  let (newExp, l) = rename_complex_exists_rC normalisationInformation ont occurrenceHash leftHandSideSet ConceptSubsumption exp in 
  (CEA.SubClassOf (concept_name_class_expression ont conceptName, newExp))::l

let normalise_equivalence_axiom normalisationInformation ont occurrenceHash leftHandSideSet conceptName exp =
  let (a, l) = rename_complex_exists_rC normalisationInformation ont occurrenceHash leftHandSideSet ConceptEquality exp in
  (match is_domain_exists_expression a with (* we don't want to have expressions of the form A = some r. Top in the *)
     None -> begin                          (* terminology (except for role domain bindings) *)
              insert_in_occurrence_hash occurrenceHash conceptName (concept_names_in_class_expression a);
              (CEA.EquivalentClasses ((concept_name_class_expression ont conceptName)::a::[]))::l
             end
   | Some r -> List.rev_append (splitDomainExistsExpression ont leftHandSideSet r conceptName a) l)

let normalise_domain_axiom normalisationInformation ont occurrenceHash leftHandSideSet objPropertExp exp =
  let (a, l) = rename_complex normalisationInformation ont occurrenceHash leftHandSideSet ConceptSubsumption exp
  in
  (domain_subsumption_axiom ont objPropertExp a)::l

let normalise_range_axiom normalisationInformation ont occurrenceHash leftHandSideSet objPropertExp exp =
  let (a, l) = rename_complex normalisationInformation ont occurrenceHash leftHandSideSet ConceptSubsumption exp
  in
  (range_subsumption_axiom ont objPropertExp a)::l

let new_symbols_introduced t = t.symbol_counter + 1

(* kate: replace-tabs on; indent-width 2; *)