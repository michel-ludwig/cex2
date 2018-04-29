%{
(***********************************************************)
(*  Copyright (C) 2009                                     *)
(*  Yevgeny Kazakov <yevgeny.kazakov@comlab.ox.ac.uk>      *)
(*  University of Oxford                                   *)
(*                                                         *)
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

open Ontology;;
open Owl2 ;;
open Normalisation;;
open Types
open Utilities;;

(* abbreviations for commonly used modules *)

module O = Ontology

module C = Class.Constructor
module OP = ObjectProperty.Constructor 
module CE = ClassExpression.Constructor
module OPE = ObjectPropertyExpression.Constructor

module CEA = ClassExpressionAxiom.Constructor
module OPA = ObjectPropertyAxiom.Constructor
module A = Assertion.Constructor

(*let parse_error s =            *)
(*  Printf.fprintf stderr "%s" s;*)
(*  raise Parsing.Parse_error    *)
(*;;                             *)

let checkIfConceptNameHashOccurredLeftAlready leftHandSideSet conceptName =
  if StringSet.mem !leftHandSideSet conceptName then
    failwith("Concept name " ^ conceptName ^ " already occurred on the left-hand side of a concept axiom!")
  else
    leftHandSideSet := StringSet.add !leftHandSideSet conceptName
%}

/* parentheses */
%token LeftParen RightParen

/* axioms keywords */
%token Implies Equivalent EquivalentRole ImpliesRole Inverse Functional
%token Transitive Composition Domain Range

/* properties */
%token DomainProperty RangeProperty RightIdentityProperty ParentsProperty ParentProperty

/* constructors */
%token And Or Some All Not Inv Top Bottom

/* identifiers */
%token <string> Identifier

/* comments */
%token <string> Comment

/* eof */
%token EOF

%start ontology
%type <Types.StringSet.t ref -> Normalisation.t -> Ontology.t * Ontology.occurrence_hash * Normalisation.t> ontology
%%

ontology : axioms EOF { $1 }

/* the second argument is a occurrence hash, i.e. a hash containing for every
 * definition (equivalent A C) occurring in the ontology the mapping
 * "A -> [concept names occurring in C]"                                       */
axioms : /* empty */ { fun leftHandSideSet normalisationInformation -> (O.create (), O.create_occurrence_hash (), normalisationInformation) }
 | axioms axiom      { fun leftHandSideSet normalisationInformation -> let (ont, occurrenceHash, normalisationInformation) = ($1 leftHandSideSet normalisationInformation)
                                                                        in $2 ont occurrenceHash normalisationInformation leftHandSideSet;
                                                                        (ont, occurrenceHash, normalisationInformation) }
;;

axiom :
   concept_axiom { fun ont occurrenceHash normalisationInformation leftHandSideSet -> List.iter (fun a -> O.add_ClassExpressionAxiom ont a)
                                                                                                ($1 ont occurrenceHash normalisationInformation leftHandSideSet) }
 | role_axiom    { fun ont _ _ _ -> O.add_ObjectPropertyAxiom ont ($1 ont) }
 | ignored_role_axiom  { fun _ _ _ _ -> () }
 | domain_axiom  { fun ont occurrenceHash normalisationInformation leftHandSideSet -> List.iter (fun a -> O.add_ClassExpressionAxiom ont a)
                                                                                                ($1 normalisationInformation ont occurrenceHash leftHandSideSet) }
 | range_axiom   { fun ont occurrenceHash normalisationInformation leftHandSideSet -> List.iter (fun a -> O.add_ClassExpressionAxiom ont a)
                                                                                                ($1 normalisationInformation ont occurrenceHash leftHandSideSet) }
 | domain_range_axiom   { fun ont occurrenceHash normalisationInformation leftHandSideSet -> List.iter (fun a -> O.add_ClassExpressionAxiom ont a)
                                                                                                       ($1 normalisationInformation ont occurrenceHash leftHandSideSet) }
;;

concept_axiom : concept_axiom_  { fun ont occurrenceHash normalisationInformation leftHandSideSet -> List.rev_map (O.cons_ClassExpressionAxiom ont)
                                                                                                                  ($1 ont occurrenceHash normalisationInformation leftHandSideSet) }

/* FIX below: "natural" definitions occurring in terminologies should be taken into account, i.e. axioms of the form A = some r.B */

concept_axiom_ :
   LeftParen Implies concept_name RightParen
   { fun ont _ _ leftHandSideSet ->
       checkIfConceptNameHashOccurredLeftAlready leftHandSideSet $3;
       [ CEA.SubClassOf (concept_name_class_expression ont $3, concept_name_class_expression ont $3)]
   }
 | LeftParen Implies concept_name concept RightParen
   { fun ont occurrenceHash normalisationInformation leftHandSideSet ->
       checkIfConceptNameHashOccurredLeftAlready leftHandSideSet $3;
       normalise_subsumption_axiom normalisationInformation ont occurrenceHash leftHandSideSet $3 ($4 ont)
   }
 | LeftParen Equivalent concept_name concept RightParen
   { fun ont occurrenceHash normalisationInformation leftHandSideSet ->
       checkIfConceptNameHashOccurredLeftAlready leftHandSideSet $3;
       normalise_equivalence_axiom normalisationInformation ont occurrenceHash leftHandSideSet $3 ($4 ont)
   }
;;

concept_name:
   Identifier
   { $1 }
;;

concept : concept_ { fun ont -> cons_ClassExpression ont ($1 ont) }
concept_:
   Identifier
   { fun ont -> (CE.Class (C.IRI (cons_IRI ont (IRI.Constructor.IRI $1)))) }
 | LeftParen And and_concepts RightParen
   { fun ont -> $3 ont }
 | LeftParen Some role Top RightParen
   { fun ont -> CE.ObjectSomeValuesFrom ($3 ont, top_class_expression ont) }
 | LeftParen Some role concept RightParen
   { fun ont -> CE.ObjectSomeValuesFrom ($3 ont, $4 ont) }
;;

and_concepts : and_concepts_ { fun ont ->  ($1 ont) }
and_concepts_:
   concept concept
   { fun ont -> construct_ObjectIntersectionOf($1 ont, $2 ont) }
 | and_concepts concept
   { fun ont -> construct_ObjectIntersectionOf(cons_ClassExpression ont ($1 ont), $2 ont) }
;;

role : role_ { fun ont -> cons_ObjectPropertyExpression ont ($1 ont) }
role_:
   Identifier
   { fun ont -> OPE.ObjectProperty (cons_ObjectProperty ont (OP.IRI (cons_IRI ont (IRI.Constructor.IRI $1)))) }
;;

role_axiom : role_axiom_ { fun ont -> cons_ObjectPropertyAxiom ont ($1 ont) }
role_axiom_:
    LeftParen ImpliesRole role RightParen
    { fun ont -> OPA.SubObjectPropertyOf ([$3 ont], $3 ont) }
  | LeftParen ImpliesRole role role RightParen 
    { fun ont -> OPA.SubObjectPropertyOf ([$3 ont], $4 ont) }
  | LeftParen ImpliesRole role ParentProperty role RightParen 
    { fun ont -> OPA.SubObjectPropertyOf ([$3 ont], $5 ont) }
  | LeftParen ImpliesRole role ParentsProperty LeftParen role RightParen RightParen
    { fun ont -> OPA.SubObjectPropertyOf ([$3 ont], $6 ont) }
;;

ignored_role_axiom : 
  | LeftParen ImpliesRole role RightIdentityProperty role RightParen
    { fun ont -> print_endline("Right-identity axiom (" ^ (Owl2IO.str_of_ObjectPropertyExpression ($3 ont)) ^ ", " ^ (Owl2IO.str_of_ObjectPropertyExpression ($3 ont)) ^ ") ignored."); }
;;

domain_axiom : domain_axiom_ { fun normalisationInformation ont occurrenceHash leftHandSideSet -> List.rev_map (cons_ClassExpressionAxiom ont) ($1 normalisationInformation ont occurrenceHash leftHandSideSet) }
domain_axiom_:
    LeftParen Domain role concept RightParen
    { fun normalisationInformation ont occurrenceHash leftHandSideSet ->
        normalise_domain_axiom normalisationInformation ont occurrenceHash leftHandSideSet ($3 ont) ($4 ont)
    }
  | LeftParen ImpliesRole role DomainProperty concept RightParen
    { fun normalisationInformation ont occurrenceHash leftHandSideSet ->
        normalise_domain_axiom normalisationInformation ont occurrenceHash leftHandSideSet ($3 ont) ($5 ont)
    }
;;

range_axiom : range_axiom_ { fun normalisationInformation ont occurrenceHash leftHandSideSet -> List.rev_map (cons_ClassExpressionAxiom ont) ($1 normalisationInformation ont occurrenceHash leftHandSideSet) }
range_axiom_:
    LeftParen Range role concept RightParen
    { fun normalisationInformation ont occurrenceHash leftHandSideSet ->
        normalise_range_axiom normalisationInformation ont occurrenceHash leftHandSideSet ($3 ont) ($4 ont)
    }
  | LeftParen ImpliesRole role RangeProperty concept RightParen
    { fun normalisationInformation ont occurrenceHash leftHandSideSet ->
        normalise_range_axiom normalisationInformation ont occurrenceHash leftHandSideSet ($3 ont) ($5 ont)
    }
;;

domain_range_axiom : domain_range_axiom_ { fun normalisationInformation ont occurrenceHash leftHandSideSet -> List.rev_map (cons_ClassExpressionAxiom ont) ($1 normalisationInformation ont occurrenceHash leftHandSideSet) }
domain_range_axiom_:
    LeftParen ImpliesRole role DomainProperty concept RangeProperty concept RightParen
    { fun normalisationInformation ont occurrenceHash leftHandSideSet ->
        List.rev_append (normalise_domain_axiom normalisationInformation ont occurrenceHash leftHandSideSet ($3 ont) ($5 ont))
                        (normalise_range_axiom normalisationInformation ont occurrenceHash leftHandSideSet ($3 ont) ($7 ont))
    }
;;

%%

(* kate: replace-tabs on; indent-width 2; *)