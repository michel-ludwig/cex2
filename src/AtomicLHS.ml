(***********************************************************)
(*  Copyright (C) 2008                                     *)
(*  Boris Konev (konev@liverpool.ac.uk)                    *)
(*  University of Liverpool                                *)
(*                                                         *)
(*  Copyright (C) 2010-2012                                *)
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
(**********************************************************)

open Owl2;;
open RoleMapping;;
open Settings;;
open Sigma;;
open Types;;
open Utilities;;

exception CounterExampleFound of concept;;
exception UniversalCounterExampleFound of concept;;
exception ElementFound of unit;;

type topConceptName = Top | ConceptName of string
type rangeConceptNamePair = topConceptName * topConceptName

let string_of_topConceptName t =
  match t with Top -> "Top"
            |  ConceptName cname -> cname

let string_of_rangeConceptNamePair pair =
  match pair with (c1, c2) -> "(" ^ (string_of_topConceptName c1) ^ ", " ^ (string_of_topConceptName c2) ^ ")"

let string_of_concept_option o =
  match o with None -> "None"
            |  Some c -> concept_to_string c

let checkSimulation pRoot p'Root sigma postConceptsFunction ont1 ont1_index pre_concept_hash1 post_concept_hash1 occurrenceHash1 leftHandSideSet1
                                                    ont2 ont2_index pre_concept_hash2 post_concept_hash2 occurrenceHash2 leftHandSideSet2 =

  debug_newline();
  debug_endline("checkSimulation for " ^ (string_of_rangeConceptNamePair pRoot) ^ " and " ^ (string_of_rangeConceptNamePair p'Root));

  let primitiveHash = Hashtbl.create 50 in
  let is0Hash = Hashtbl.create 50 in

  let impliedConceptNamesByPair pair post_hash =
    match pair with (Top, Top)                            -> StringSet.empty
                |  (Top, ConceptName cname)               -> postConceptsFunction post_hash cname
                |  (ConceptName cname, Top)               -> postConceptsFunction post_hash cname
                |  (ConceptName cname, ConceptName dname) -> StringSet.union (postConceptsFunction post_hash cname)
                                                                             (postConceptsFunction post_hash dname)
  in

  let impliedConceptNamesByPair1 pair =
    impliedConceptNamesByPair pair post_concept_hash1
  in

  let impliedConceptNamesByPair2 pair =
    impliedConceptNamesByPair pair post_concept_hash2
  in

  let impliedConceptNames cname post_hash =
    postConceptsFunction post_hash cname
  in

  let impliedConceptNames2 cname =
    impliedConceptNames cname post_concept_hash2
  in

  let is_primitive1 cname =
    IndexTBox.is_primitive ont1_index leftHandSideSet1 cname
  in

  let is_primitive2 cname =
    IndexTBox.is_primitive ont2_index leftHandSideSet2 cname
  in

  let post_role1 rname =
    RoleDifference.postRole (Ontology.get_RoleDifferenceInformation ont1) rname
  in

  let implied_concept_names_from_domain_restriction2 rname =
    postConceptsFunction post_concept_hash2 (RoleMapping.map_role_to_domain_binding rname)
  in

  (* unused so far *)
  (*let post_role2 rname =
    RoleDifference.postRole (Ontology.get_RoleDifferenceInformation ont2) rname
  in

  let post_role_sigma1 rname =
    RoleDifference.postRoleSigma sigma (Ontology.get_RoleDifferenceInformation ont1) rname
  in*)

  let post_role_sigma2 rname =
    RoleDifference.postRoleSigma sigma (Ontology.get_RoleDifferenceInformation ont2) rname
  in

  (* functions computing the non-conjunctive sets; *)
  (* for (implies A (and B_1 ... A ... B_n)) or (equivalent A (and B_1 ... A ... B_n)), and *)
  (* 'cname' == A, this function returns [B_1, ..., B_n] *)
  let non_conjunctive_implied cname ont occurrenceHash leftHandSideSet ont_index =
    let visited = ref StringSet.empty in
    let toBeVisited = ref [cname] in
    let rec non_conjunctive_implied_ acc =
      match !toBeVisited with
        [] -> acc
      | (cname::tl) -> begin
                       toBeVisited := tl;
                       visited := StringSet.add !visited cname;
                       match IndexTBox.normalised_get_conjunctive_rhs ont_index ont occurrenceHash leftHandSideSet cname with
                         None -> non_conjunctive_implied_ (StringSet.add acc cname)
                       | Some l -> begin
                                   List.iter (fun dname -> if not (StringSet.mem !visited dname) then
                                                             begin
                                                             toBeVisited := dname::!toBeVisited;
                                                             end)
                                             l;
                                   non_conjunctive_implied_ acc
                                   end
                    end
    in
    non_conjunctive_implied_ StringSet.empty
  in

  let non_conjunctive_implied2 cname =
    non_conjunctive_implied cname ont2 occurrenceHash2 leftHandSideSet2 ont2_index
  in

  let non_conjunctive_implied2_set cnameSet =
    StringSet.fold (fun newSet cname -> StringSet.union newSet (non_conjunctive_implied2 cname))
                   StringSet.empty
                   cnameSet
  in

  let updateCex cexRef c =
    match c with Types.Top -> () (* Types.Top is always present *)
              |  _ -> (match !cexRef with [Types.Top] -> cexRef := [c]
                                        | _ -> if not (List.mem c !cexRef) then
                                                 cexRef := c::(!cexRef))
  in

  let rec isO p p' =
    debug_endline ("isO " ^ (string_of_rangeConceptNamePair p) ^ ", " ^ (string_of_rangeConceptNamePair p'));
    (* hash optimisation *)
    try
      Hashtbl.find is0Hash (p,p')
    with Not_found ->
      let res =

        let findSimulationElementInT1 p' =
          let cexRef = ref [Types.Top] in
          let rec findSimulationElementInT1_ p =
            match isO p p' with
              None -> raise (ElementFound())
            | Some newCex -> begin
                             updateCex cexRef newCex;
                             let impliedConceptNamesByPair1 = impliedConceptNamesByPair1 p in
                             StringSet.iter (fun aname -> if not (is_primitive1 aname) then
                                                            begin
                                                            let rhsInTBox1 = IndexTBox.get_concept_rhs_in_terminology ont1_index ont1 occurrenceHash1 aname in
                                                            handle_normalised_right_hand_side_expression rhsInTBox1
                                                            (* Top *)
                                                            (fun _ -> failwith "Handling of Top is not implemented.")
                                                            (* cname = And(.ls.) *)
                                                            (fun ls -> ())
                                                            (* some r Top *)
                                                            (fun r1 -> findSimulationElementInT1_ (ConceptName (map_role_to_range_binding r1), Top))
                                                            (* some rname aname *)
                                                            (fun r1 aname -> findSimulationElementInT1_(ConceptName (map_role_to_range_binding r1), ConceptName aname))
                                                            end)
                                            impliedConceptNamesByPair1
                             end
          in
          try
            findSimulationElementInT1_ pRoot;
            match !cexRef with [c] -> (Some c) | _ -> (Some (And !cexRef))
          with ElementFound _ -> None
        in

        let isPrimO p p' =
          debug_endline ("   isPrimO " ^ (string_of_rangeConceptNamePair p) ^ " " ^ (string_of_rangeConceptNamePair p'));
          (* hash optimisation *)
          try
            Hashtbl.find primitiveHash (p,p')
          with Not_found ->
            let result =
              let impliedConceptNamesByPair2 = impliedConceptNamesByPair2 p' in
              let impliedConceptNamesByPair1 = impliedConceptNamesByPair1 p in
              try
                StringSet.iter (fun cname -> if Sigma.is_concept_name_contained sigma cname
                                                &&  not (StringSet.mem impliedConceptNamesByPair1 cname) then
                                                raise (CounterExampleFound (Name cname)))
                               impliedConceptNamesByPair2;
                None
              with CounterExampleFound cex -> (Some cex)
            in
              debug_endline ("......" ^ (string_of_concept_option result));
              Hashtbl.add primitiveHash (p, p') result;
              result
        in

        let impliedConceptNamesByPair1 = impliedConceptNamesByPair1 p in

        let checkRoleCondition cname =
          debug_endline ("...checkRoleCondition for " ^ cname);

          let findMatchingRoleSuccessorInTBox1 p2' rSet =
            debug_endline ("   findMatchingRoleSuccessorInTBox1 " ^ (string_of_rangeConceptNamePair p2') ^ " rSet= " ^ (StringSet.to_string rSet));
            let cexRef = ref [Types.Top] in
            if !debug then
              begin
              print_string("Implied concept names in TBox1: "); StringSet.print_set impliedConceptNamesByPair1; print_newline();
              end;
            let found = StringSet.exists (fun b ->  debug_endline("analysing in T1" ^ b);
                                                    if not (is_primitive1 b) then
                                                      begin
                                                      let rhsInTBox1 = IndexTBox.get_concept_rhs_in_terminology ont1_index ont1 occurrenceHash1 b in
                                                      let candidate =  handle_normalised_right_hand_side_expression rhsInTBox1
                                                                       (* Top *)
                                                                       (fun _ -> failwith "Handling of Top is not implemented.")
                                                                       (* cname = And(.ls.) *)
                                                                       (fun ls -> None)
                                                                       (* some r Top *)
                                                                       (fun r1 -> Some(r1, (ConceptName (map_role_to_range_binding r1), Top)))
                                                                       (* some rname aname *)
                                                                       (fun r1 aname -> Some (r1, (ConceptName (map_role_to_range_binding r1), ConceptName aname)))
                                                      in
                                                      match candidate with
                                                        None -> false
                                                      | Some(r1, candidateP) -> begin
                                                                                if (StringSet.subset rSet (post_role1 r1)) then
                                                                                  begin
                                                                                  match isO candidateP p2' with
                                                                                    None -> true
                                                                                  | Some cex -> begin
                                                                                                  if !debug then
                                                                                                    begin
                                                                                                    print_string "CEX found "; print_concept cex; print_newline();
                                                                                                    end;
                                                                                                  updateCex cexRef cex;
                                                                                                  false
                                                                                                end
                                                                                  end
                                                                                else
                                                                                  false
                                                                                end
                                                      end
                                                    else
                                                      false)
                                         impliedConceptNamesByPair1
            in
            if not found then
              begin
              if StringSet.cardinal rSet == 1 then
                raise (CounterExampleFound (Exists((StringSet.choose rSet), (match !cexRef with [c] -> c | _ -> (And !cexRef)))))
              else
                raise (CounterExampleFound (ExistsRoleConjunction(StringSet.to_list rSet, (match !cexRef with [c] -> c | _ -> (And !cexRef)))))
              end
          in
          (* if 'cname' is primitive in T2, then it cannot imply concepts of the form (some r C)) *)
          (* as T2 is a terminology  *)
          if not (is_primitive2 cname) then
            begin
            let rhsInTBox2 = IndexTBox.get_concept_rhs_in_terminology ont2_index ont2 occurrenceHash2 cname in
            let candidate = handle_normalised_right_hand_side_expression rhsInTBox2
                            (* Top *)
                            (fun _ -> failwith "Handling of Top is not implemented.")
                            (* cname = And(.ls.) *)
                            (fun ls -> None)
                            (* some r Top *)
                            (fun r1' -> Some (post_role_sigma2 r1', (ConceptName (map_role_to_range_binding r1'), Top)))
                            (* some rname aname *)
                            (fun r1' aname -> Some (post_role_sigma2 r1', (ConceptName (map_role_to_range_binding r1'), ConceptName aname)))
            in
            match candidate with
              None -> ()
            | Some(postRoleSigmaT2, p2') -> if is_conjunctive_query_case() then
                                              begin
                                              if StringSet.is_empty postRoleSigmaT2 then
                                                begin
                                                debug_endline("no sigma successor for " ^ (string_of_rangeConceptNamePair p2'));
                                                match findSimulationElementInT1 p2' with
                                                  None -> ()
                                                | Some cex -> (* for counter-examples that start with (some :universal C) *)
                                                              (* we don't have to go back through the role chain *)
                                                              raise (UniversalCounterExampleFound (ExistsUniversalRole cex))
                                                end
                                              else
                                                findMatchingRoleSuccessorInTBox1 p2' postRoleSigmaT2
                                              end
                                            else
                                              StringSet.iter (fun r -> findMatchingRoleSuccessorInTBox1 p2' (StringSet.singleton r))
                                                             postRoleSigmaT2
            end
        in

        let findAllExists2 cnameSet =
          let rec findAllExists2_ cnameSet acc =
            let newCNames = StringSet.fold (fun newSet cname -> let nonConjunctiveImplied = non_conjunctive_implied2 cname in
                                                                let domainRestrictions = StringSet.fold (fun newSet dname -> match IndexTBox.get_role_successor_in_terminology ont2_index ont2 occurrenceHash2 dname with
                                                                                                                                None -> newSet
                                                                                                                              | Some r -> StringSet.union newSet
                                                                                                                                                          (non_conjunctive_implied2_set (implied_concept_names_from_domain_restriction2 r)))
                                                                                                        StringSet.empty
                                                                                                        nonConjunctiveImplied
                                                                in
                                                                StringSet.union newSet (StringSet.union (StringSet.difference nonConjunctiveImplied acc)
                                                                                       (StringSet.difference domainRestrictions acc)))
                                           StringSet.empty
                                           cnameSet
            in
            if not (StringSet.is_empty newCNames) then
              findAllExists2_ newCNames (StringSet.union acc newCNames)
            else
              acc
          in
          findAllExists2_ cnameSet StringSet.empty
        in
        match isPrimO p p' with
          Some cex -> Some cex
          (* for performance reasons we don't want to go through all the concept names implied by *)
          (* the 'proper' concept name of the pair p' (i.e. its second component) as this would   *)
          (* also include concept names A defined as (equivalent A (some r B)) in the terminology *)
          (* T2 whose role successor 'r' has already been handled before, i.e. the role successor *)
          (* 'r' would be handled twice. *)
        | None -> let cnamesWithExist = match p' with
                                          (Top, Top) -> StringSet.empty
                                        | (Top, ConceptName cname) -> findAllExists2 (StringSet.singleton cname)
                                        | (ConceptName rangeConceptName, Top) -> findAllExists2 (impliedConceptNames2 rangeConceptName)
                                        | (ConceptName rangeConceptName, ConceptName cname) -> findAllExists2 (StringSet.union (impliedConceptNames2 rangeConceptName) (StringSet.singleton cname))
                  in
                  try
                    StringSet.iter checkRoleCondition cnamesWithExist;
                    None
                  with CounterExampleFound cex -> (Some cex)
      in

      Hashtbl.add is0Hash (p, p') res;
      res
  in
  try
    isO pRoot p'Root
  with
    UniversalCounterExampleFound cex -> (Some cex)


let checkCEx sigma nameMapping outputChannel ont1 ont1_index pre_concept_hash1 post_concept_hash1 occurrenceHash1 leftHandSideSet1
                                             ont2 ont2_index pre_concept_hash2 post_concept_hash2 occurrenceHash2 leftHandSideSet2 =
  let nrCounterExamples = ref 0 in
  let constructedCounterExamples = ref [] in
  let counterExampleWitnessesRef = ref StringSet.empty
  in
  StringSet.iter (fun c -> let res = checkSimulation (Top, ConceptName c) (Top, ConceptName c) sigma Ontology.post_proper_concepts
                                                     ont1 ont1_index pre_concept_hash1 post_concept_hash1 occurrenceHash1 leftHandSideSet1
                                                     ont2 ont2_index pre_concept_hash2 post_concept_hash2 occurrenceHash2 leftHandSideSet2
                            in
                            match res with
                              None -> ()
                            | Some cex -> incr nrCounterExamples;
                                          counterExampleWitnessesRef := StringSet.add !counterExampleWitnessesRef c;
                                          if !constructCounterExamples then
                                            begin
                                            output_axiom_with_mapping outputChannel (ConceptInclusion(Name c, cex)) nameMapping; output_string outputChannel "\n";
                                            Statistics.collectForLHSCounterExample c cex;
                                            constructedCounterExamples := (Name c, cex)::(!constructedCounterExamples)
                                            end
                                          else
                                            print_endline ("LHS counter-example found for " ^ c ^ "."))
                 (Sigma.get_concept_names sigma);
  print_endline("Number of differences with atomic LHS: " ^ (string_of_int !nrCounterExamples));
  (!constructedCounterExamples, !counterExampleWitnessesRef, !nrCounterExamples)


let checkRoleDomainCEx sigma nameMapping outputChannel ont1 ont1_index pre_concept_hash1 post_concept_hash1 occurrenceHash1 leftHandSideSet1
                                                       ont2 ont2_index pre_concept_hash2 post_concept_hash2 occurrenceHash2 leftHandSideSet2 =
  let nrCounterExamples = ref 0 in
  let constructedCounterExamples = ref [] in
  let counterExampleWitnessesRef = ref StringSet.empty
  in
  StringSet.iter (fun r -> let res = checkSimulation (Top, ConceptName (map_role_to_domain_binding r)) (Top, ConceptName (map_role_to_domain_binding r))
                                                     sigma Ontology.post_proper_concepts_with_domain_bindings
                                                     ont1 ont1_index pre_concept_hash1 post_concept_hash1 occurrenceHash1 leftHandSideSet1
                                                     ont2 ont2_index pre_concept_hash2 post_concept_hash2 occurrenceHash2 leftHandSideSet2
                            in
                            match res with
                              None -> ()
                            | Some cex -> incr nrCounterExamples;
                                          counterExampleWitnessesRef := StringSet.add !counterExampleWitnessesRef r;
                                          if !constructCounterExamples then
                                            begin
                                            output_axiom_with_mapping outputChannel (ConceptInclusion(Domain r, cex)) nameMapping; output_string outputChannel "\n";
                                            Statistics.collectForDomainCounterExample r cex;
                                            constructedCounterExamples := (Domain r, cex)::(!constructedCounterExamples)
                                            end
                                          else
                                            print_endline ("Role domain counter-example found for " ^ r ^ "."))
                 (Sigma.get_role_names sigma);
  print_endline("Number of differences w.r.t. the domain of roles: " ^ (string_of_int !nrCounterExamples));
  (!constructedCounterExamples, !counterExampleWitnessesRef, !nrCounterExamples)

let checkRoleRangeCEx sigma nameMapping outputChannel ont1 ont1_index pre_concept_hash1 post_concept_hash1 occurrenceHash1 leftHandSideSet1
                                                      ont2 ont2_index pre_concept_hash2 post_concept_hash2 occurrenceHash2 leftHandSideSet2 =
  let nrCounterExamples = ref 0 in
  let constructedCounterExamples = ref [] in
  let counterExampleWitnessesRef = ref StringSet.empty
  in
  StringSet.iter (fun r -> let res = checkSimulation (ConceptName (map_role_to_range_binding r), Top) (ConceptName (map_role_to_range_binding r), Top)
                                                     sigma Ontology.post_proper_concepts_with_domain_bindings
                                                     ont1 ont1_index pre_concept_hash1 post_concept_hash1 occurrenceHash1 leftHandSideSet1
                                                     ont2 ont2_index pre_concept_hash2 post_concept_hash2 occurrenceHash2 leftHandSideSet2
                            in
                            match res with
                              None -> ()
                            | Some cex -> incr nrCounterExamples;
                                          counterExampleWitnessesRef := StringSet.add !counterExampleWitnessesRef r;
                                          if !constructCounterExamples then
                                            begin
                                            output_axiom_with_mapping outputChannel (ConceptInclusion(Range r, cex)) nameMapping; output_string outputChannel "\n";
                                            Statistics.collectForRangeCounterExample r cex;
                                            constructedCounterExamples := (Range r, cex)::(!constructedCounterExamples)
                                            end
                                          else
                                            print_endline ("Role range counter-example found for " ^ r ^ "."))
                 (Sigma.get_role_names sigma);
  print_endline("Number of differences w.r.t. the range of roles: " ^ (string_of_int !nrCounterExamples));
  (!constructedCounterExamples, !counterExampleWitnessesRef, !nrCounterExamples)

(* kate: replace-tabs on; indent-width 2; *)