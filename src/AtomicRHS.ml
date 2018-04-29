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
(***********************************************************)

(* open Settings;; *)
open Debug
open Consed.T
open Owl2
open Owl2IO
open IndexTBox
open Settings
open Sigma
open Simplification
open Types
open Types.StringSet
open Utilities

exception NoCounterExamplePossible;;

let print_list lst = 
  List.iter (fun x -> print_string (x ^ " ")) lst

let print_list_endline lst = 
  List.iter (fun x -> print_string (x ^ " ")) lst; 
  print_newline ()

let print_pair (s1,i) = print_string ("(" ^ s1 ^ ", " ^ (string_of_int i) ^ ") ")

let print_excl s lst = print_string ("exclude(" ^ s ^ ") = ["); 
    UniversalSet.print_set lst; print_endline "]"
let print_excl_hash exclude = Hashtbl.iter print_excl exclude

let print_roleNameToExist r set = print_string ("roleNameToExist(" ^ r ^ ") = ["); UniversalSet.print_set set; print_endline "]"
let print_roleNameToExist h = Hashtbl.iter print_roleNameToExist h

let print1Tables  (exclude, roleNameToExist) = 
begin
  print_endline "***********************";
  print_endline "exclude:";
  print_excl_hash exclude;

  print_endline "***********************";
  print_endline "roleNameToExist: ";
  print_roleNameToExist roleNameToExist;
  print_endline "***********************";
end;;
(* End debugging *)

let print_marked c set = print_string ("Marked("^ c ^ ") = ["); UniversalSet.print_set set;  print_endline "]";;
let print_marked h = Hashtbl.iter print_marked h;;

(***********************************************************************)
(*                  Filling hashes from TBox 1                         *)
(***********************************************************************)

let fillHashes sigma ont1 ont1_index pre_concept_hash1 occurrenceHash1 hashSize = 
   let exclude         = Hashtbl.create hashSize and
                        (* is it a good guess? (too much?) *)
   roleNameToExist     = Hashtbl.create hashSize in

   (* given a hash table (key type) ---> Set(value type) *)
   (* add value to the set corresponding to key *)
   let addToSetHashTable hTable key value = 
   try
        (* get the reference*)
        let curset = Hashtbl.find hTable key in
        Hashtbl.replace hTable key (UniversalSet.add value curset);
   with 
        Not_found -> Hashtbl.add hTable key (UniversalSet.singleton value)
   in

   (* update tables for a "primitive" concept name *)
   let processPrimitive cname = 
    debug_endline ("processing pseudo-primitive " ^ cname);

    (* for every element of set, adds elem --> cname entry *)
    (* For exclude(A) = {B_1, \dotsc, B_n} it holds that \forall i: T \entails A \sqsubseteq B_i *)
    (* with A in Sigma, and B_i proper concepts *)
    let updateExclude cname set =
        StringSet.iter (fun x -> addToSetHashTable exclude x cname) set
    in

    try
      if RoleMapping.is_proper_concept_name cname then
        let sigmaPreCNSet = Ontology.pre_sigma_concepts_with_domain_range ont1 pre_concept_hash1 sigma cname in 
        updateExclude cname sigmaPreCNSet;
    with Not_found -> failwith("Exception 'Not_found' in 'processPrimitive' for " ^ cname)
   in

   (* update tables for a "compound" concept name *)
   let processCompound cname (concept : ClassExpression.t) = 
    debug_endline ("processing compound " ^ cname ^ " = " ^ (str_of_ClassExpression concept));
    (* update tables for "propositional" part*)
    processPrimitive cname;
    handle_normalised_right_hand_side_expression concept
        (* Top *)
        (fun _ -> failwith "Handling of Top is not implemented.") 
        (* cname = And(.ls.) *)
        (fun ls -> ())
        (* some r Top *)
        (fun r -> failwith "The case (some r Top) should not occur.")
        (* some rname aname *)
        (fun r aname ->
          (* update tables for some..., also for non-sigma roles 'r' *)
          addToSetHashTable roleNameToExist r cname)
   in


   (* get the definition of cname and use the functions defined above *)
   (* to process this definition *)
   let processDef cname occurrenceHash ont ont_index =
      if Hashtbl.mem occurrenceHash cname && RoleMapping.is_proper_concept_name cname then
        begin
        let c = get_concept_rhs_in_terminology ont_index ont occurrenceHash cname in
        processCompound cname c
        end
      else (* cname must be pseudo-primitive*)
        begin
        processPrimitive cname
        end
   in

  (**********************************************************************)
  (*                    MAIN part of the function                       *)
  (**********************************************************************)

  (* First, process concept names one by one *)
   StringSet.iter (fun cname -> processDef cname occurrenceHash1 ont1 ont1_index)
                  (Ontology.get_concept_names ont1);

   (* return generated tables *)
   (exclude, roleNameToExist)


(* check if there exists a counterexample to conservativity of the form *)
(* \phi \sqsubseteq A such that TBox_1 does not prove it but  *)
(*  TBox_2 does *)
let checkCEx sigma nameMapping outputChannel ont1 ont1_index pre_concept_hash1 occurrenceHash1
                                             ont2 ont2_index pre_concept_hash2 occurrenceHash2 =
  let constructedCounterExamples = ref [] in
  let (exclude, roleNameToExist)
         = fillHashes sigma ont1 ont1_index pre_concept_hash1 occurrenceHash1 (Ontology.total_ClassAssertion ont1) in
  let nonConjunctiveHash1 = Hashtbl.create 50 in
  let nonConjunctiveHash2 = Hashtbl.create 50 in
  let roleDifference1 = Ontology.get_RoleDifferenceInformation ont1 in
  let roleDifference2 = Ontology.get_RoleDifferenceInformation ont2 in
  if verbose_output () then print1Tables (exclude, roleNameToExist);

  (* main data structure *)
  let marked = Hashtbl.create (Ontology.total_ClassAssertion ont2) in 

  (* functions computing the non-conjunctive sets *)
  let rec non_conjunctive cname ont occurrenceHash nonConjunctiveHash ont_index =
    try
      Hashtbl.find nonConjunctiveHash cname
    with Not_found ->
      let v =
        if not (is_conjunctive ont_index ont occurrenceHash cname) then
          [cname]
        else
         begin
          StringSet.fold (fun l dname -> 
                                         (List.rev_append l (non_conjunctive dname ont occurrenceHash nonConjunctiveHash ont_index)))
                         [] (Hashtbl.find occurrenceHash cname)
        end
      in
        Hashtbl.add nonConjunctiveHash cname v;
        v
  in

  let non_conjunctive1 cname =
    non_conjunctive cname ont1 occurrenceHash1 nonConjunctiveHash1 ont1_index
  in

  let non_conjunctive2 cname =
    non_conjunctive cname ont2 occurrenceHash2 nonConjunctiveHash2 ont2_index
  in

  let roleNamesToDomainBindings set =
    StringSet.fold (fun newSet r -> StringSet.add newSet (RoleMapping.map_role_to_domain_binding r))
                   StringSet.empty
                   set
  in

  (* Returns the concept name itself if it can't be found in 'exclude'  *)
  let lookup_exclude cname =
    try
      Hashtbl.find exclude cname
    with Not_found -> UniversalSet.singleton cname
  in

  (* Return an empty set if the role name cannot be found in 'roleNameToExist'. *)
  let lookup_roleNameToExist rname =
    try
      Hashtbl.find roleNameToExist rname
    with Not_found -> UniversalSet.empty
  in

  let preCT1 cname =
    Ontology.pre_concepts pre_concept_hash1 cname
  in

  let preCT2 cname =
    Ontology.pre_concepts pre_concept_hash2 cname
  in

  (* unused so far *)
  (*let preCSigmaT1 cname =
    Ontology.pre_sigma_concepts ont1 pre_concept_hash1 sigma cname
  in*)

  let preCSigmaT2 cname =
    Ontology.pre_sigma_concepts ont2 pre_concept_hash2 sigma cname
  in

  (* unused so far *)
  (*let preRanSigmaT1 cname =
    Ontology.pre_sigma_range ont1 pre_concept_hash1 sigma cname
  in

  let preRanSigmaT2 cname =
    Ontology.pre_sigma_range ont2 pre_concept_hash2 sigma cname
  in*)

  let preRanT1 cname =
    Ontology.pre_range ont1 pre_concept_hash1 cname
  in

  let preRanT2 cname =
    Ontology.pre_range ont2 pre_concept_hash2 cname
  in

  (* unused so far *)
  (*
  let preDomainSigmaT1 cname =
    Ontology.pre_sigma_domain ont1 pre_concept_hash1 sigma cname
  in

  let preDomainSigmaT2 cname =
    Ontology.pre_sigma_domain ont2 pre_concept_hash2 sigma cname
  in*)

  let preDomainT1 cname =
    Ontology.pre_domain ont1 pre_concept_hash1 cname
  in

  let preDomainT2 cname =
    Ontology.pre_domain ont2 pre_concept_hash2 cname
  in

  let postRoleT1 r =
    RoleDifference.postRole roleDifference1 r
  in

  let preRoleSigmaT1 r =
    RoleDifference.preRoleSigma sigma roleDifference1 r
  in

  let preRoleT1 r =
    RoleDifference.preRole roleDifference1 r
  in

  let preRoleSigmaT2 r =
    RoleDifference.preRoleSigma sigma roleDifference2 r
  in

  let preRoleT2 r =
    RoleDifference.preRole roleDifference1 r
  in

  let mem_role_sigma_and_set x set = 
    if not (StringSet.mem (Sigma.get_role_names sigma) x) then
      false
    else
      StringSet.mem set x
  in

  let filterForPseudoPrimitivesInT1 set =
    UniversalSet.fold (fun cname set2 -> if is_pseudo_primitive ont1_index occurrenceHash1 cname then 
                                           UniversalSet.add cname set2
                                         else
                                           set2)
                      set UniversalSet.empty
  in

  let filterForExistsInT1 set =
    UniversalSet.fold (fun cname set2 -> if is_exists_definition ont1_index ont1 occurrenceHash1 cname then
                                           UniversalSet.add cname set2
                                         else
                                           set2)
                      set UniversalSet.empty
  in

  let filterForPseudoPrimitivesOrExistsInT1 set =
    UniversalSet.fold (fun cname set2 -> if (is_pseudo_primitive ont1_index occurrenceHash1 cname)
                                            || (is_exists_definition ont1_index ont1 occurrenceHash1 cname) then
                                           UniversalSet.add cname set2
                                         else
                                           set2)
                      set UniversalSet.empty
  in

  (* Given a set of cnames, cnset, compute the intersection of *)
  (* exclude applied to its elements  *)
  let computeIntersectionOfExcludeApplied cnset = 
    try 
      if StringSet.is_empty cnset then
        UniversalSet.empty
      else
        StringSet.fold_non_empty
                        (fun cname -> lookup_exclude cname)
                        (fun pSet cname -> 
                          let cnSet = (lookup_exclude cname) in
                          UniversalSet.inter cnSet pSet
                      )
                      cnset
    with Not_found -> failwith "Not found in exclude."
  in

  (* Given a set of role names, cnset, compute the intersection of *)
  (* exclude union roleNameToExist and postRole (in T1) applied to its elements. *)
  (* We keep intersecting with 'propMarkingSet' to keep the computed set as small *)
  (* as possible. *)
  let findAEquivExistsTBUsingPreDomAUnionPreRoleTInT1 propMarkingSet rnset =
    let lookup_roleNameToExist_set rset =
      StringSet.fold (fun set rname -> UniversalSet.inter propMarkingSet (UniversalSet.union set (lookup_roleNameToExist rname)))
                     (UniversalSet.empty)
                     rset
    in
    let handleRName rname =
      UniversalSet.union (lookup_roleNameToExist_set (postRoleT1 rname))
                         (UniversalSet.inter propMarkingSet (lookup_exclude (RoleMapping.map_role_to_domain_binding rname)))
    in
    if StringSet.is_empty rnset then
      UniversalSet.empty
    else
      filterForExistsInT1 (StringSet.fold_non_empty (fun rname -> handleRName rname)
                                                    (fun pSet rname -> UniversalSet.inter pSet (handleRName rname))
                                                    rnset)
  in

  (* given a list of concept name, take the union of their marking *)
  (* remember! we need to fetch the name of the concept first! *)
  (* assumes all concepts in the list are atomic *)
  let rec computeUnion concLst =
  try 
   (
    match concLst with
    | head::[] -> let hcnSet = Hashtbl.find marked head in 
        (*print_excl "computeUnion head::[]" hcnSet; *)
                  hcnSet
    | head::tail -> let hcnSet = (Hashtbl.find marked head)  
                    and tcnSet = (computeUnion tail) in
         (* print_excl "computeUnion head::tail: head" hcnSet;  *)
         (* print_excl "computeUnion head::tail: tail" tcnSet;  *)
                    UniversalSet.union hcnSet tcnSet
                                   
     | [] -> 
         (* print_endline "empty union"; *)
         UniversalSet.empty  
    )
  with 
     | Not_found -> failwith("Exception 'Not_found' in 'computeUnion'");
  in

  (* We only return non-conjunctive concept names (in T1) in the following methods *)
  let computePreMarkConcept cname =
    let sigmaPreCN = preCSigmaT2 cname in 
    if StringSet.is_empty sigmaPreCN then
      UniversalSet.universal
    else
      filterForPseudoPrimitivesOrExistsInT1 (computeIntersectionOfExcludeApplied sigmaPreCN)
  in

  let computePreMarkRan cname =
    let sigmaPreRangeCN = Ontology.pre_sigma_range_concept_names ont2 pre_concept_hash2 sigma cname in 
    if StringSet.is_empty sigmaPreRangeCN then
      UniversalSet.universal
    else
      filterForPseudoPrimitivesOrExistsInT1 (computeIntersectionOfExcludeApplied sigmaPreRangeCN)
  in

  let computePreMarkDom cname =
    let sigmaPreDomCN = Ontology.pre_sigma_domain_concept_names ont2 pre_concept_hash2 sigma cname in 
    if StringSet.is_empty sigmaPreDomCN then
      UniversalSet.universal
    else
      filterForPseudoPrimitivesOrExistsInT1 (computeIntersectionOfExcludeApplied sigmaPreDomCN)
  in

  let computePreMark cname =
    UniversalSet.inter (UniversalSet.inter (computePreMarkConcept cname) (computePreMarkRan cname))
                       (computePreMarkDom cname)
  in

  let computePrimitiveMark cname = 
    computePreMark cname
  in

   (* mark with primitive cname all (A,i) such that (A,i) does not prove cname *)
  let markPrimitiveEx cname =
  try
    let mark = (computePrimitiveMark cname) in
        if debug_output () then begin
          print_string "  computed marking: ";
          UniversalSet.print_set mark;
          print_newline();
        end;
     Hashtbl.add marked cname mark
  with 
    | Not_found -> failwith("Exception 'Not_found' in 'markPrimitiveEx' for " ^ cname)
  in

  (* mark with compound cname all (A,i) such that (A,i) does not prove cname *)
  let markCompoundEx ename concept = 
    debug_endline ("processing compound " ^ ename ^ " = " ^ (str_of_ClassExpression concept));
    handle_normalised_right_hand_side_expression concept
       (* Top *)
       (fun _ -> failwith "Handling of Top is not implemented.")

       (* And(...ls...) *)
       (fun ls ->
         let mark = computeUnion ls in
             if debug_output () then begin
               print_string "  computed marking: ";
               UniversalSet.print_set mark;
               print_newline();
             end;
         Hashtbl.add marked ename mark)

       (* some r Top *)
       (fun r -> failwith "The case (some r Top) should not occur.")

       (* some r c *)
       (fun r e' ->
         (* this is by far the hardest case.. *)
         (* compute this who do not imply cname "propositionally" *)
         let propMarkingSet = (computePrimitiveMark ename) in 
             if debug_output () then begin
               print_string "propositional marking: "; 
               UniversalSet.print_set propMarkingSet; 
               print_newline(); 
             end;
         let rPreRoleSigmaNamesT2 = preRoleSigmaT2 r in
         let rPreRoleSigmaDomainConceptNamesT2 = roleNamesToDomainBindings rPreRoleSigmaNamesT2 in

         (* Now we find all expressions of the form exists r.C such that *)
         (* (C,i) does not imply c in TBox2 *)
         let cMarking = Hashtbl.find marked e' in 

         (* now we compute the final mark *)
         let mark = 
           (* We have to consider two exceptions, though: *)
           (* if r is not from sigma or if nothing at all implies cMarking *)
           (* in both cases, nothing of the form Some(_,_) can possibly *)
           (* imply Some(r,c) *)
           if (UniversalSet.is_universal cMarking) || (StringSet.is_empty rPreRoleSigmaNamesT2)
           (* so, the marking is just the propositional marking *)
           then propMarkingSet
           else 
             begin
             (* otherwise, we have to consider the possibility of *)
             (* Som(_,_) implying cname*)
             let nonConjunctiveEPrimeInT2 = non_conjunctive2 e' in
             (* As not (UniversalSet.is_universal cMarking), it cannot hold that there exists e'' in nonConjunctiveEPrimeInT2 *)
             (* with UniversalSet.is_universal (Hashtbl.find marked e'') as marked e' = \union_e'' marked e''! *)
             let pseudoPrimitiveMark = filterForPseudoPrimitivesInT1 (computeIntersectionOfExcludeApplied rPreRoleSigmaDomainConceptNamesT2)
             in
             let existsMark = 
                (* reduce the number of candidates as much as possible *)
                let candidates = UniversalSet.inter propMarkingSet (findAEquivExistsTBUsingPreDomAUnionPreRoleTInT1 propMarkingSet rPreRoleSigmaNamesT2) in
                let checkCondition aname =
                  let (tname, bname) = get_rhs_of_definition_in_terminology ont1_index ont1 occurrenceHash1 aname in
                  let nonConjunctiveBInT1 = non_conjunctive1 bname in
                  let preDomainT1A = preDomainT1 aname in
                  StringSet.for_all (fun s ->  if not (StringSet.mem (preRoleSigmaT1 tname) s) then
                                                 true
                                               else if mem_role_sigma_and_set s preDomainT1A then
                                                 true
                                               else
                                                  List.for_all (fun b' -> if mem_role_sigma_and_set s (preRanT1 b') then
                                                                            true
                                                                          else
                                                                            List.exists (fun e'' -> (UniversalSet.mem b' (Hashtbl.find marked e''))
                                                                                                     && (not (mem_role_sigma_and_set s (preRanT2 e''))))
                                                                                        nonConjunctiveEPrimeInT2
                                                               )
                                                               nonConjunctiveBInT1
                                    )
                                    rPreRoleSigmaNamesT2
                in
                (* we still have to go through the set of candidates and filter out the wrong ones *)
                UniversalSet.fold (fun aname set -> if checkCondition aname then
                                                      UniversalSet.add aname set
                                                    else
                                                      set)
                                  candidates
                                  UniversalSet.empty
               in
               UniversalSet.inter propMarkingSet 
                                  (UniversalSet.union pseudoPrimitiveMark existsMark)
               end
         in
         if debug_output () then begin
           print_string "  marking: ";
           UniversalSet.print_set mark;
           print_newline();
         end;

         Hashtbl.add marked ename mark)
  in

  (* get the definition of cname and use the functions defined above *)
  (* to mark with cname (A,i)'s *)
  let markDef cname = (
     if Hashtbl.mem occurrenceHash2 cname then
       begin
       debug_endline ("marking compound " ^ cname);
       let c = get_concept_rhs_in_terminology ont2_index ont2 occurrenceHash2 cname in
       markCompoundEx cname c
       end
     else (* cname must be pseudo-primitive*)
      begin
       debug_endline ("marking primitive " ^ cname);
       markPrimitiveEx cname 
      end;
  )
  in


  let constructNoimplyCounterExampleUsingHash = Hashtbl.create 50 in
  let constructAllSigmaInclusionConceptInT2Hash = Hashtbl.create 50 in
  let checkConditionsForPseudoPrimitiveRHSInT2Hash = Hashtbl.create 50 in

  (* Construct conjunctions of subconcepts C_1, \dotsc, C_n of noimply_\Tmc_1,\Sigma(noimp) such that  *)
  (* \Tmc_2 \entails C_1 \sqcap \dotsc \sqcap C_n \sqsubseteq rhs *)
  (* noimp is assumed to be non-conjunctive in T1 *)
  let rec constructNoimplyCounterExampleUsing compareRan noimp rhs =
    try
      Hashtbl.find constructNoimplyCounterExampleUsingHash (compareRan, noimp, rhs)
    with Not_found ->
    let result = 
      debug_endline("constructCounterExampleUsing " ^ noimp ^ " " ^ rhs);
      let find_proper_cname_in_intersection_except set1 set2 l =
        StringSet.find_in_intersection_except RoleMapping.is_proper_concept_name set1 set2 l
      in
      let find_proper_cname_in_intersection set1 set2 =
        StringSet.find_in_intersection RoleMapping.is_proper_concept_name set1 set2
      in
      let find_role_name_in_intersection_except set1 set2 l =
        StringSet.find_in_intersection_except (fun _ -> true) set1 set2 l
      in
      let find_role_name_in_intersection set1 set2 =
        StringSet.find_in_intersection (fun _ -> true) set1 set2
      in
      let sigmaConceptNames = Sigma.get_concept_names sigma in
      let sigmaRoleNames = Sigma.get_role_names sigma in

      let conceptListToConjunctionOption conceptList =
        match conceptList with
          [] -> None
        | [c] -> Some c
        | l -> Some (And (if !simplifyCounterExamplesSemantically then
                            simplifyListOfConcepts pre_concept_hash2 l
                          else
                            l))
      in

      (******************************************************************)
      (* For handling 2nd part of condition e1 in the implication lemma *)
      (******************************************************************)
      let constructConceptFor2ndPartOfConditionE1InT2 s f preRanRHSE'T2 nonConjunctiveRHSE'T2 =
        if StringSet.mem preRanRHSE'T2 s then
          Some (Exists(s, Top)) (* 2nd part of condition e1 is fulfilled through ran(s) *)
        else
          let conceptList = 
            try
              List.fold_left (fun l e'' -> if StringSet.mem (preRanT2 e'') s then
                                            l
                                          else
                                            match f e'' with
                                              None -> raise NoCounterExamplePossible
                                            | Some c -> (if not (List.mem c l) then (c::l) else l))
                             []
                             nonConjunctiveRHSE'T2
            with NoCounterExamplePossible -> []
          in
          conceptListToConjunctionOption conceptList
      in

      (********************************************)
      (* For constructing subconcepts of AllSigma *)
      (********************************************)
      (* rhs is assumed to be non-conjunctive in T2  *)
      let rec constructAllSigmaInclusionConceptInT2 compareRan rhs =
        try
          Hashtbl.find constructAllSigmaInclusionConceptInT2Hash (compareRan, rhs)
        with Not_found ->
        let result = 
            debug_endline("constructAllSigmaInclusionConceptInT2 " ^ rhs);
            let preDomainRHST2 = preDomainT2 rhs in
            let preRanRHST2 = preRanT2 rhs in
            let preCRHST2 = preCT2 rhs in
            let checkConditionsForPseudoPrimitiveRHSInT2 compareRan =
              match find_proper_cname_in_intersection sigmaConceptNames preCRHST2 with
                Some s -> Some (Name s)
              | None ->
                  match find_role_name_in_intersection sigmaRoleNames preDomainRHST2 with
                    Some s -> Some (Domain s)
                  | None -> if compareRan then
                              match find_role_name_in_intersection sigmaRoleNames preRanRHST2 with
                                Some s -> Some (Range s)
                              | None -> None
                            else
                              None
            in
            if is_pseudo_primitive ont2_index occurrenceHash2 rhs then
              checkConditionsForPseudoPrimitiveRHSInT2 compareRan
            else (* 'rhs' is of the form rhs = some r .b in T2*)
              let (rhsR, rhsE') = get_rhs_of_definition_in_terminology ont2_index ont2 occurrenceHash2 rhs in
              let pseudoPrimitiveConditionsResult = checkConditionsForPseudoPrimitiveRHSInT2 compareRan in
              if pseudoPrimitiveConditionsResult != None then
                pseudoPrimitiveConditionsResult
              else
                let preRoleRHSRT2 = preRoleT2 rhsR in
                let preRanRHSE'T2 = preRanT2 rhsE' in
                let nonConjunctiveRHSE'T2 = non_conjunctive2 rhsE' in
                let roleCandidates = (StringSet.intersection sigmaRoleNames preRoleRHSRT2) in
                StringSet.find_object (fun s -> match constructConceptFor2ndPartOfConditionE1InT2 s (constructAllSigmaInclusionConceptInT2 (is_instance_case() || is_conjunctive_query_case()))
                                                                                                    preRanRHSE'T2 nonConjunctiveRHSE'T2
                                                with Some c -> Some (Exists(s, c))
                                                |    None -> None)
                                      roleCandidates
        in
          Hashtbl.add constructAllSigmaInclusionConceptInT2Hash (compareRan, rhs) result;
          result
      in

      (*******************)
      let preDomainNoimpT1 = preDomainT1 noimp in
      let preRanNoimpT1 = preRanT1 noimp in
      let preCNoimpT1 = preCT1 noimp in
      let preDomainRHST2 = preDomainT2 rhs in
      let preRanRHST2 = preRanT2 rhs in
      let preCRHST2 = preCT2 rhs in

      (*******************************************************************************)
      (* Checks all the conditions of implication for pseudo-primitive concept names *)
      (* found in the implication lemma.                                             *)
      (*******************************************************************************)
      let checkConditionsForPseudoPrimitiveRHSInT2 compareRan =
        try
          Hashtbl.find checkConditionsForPseudoPrimitiveRHSInT2Hash (compareRan, noimp, rhs)
        with Not_found ->
          let result = 
            debug_endline("checkConditionsForPseudoPrimitiveRHSInT2 " ^ rhs);
            begin
            if is_pseudo_primitive ont1_index occurrenceHash1 noimp then
              begin
              debug_endline("\t" ^ noimp ^ " is pseudo-primitive in T1");
              match find_proper_cname_in_intersection_except sigmaConceptNames preCRHST2 [preCNoimpT1] with
                Some s -> Some (Name s)
              | None ->
                  match find_role_name_in_intersection_except sigmaRoleNames preDomainRHST2 [preDomainNoimpT1] with
                    Some s -> Some (Exists (s, Top))
                  | None -> if compareRan then 
                              match find_role_name_in_intersection_except sigmaRoleNames preRanRHST2 [preRanNoimpT1] with
                                Some s -> Some (Range s)
                              | None -> None
                             else
                              None
              end
            else if is_exists_definition ont1_index ont1 occurrenceHash1 noimp then
              begin
              debug_endline("\t" ^ noimp ^ " is exists in T1");
              let (noimpR, noimpB) = get_rhs_of_definition_in_terminology ont1_index ont1 occurrenceHash1 noimp in
              let nonConjunctiveNoimpBT1 = non_conjunctive1 noimpB in
              let preRoleSigmaNoimpRT1 = preRoleSigmaT1 noimpR in
              match find_proper_cname_in_intersection_except sigmaConceptNames preCRHST2 [preCNoimpT1] with
                Some s -> Some (Name s)
              | None ->
                        match find_role_name_in_intersection_except sigmaRoleNames preDomainRHST2 [preDomainNoimpT1;preRoleSigmaNoimpRT1] with
                          Some s -> Some (Exists (s, Top))
                        | None -> let roleCandidates2 = StringSet.difference (StringSet.intersection preRoleSigmaNoimpRT1 preDomainRHST2) preDomainNoimpT1
                                  in
                                  match StringSet.find_object (fun s -> list_find_object (fun b' -> if not (StringSet.mem (preRanT1 b') s) then
                                                                                                      Some (Exists (s, Top))
                                                                                                    else
                                                                                                      None)
                                                                                          nonConjunctiveNoimpBT1)
                                                               roleCandidates2
                                  with
                                    Some _ as result -> result
                                  | None -> if compareRan then 
                                              match find_role_name_in_intersection_except sigmaRoleNames preRanRHST2 [preRanNoimpT1] with
                                                Some s -> Some (Range s)
                                              | None -> None
                                             else
                                                None
              end
            else 
              failwith "Invalid argument."
            end
        in
          Hashtbl.add checkConditionsForPseudoPrimitiveRHSInT2Hash (compareRan, noimp, rhs) result;
          result
      in

      (*******************************)
      (* Start of main function body *)
      (*******************************)
      if is_pseudo_primitive ont2_index occurrenceHash2 rhs then
        begin
        debug_endline("\t" ^ rhs ^ " is pseudo-primitive in T2");
        checkConditionsForPseudoPrimitiveRHSInT2 compareRan
        end
      else if is_exists_definition ont2_index ont2 occurrenceHash2 rhs then (* 'rhs' is of the form rhs = some r .b in T2*)
        begin
        debug_endline("\t" ^ rhs ^ " is exists in T2");
        let (rhsR, rhsE') = get_rhs_of_definition_in_terminology ont2_index ont2 occurrenceHash2 rhs in
        let pseudoPrimitiveConditionsResult = checkConditionsForPseudoPrimitiveRHSInT2 compareRan in
        if pseudoPrimitiveConditionsResult != None then
          pseudoPrimitiveConditionsResult
        else
          let preRoleSigmaRHSRT2 = preRoleSigmaT2 rhsR in
          let preRanRHSE'T2 = preRanT2 rhsE' in
          let nonConjunctiveRHSE'T2 = non_conjunctive2 rhsE' in

          if is_pseudo_primitive ont1_index occurrenceHash1 noimp then
            begin
              let roleCandidates = StringSet.difference preRoleSigmaRHSRT2 preDomainNoimpT1 in
              StringSet.find_object (fun s -> match constructConceptFor2ndPartOfConditionE1InT2 s (constructAllSigmaInclusionConceptInT2 (is_instance_case() || is_conjunctive_query_case()))
                                                                                                  preRanRHSE'T2 nonConjunctiveRHSE'T2
                                              with Some c -> Some(Exists(s, c))
                                              |    None -> None)
                                    roleCandidates
            end
          else if is_exists_definition ont1_index ont1 occurrenceHash1 noimp then
            begin
              let (noimpR, noimpB) = get_rhs_of_definition_in_terminology ont1_index ont1 occurrenceHash1 noimp in
              let preRoleNoimpRT1 = preRoleT1 noimpR in
              let nonConjunctiveNoimpBT1 = non_conjunctive1 noimpB in
              let roleCandidates1 = StringSet.difference preRoleSigmaRHSRT2 (StringSet.union preDomainNoimpT1 preRoleNoimpRT1) in
              let possibility1 = StringSet.find_object (fun s -> match constructConceptFor2ndPartOfConditionE1InT2 s (constructAllSigmaInclusionConceptInT2 (is_instance_case() || is_conjunctive_query_case()))
                                                                                                                     preRanRHSE'T2 nonConjunctiveRHSE'T2
                                                                with Some c -> Some(Exists(s, c))
                                                                |    None -> None)
                                                        roleCandidates1
              in
              if possibility1 != None then
                possibility1
              else
              let roleCandidates2 = StringSet.difference (StringSet.intersection preRoleSigmaRHSRT2 preRoleNoimpRT1) preDomainNoimpT1
              in
              StringSet.find_object (fun s -> list_find_object (fun b' -> if StringSet.mem (preRanT1 b') s then
                                                                            None
                                                                          else
                                                                            match constructConceptFor2ndPartOfConditionE1InT2 s (constructNoimplyCounterExampleUsing (is_instance_case() || is_conjunctive_query_case()) b')
                                                                                                                                preRanRHSE'T2 nonConjunctiveRHSE'T2
                                                                            with Some c -> Some(Exists(s, c))
                                                                            |    None   -> None)
                                                               nonConjunctiveNoimpBT1)


                                    roleCandidates2
            end
          else 
            failwith "Invalid argument."
        end
      else (* 'a' is of the form a = (and c_1 ... c_n) in T2 *)
        begin
        (* we construct the conjunction of counter-examples found for every element *)
        (* in c_1 ... c_n *)
        let rec construct_conjunction ll =
            assert(not (list_is_empty ll));
            let noCounterExampleFoundList = ref [] in
            (* in the concept case we don't allow the counter-examples for the different c_i s to contain 'ran' as this is handled later, *)
            (* it is also guaranteed that none of the counter-examples found contains a conjunction as top-level operator as all the c_i s*)
            (* are non-conjunctive *)
            let compareRanNow = ((is_instance_case() || is_conjunctive_query_case()) && compareRan) in
            let counterExamplesList = List.fold_left (fun l c -> match constructNoimplyCounterExampleUsing compareRanNow noimp c with
                                                                   None -> noCounterExampleFoundList := c::(!noCounterExampleFoundList); l
                                                                 | Some c -> (if not (List.mem c l) then (c::l) else l))
                                                     []
                                                     ll
            in
            if is_instance_case() || is_conjunctive_query_case() then
              begin
              if list_is_empty !noCounterExampleFoundList then
                counterExamplesList
              else
                []
              end
            else
              begin
              if list_is_empty !noCounterExampleFoundList then
                counterExamplesList
              else
                (* we have to check if the range of a role could subsume all the concept names found in 'noCounterExampleFoundList' *)
                begin
                  match find_role_name_in_intersection_except sigmaRoleNames
                                                              (StringSet.compute_list_intersection preRanT2 !noCounterExampleFoundList)
                                                              [preRanNoimpT1] with
                    Some r -> (Range r)::counterExamplesList
                  | None -> []
                end
              end
        in

        let conceptList = construct_conjunction (non_conjunctive2 rhs) in
        conceptListToConjunctionOption conceptList

        end
    in
      Hashtbl.add constructNoimplyCounterExampleUsingHash (compareRan, noimp, rhs) result;
      result
  and
    (*****************************************************************************)
    (* Tries to construct a concept using all the elements of noimply_\Tmc(rhs). *)
    (*****************************************************************************)
    constructNoimplyCounterExample compareRan rhs =
      debug_endline ("constructNoimplyCounterExample " ^ (string_of_bool compareRan) ^ " " ^ rhs);
      list_find_object (fun cname -> constructNoimplyCounterExampleUsing compareRan cname rhs)
                       (non_conjunctive1 rhs);
  in

   (* __Assuming__ marking for cname is computed, check if cname gives   *)
   (* raise to a counterexample of the form \phi\sqsubseteq cname, where *)
   (* \phi is non-conjunctive *) 
  let isCEx cname = 
    (* for sigma-names only *)
    if is_concept_name_contained sigma cname then
    begin
      try
        let nonConjunctiveCEX = ref None in
        let cMarking = Hashtbl.find marked cname in 
        ignore (List.exists (fun dname -> if not (UniversalSet.mem dname cMarking) then
                                            begin
                                            if verbose_output () then
                                              begin
                                              print_endline ( "C(" ^ cname ^ ")_" ^ dname ^
                                                              " implies " ^ cname);
                                              end;
                                            nonConjunctiveCEX := Some dname;
                                            true
                                            end
                                          else
                                            false)
               (non_conjunctive1 cname));
        !nonConjunctiveCEX
      with Not_found -> failwith("Exception 'Not_found' in 'isCEx' for " ^ cname);
    end
    (* non sigma-names cannot be counterexamples *)
    else None
  in
  let i = ref 0 in
  let conceptCounter = ref 1 in
  let nrCounterExamples = ref 0 in
  let counterExampleWitnesses = ref StringSet.empty in
  let definitorialDepthHash2 = Ontology.compute_definitorial_depth_hash ont2 occurrenceHash2  in
  begin
    try
      while true do
        (* Note that it is enough to only go through the concept names present in T2. If there is   *)
        (* a concept name A in \sigma but not in T2, then T2 only implies A \sqsubseteq A for       *)
        (* concept inclusions with A as RHS. Thus, T2 doesn't imply anything more than T1 regarding *)
        (* such concept inclusions.                                                                 *)
        List.iter (fun x -> if RoleMapping.is_proper_concept_name x then
                              begin
                                debug_endline("marking " ^ x ^ " (" ^ (string_of_int !conceptCounter) ^ "/" ^ (string_of_int (Ontology.total_ClassIRI ont2)) ^ ")");
                                markDef x;
                                let nonConjunctiveCEXOption = isCEx x
                                in
                                match nonConjunctiveCEXOption with
                                  Some b ->
                                    begin
                                      (* In the concept case we aren't done yet as 'x' might only be a counter-example in the instance case. *)
                                      (* So we have to check if we can find a counter-example for the concept case. *)
                                      if is_concept_case() then
                                        begin
                                         (* We play safe here and search again through all of noimply(x) for the counter-example. *)
                                          match constructNoimplyCounterExample true x with
                                            None -> ()
                                          | Some c -> incr nrCounterExamples;
                                                      counterExampleWitnesses := StringSet.add !counterExampleWitnesses x;
                                                      if !constructCounterExamples then
                                                        begin
                                                          output_axiom_with_mapping outputChannel (ConceptInclusion(c, Name x)) nameMapping; output_string outputChannel "\n";
                                                          Statistics.collectForRHSCounterExample c x;
                                                          constructedCounterExamples :=  (c, Name x)::!constructedCounterExamples
                                                        end
                                                      else
                                                        begin
                                                          print_endline ("RHS counter-example found for " ^ x ^ ".");
                                                        end
                                        end
                                      else
                                        begin
                                          incr nrCounterExamples;
                                          counterExampleWitnesses := StringSet.add !counterExampleWitnesses x;
                                          if !constructCounterExamples then
                                            begin
                                            match constructNoimplyCounterExampleUsing true b x with
                                              None -> failwith "No counter-example found."
                                            | Some c -> output_axiom_with_mapping outputChannel (ConceptInclusion(c, Name x)) nameMapping; output_string outputChannel "\n";
                                                        Statistics.collectForRHSCounterExample c x;
                                                        constructedCounterExamples :=  (c, Name x)::!constructedCounterExamples
                                            end
                                          else
                                            begin
                                              print_endline ("RHS counter-example found for " ^ x ^ ".");
                                            end
                                        end
                                    end
                                 | None -> ()
                              end;
                              incr conceptCounter;)
                  (to_list (Hashtbl.find definitorialDepthHash2 !i));
        incr i;
      done;
    with Not_found -> ()
  end;
  if verbose_output () then
  begin
    print_endline "Marked:";
    print_marked marked
  end;
  print_endline("Number of differences with atomic RHS: " ^ (string_of_int !nrCounterExamples));
  (!constructedCounterExamples, !counterExampleWitnesses, !nrCounterExamples)
  (* Checks if there exist a counterexample with Atomic(cname) in the RHS *)


(* kate: replace-tabs on; indent-width 2; *)
