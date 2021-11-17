(*Author: Joanne Dumont*)
(*Based on Arthur Gontier's work*)

(*I - Prerequisites*)

(*I.1 - Definitions*)
open List 
type var_name = X | B of int | T | I | V | N | O
(*Index modifications*) 
type ind_name = I of int | T of int | P of int | R of int
type ind_set = D of int | D2 of ind_name list
type ind_const = C of int 
type ind_symbols = PLUS|MINUS|IN|NEQ|LEQ|GEQ|EQ 
type ind_modifs = | Set of ind_name*ind_symbols*ind_set (*I∈D*) 
                  | Rel of ind_name*ind_symbols*ind_name (*I≠I2*) 
                  | Addint of ind_name*ind_name*ind_symbols*int (*I2=I+1*) 
                  | Addcst of ind_name*ind_name*ind_symbols*ind_const*ind_name (*I3=I2-C I*) 
                  | EXFORALL of ind_name 
                  | EXEXISTS of ind_name 
type consistancy = AC | BC (*AC: equal/non-equal; BC: greater (or equal)/smaller*)
(*Event types*) 
type index = Ind of ind_name*ind_modifs list
type event = | Global_event of bool*var_name*index list*consistancy
             | Decomp_event of bool*var_name*index list
type decomp_event = | Global_devent  of bool*var_name*(index list->index list)*(index list->index list)*consistancy
                    | Decomp_devent  of bool*var_name*(index list->index list)*(index list->index list)
                    | Reified_devent of bool*var_name*(index list->index list)*(index list->index list)
(*Explanation tree*) 
type leaf = Var of event | T | F | IM | R | FE 
type tree = | Lit of leaf 
            | EXOR of event*tree list 
            | EXAND of event*tree list 
(*Constraint with id, explanation rule and devent list*) 
type decomp_ctr = Decomp of int*(event->decomp_event->decomp_ctr->decomp_ctr list->event list->tree)*decomp_event list

(*I.2 - Useful functions to use events, constraints and lists*)
let sign e = match e with Global_event (b,_,_,_) | Decomp_event (b,_,_) -> b
let dsign e = match e with Global_devent (b,_,_,_,_) | Decomp_devent (b,_,_,_) | Reified_devent (b,_,_,_) -> b
let name e = match e with Global_event (_,n,_,_) | Decomp_event (_,n,_) -> n
let dname e = match e with Global_devent (_,n,_,_,_) | Decomp_devent (_,n,_,_) | Reified_devent (_,n,_,_) -> n
let index_list e = match e with Global_event (_,_,l,_) | Decomp_event (_,_,l)->l
let cons e = match e with
    |Global_event (_,_,_,c) -> c
    |_ -> failwith "inner decomp events have no consistancy"
let dcons e = match e with
    |Global_devent (_,_,_,_,c) -> c 
    |_ -> failwith "inner decomp events have no consistancy"
let index_update e = match e with Global_devent (_,_,f,_,_) | Decomp_devent (_,_,f,_) | Reified_devent (_,_,f,_) -> f
let index_propagate e = match e with Global_devent (_,_,_,f,_) | Decomp_devent (_,_,_,f) | Reified_devent (_,_,_,f) -> f
let ind_name i = match i with Ind (i,_) -> i
let ind_modifs_list i = match i with Ind (_,l) -> l
let decomp_ctr_rule c = match c with Decomp (_,r,_) -> r
let decomp_ctr_id c = match c with Decomp (id,_,_) -> id
let decomp_event_list c = match c with Decomp (_,_,l) -> l

let prim i = match i with I a -> I (a+1) | T a -> T (a+1) | P a -> P (a+1) | R a -> R (a+1)

let id  x = x(*identity function*) 
let n   e = match e with(*negation of event x*) 
  | Global_event (b,n,l,c)-> Global_event (not b,n,l,c)
  | Decomp_event (b,n,l) -> Decomp_event (not b,n,l)

let rec is_event e dcl = (*checks if event e appears in decomp constraint list dcl*) 
  match dcl with
    | [] -> false
    | de::tl -> if dname de = name e then true
                else is_event e tl 
let rec same_name e el = (*removes event which don't have the same name as event e from event list el*) 
  match el with
    | [] -> []
    | de::tl -> if dname de = name e then de::same_name e tl
                else same_name e tl 
let rec ctr_with_event e cl = (*removes constraints in which event e doesn't appear from constraint list cl*) 
  match cl with
    | [] -> []
    | c::tl -> if is_event e (decomp_event_list c) then c::ctr_with_event e tl
               else ctr_with_event e tl 
let rec removes_event e el = (*removes event e from event list el*) 
  match el with
    | [] -> []
    | c::tl -> if (dsign e = dsign c)&&(dname e = dname c) then removes_event e tl
               else c::removes_event e tl

let rec reified_devent del = (*catch a reified event in a list*)
  match del with
    | [] -> Reified_devent (true, T,id,id)
    | de::tl -> match de with
        | Reified_devent (_,_,_,_) -> de
        | _ -> reified_devent tl

let rec removes_index i il = (*removes index i from index list il*)
  match il with
    | [] -> []
    | j::tl -> if  ind_name i = ind_name j then removes_index i tl
               else j::removes_index i tl 

let rec removes_constraint c cl = (*removes constraint c from constraint list cl*)
  match cl with
    | [] -> []
    | cc::tl -> if  decomp_ctr_id c = decomp_ctr_id cc then removes_constraint c tl
               else cc::removes_constraint c tl 

let rec is_constraint c cl = (*checks if constraint c appears in constraint list cl *) 
  match cl with
    | [] -> false
    | cc::tl -> if cc=c then true else is_constraint c tl 

(*II - Index propagation*)

(*II.1 - Index modification functions*)
(*TODO: change names*)
(*Constructors for index modification functions*) 
let iprim i = Ind (prim (ind_name i), ind_modifs_list i) 
let iprimneqi i = Ind (prim (ind_name i), Rel (prim (ind_name i),NEQ,ind_name i)::ind_modifs_list i) 
let addint i sym int = Ind (prim (ind_name i), [Addint (prim (ind_name i), ind_name i, sym, int)]@ind_modifs_list i) 
let addcst i sym cst i2 = Ind (prim (ind_name i), [Addcst (prim (ind_name i), ind_name i, sym, cst, ind_name i2)]@ind_modifs_list i) 
let rec uniqueset i set iml = match iml with
  | [] -> [Set (i,IN,set)]
  | Set (j,_,d)::tl -> if i!=j||set!=d then uniqueset i set tl else []
  | _ -> []
let sum i d = Ind (prim (ind_name i), [EXFORALL (prim (ind_name i)); Set (prim (ind_name i),IN,d); Rel (prim (ind_name i), NEQ, ind_name i)]@ind_modifs_list i) 
(*Index finders applyers and removals*)
(*TODO: fix repetitions*)
(*Find index in list*)
let rec iii il = match il with
  | [] -> failwith "Index i has left the building"
  | i::tl -> match i with Ind (I _,_) -> i
  | _ -> iii tl
let rec ttt il = match il with
  | [] -> failwith "Index t has left the building"
  | i::tl -> match i with Ind (T _,_) -> i
  | _ -> ttt tl
let rec ppp il = match il with
  | [] -> failwith "Index p has left the building"
  | i::tl -> match i with Ind (P _,_) -> i
  | _ -> ppp tl
(*Applies function to one index in a list*)
let rec iap f il = match il with [] -> [] | i::tl -> match i with | Ind (I _,_) -> f i::iap f tl | _ -> i::iap f tl
let rec tap f il = match il with [] -> [] | i::tl -> match i with Ind (T _,_) -> f i::tap f tl | _ -> i::tap f tl
let rec pap f il = match il with [] -> [] | i::tl -> match i with Ind (P _,_) -> f i::pap f tl | _ -> i::pap f tl
(*Removes index from list*)
let rec i_out il = match il with [] -> [] | i::tl -> match i with Ind (I _,_) -> tl | _ -> i::i_out tl
let rec t_out il = match il with [] -> [] | i::tl -> match i with Ind (T _,_) -> tl | _ -> i::t_out tl
let rec p_out il = match il with [] -> [] | i::tl -> match i with Ind (P _,_) -> tl | _ -> i::p_out tl
(*Creates an index - used when an event is appplied to several variables*)
let oni il = Ind (I 1,Set (I 1,IN,D 1)::[])::[]
let ont il = Ind (T 1,Set (T 1,IN,D 2)::[])::[]
let onp il = Ind (P 1,Set (P 1,IN,D 3)::[])::[]
let onr il = Ind (R 1,Set (R 1,IN,D 4)::[])::[]
(*Creates a function that creates an index*)
let oniin set = fun il -> Ind (I 1,Set (I 1,IN,set)::[])::[]
let ontin set = fun il -> Ind (T 1,Set (T 1,IN,set)::[])::[]
let onpin set = fun il -> Ind (P 1,Set (P 1,IN,set)::[])::[]
let onrin set = fun il -> Ind (R 1,Set (R 1,IN,set)::[])::[]

(*Index modification functions*)
(*TODO: fix repetitions*)
let sumiin set = iap (function x -> sum x set) 
let sumtin set = tap (function x -> sum x set) 
let sumpin set = pap (function x -> sum x set) 
let sumi = iap (function x -> sum x (D 1)) 
let sumt = tap (function x -> sum x (D 2)) 
let sump = pap (function x -> sum x (D 3)) 
let foralliin set = function il -> Ind (I 1,[EXFORALL (I 1);Set (I 1,IN,set)])::il 
let foralltin set = function il -> Ind (T 1,[EXFORALL (T 1);Set (T 1,IN,set)])::il 
let forallpin set = function il -> Ind (P 1,[EXFORALL (P 1);Set (P 1,IN,set)])::il 
let foralli = function il -> Ind (I 1,[EXFORALL (I 1);Set (I 1,IN,D 1)])::il 
let forallt = function il -> Ind (T 1,[EXFORALL (T 1);Set (T 1,IN,D 2)])::il 
let forallp = function il -> Ind (P 1,[EXFORALL (P 1);Set (P 1,IN,D 3)])::il 
let iplus int = iap (function x -> addint x PLUS int)
let iminus int = iap (function x -> addint x MINUS int)
let tplus int = tap (function x -> addint x PLUS int)
let tminus int = tap (function x -> addint x MINUS int)
let tplusci c = function il -> tap (function x -> addcst x PLUS c (iii il)) il
let tminusci c = function il -> tap (function x -> addcst x MINUS c (iii il)) il
let tprimin d = tap (function x -> Ind (prim (ind_name x), [Set (prim (ind_name x),IN,d); Rel (prim (ind_name x), NEQ, ind_name x)]@ind_modifs_list x))
(*Creates a function that applies multiple functions*)
let rec agg_functions l = match l with
  | []->failwith "empty im list"
  | f::[] -> (fun il -> f il)
  | f::tl -> (fun il -> f ((agg_functions tl) il))

(*II.2 - To use the index modification functions*)

(*apply index modification functions on an event*) 
let i_prop e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (b,n,(index_propagate de) ((index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (b,n,(index_propagate de) ((index_update dep) (index_list e)))
(*apply index modification functions with negation*) 
let n_i_prop e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (not b,n,(index_propagate de) ((index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (not b,n,(index_propagate de) ((index_update dep) (index_list e)))
(*TODO: change names*)
(*apply index modification functions with particularities for sum, bigvee and bigwedge*)
let addexists de = (fun ill -> (match ((index_propagate de) []) with Ind (i,il)::[]->Ind (i,EXEXISTS i::il)|_->failwith "missing index set exist")::ill)
let addforall de = (fun ill -> (match ((index_propagate de) []) with Ind (i,il)::[]->Ind (i,EXFORALL i::il)|_->failwith "missing index set forall")::ill)
let addprim   de = (fun ill -> (match ((index_propagate de) []) with Ind (i,il)::[]->Ind (prim i,EXFORALL (prim i)::Rel (prim i,NEQ,i)::Set (prim i,IN,match il with Set (_,_,d)::[]->d|_->failwith "missing index set" )::il)|_->failwith "missing index set prim")::ill)
let apexists e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (b,n,(addexists de) ((index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (b,n,(addexists de) ((index_update dep) (index_list e)))
let apforall e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (b,n,(addforall de) ((index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (b,n,(addforall de) ((index_update dep) (index_list e)))
let apprim e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (b,n,(addprim de) ((index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (b,n,(addprim de) ((index_update dep) (index_list e)))
let napexists e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (not b,n,(addexists de) ((index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (not b,n,(addexists de) ((index_update dep) (index_list e)))
let napforall e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (not b,n,(addforall de) ((index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (not b,n,(addforall de) ((index_update dep) (index_list e)))
let napprim e de dep = match de with
  | Global_devent  (b,n,_,_,c) -> Global_event (not b,n,(addprim de) ((index_update dep) (index_list e)),c)
  | Decomp_devent  (b,n,_,_)
  | Reified_devent (b,n,_,_)   -> Decomp_event (not b,n,(addprim de) ((index_update dep) (index_list e)))

(*III - Explanation rules*)
(*See "rules.png" for documentation*)

(*III.1 - Useful functions*)
 
(*Find event e in the decomposition dec and call the explanations rules*) 
let rec find e prec dec ch =  
  if is_constraint e ch || is_constraint (n e) ch then Lit R else 
  let cl = ctr_with_event e dec in 
  let cl = removes_constraint prec cl in 
  if cl = [] then Lit IM else 
  EXOR (e,flatten (map (fun c-> map (fun de -> (decomp_ctr_rule c) e de c dec (ch@[e])) (same_name e (decomp_event_list c))) cl)) 
 
and exp_re  re e de c dec ch =  (*explanation by refied event*) 
  if dname re  = T then Lit T else EXAND (e,[find (i_prop e re de) c dec ch]) 
and exp_nre re e de c dec ch =  (*explanation by negative refied event*) 
  if dname re  = T then Lit F else EXAND (e,[find (n_i_prop e re de) c dec ch])
and exp_el  del e de c dec ch = (*explanation by event list*) 
  map (fun dee-> find (i_prop e dee de) c dec ch) del 
and exp_nel del e de c dec ch = (*explanation by negative event list*) 
  map (fun dee-> find (n_i_prop e dee de) c dec ch) del 

let rec removesame l = (*keeps one occurence of each element*)
  match l with []->[]|v::tl->if is_constraint v tl then removesame tl else [v]@(removesame tl) 
let rec imp l = (*detect impossible literals*) 
  match l with []->false | c::tl -> match c with |F|IM|FE|R -> true | _ -> imp tl 
let rec removeimp ll = (*removes explanation with impossible literals*) 
  match ll with []->[]|l::tl->if imp l || is_constraint l tl then removeimp tl else [removesame l]@(removeimp tl) 
 
let concat l = (*concatenation of EXAND and EXOR into EXOR of EXAND*) 
  match l with []-> [] | l1::[]-> l1 | l1::tl -> fold_left (fun l1 l2 -> flatten (map (fun x -> map (fun y -> x@y) l1) l2)) l1 tl 

let rec analysis a = (*analysis of the explanation tree, returns explanation list*) 
  match a with 
    | Lit x -> [[x]] 
    | EXOR (_,l) -> flatten (map analysis l) 
    | EXAND (_,l) -> concat (map analysis l)

(*III.2 - Rules*)

let rule0 e de c dec ch = (*reified - input global event*)  
  let re = reified_devent (decomp_event_list c) in 
  if dsign de = sign e then exp_re re e de c dec ch
  else exp_nre re e de c dec ch

let rule1 e de c dec ch = (*reified*)
  let re = reified_devent (decomp_event_list c) in 
  let x = hd (removes_event re (decomp_event_list c)) in 
  if dname re = name e 
  then if dsign de = sign e
    then EXAND (e,[Lit (Var (i_prop e x re))]) 
    else EXAND (e,[Lit (Var (n_i_prop e x re))]) 
  else Lit FE

and rule3 e de c dec ch = (*conjonction*) 
  let re = reified_devent (decomp_event_list c) in
  let del = removes_event re (decomp_event_list c) in
  if dname de = dname re
  then if dsign de = sign e
    then match del with 
      | dee::[] -> EXAND (e,[find (apforall e dee de) c dec ch]) 
      | _       -> EXAND (e, exp_el del e de c dec ch) 
    else match del with 
      | dee::[] -> EXOR  (e,[find (napexists e dee de) c dec ch]) 
      | _       -> EXOR  (e, exp_nel del e de c dec ch) 
  else 
    if sign e = dsign de
    then exp_re re e de c dec ch 
    else match del with
      | dee::[] -> EXOR  (e,exp_nre re e de c dec ch::[find (apprim e dee de) c dec ch]) 
      | _       -> EXAND (e,exp_nre re e de c dec ch::exp_el (removes_event de del) e de c dec ch) 

and rule4 e de c dec ch = (*disjunction*) 
  let re = reified_devent (decomp_event_list c) in
  let del = removes_event re (decomp_event_list c) in
  if dname de = dname re
  then if dsign de = sign e 
    then match del with 
      | dee::[] -> EXOR  (e,[find (apexists e dee de) c dec ch]) 
      | _       -> EXOR  (e,exp_el del e de c dec ch) 
    else match del with 
      | dee::[] -> EXAND (e,[find (napforall e dee de) c dec ch]) 
      | _       -> EXAND (e,exp_nel del e de c dec ch) 
  else  
    if sign e = dsign de
    then match del with
      | dee::[] -> EXOR  (e,exp_re re e de c dec ch::[find (napprim e dee de) c dec ch]) 
      | _       -> EXAND (e,exp_re re e de c dec ch::exp_nel (removes_event de del) e de c dec ch) 
    else exp_nre re e de c dec ch 

and rule5 e de c dec ch = (*Bool sum<=c*) 
  let re = reified_devent (decomp_event_list c) in
  match removes_event re (decomp_event_list c) with
    | dee::[]->
      if dname de = dname re
      then if dsign de = sign e 
        then EXAND (e,[find (napforall e dee de) c dec ch])
        else EXAND (e,[find ( apforall e dee de) c dec ch]) 
      else  
        if sign e = dsign de
        then EXAND (e,exp_nre re e de c dec ch::[find (napprim e dee de) c dec ch])
        else EXAND (e,exp_re re e de c dec ch::[find ( apprim e dee de) c dec ch])
    | _ -> failwith "multiple sums to be implemented"

and rule6 e de c dec ch = (*Bool sum=>c*) 
  let re = reified_devent (decomp_event_list c) in
  match removes_event re (decomp_event_list c) with
    | dee::[]->
      if dname de = dname re
      then if dsign de = sign e 
        then EXAND (e,[find ( apforall e dee de) c dec ch]) 
        else EXAND (e,[find (napforall e dee de) c dec ch])
      else  
        if sign e = dsign de
        then EXAND (e,exp_re re e de c dec ch::[find (napprim e dee de) c dec ch])
        else EXAND (e,exp_nre re e de c dec ch::[find ( apprim e dee de) c dec ch])
    | _ -> failwith "multiple sums to be implemented"

and rule7 e de c dec ch = (*Bool sum=c*) 
  let re = reified_devent (decomp_event_list c) in
  match removes_event re (decomp_event_list c) with
    | dee::[]->
      if dname de = dname re
      then if dsign de = sign e 
        then EXAND (e,find (apforall e dee de) c dec ch::[find (napforall e dee de) c dec ch])(*incoherent?*) 
        else EXOR  (e,find (apforall e dee de) c dec ch::[find (napforall e dee de) c dec ch])(*incoherent?*) 
      else  
        if sign e = dsign de
        then EXAND (e,exp_re re e de c dec ch::[find (napforall e dee de) c dec ch]) 
        else EXAND (e,exp_re re e de c dec ch::[find ( apforall e dee de) c dec ch]) 
    | _ -> failwith "multiple sums to be implemented"

(*IV - Output*)

open Printf

(*IV.1 - Print explanation as a string*) 
let rec printprim n = match n with 1 -> "" | _ ->"'"^printprim (n-1)
let printind_name_int a = match a with 1 -> "" | 2 -> "'" | 3 -> "''" | _ -> "_{"^string_of_int a^"}"
let printind_name i = match i with I a -> "i"^printind_name_int a | T a -> "t"^printind_name_int a | P a -> "p"^printind_name_int a | R a -> "r"^printind_name_int a
let printind_set_int a = match a with 1 -> "\\llbracket1,n\\rrbracket" | 2 -> "\\llbracket1,m\\rrbracket" | 3 -> "\\llbracket1,n\\rrbracket" | _ -> "D_{"^string_of_int a ^"}"
let printind_set s = match s with D a -> printind_set_int a | D2 _ -> "setfils" 
let printind_const_int a = match a with 1 -> "" | _ -> "_{"^string_of_int a^"}"
let printind_const c = match c with C a -> "d"^printind_const_int a
let printind_symbols s = match s with PLUS-> "+"|MINUS->"-"|IN->"∈"|NEQ->"≠"|LEQ->"<="|GEQ->">="|EQ->"=" 
let printind_modifs op= match op with 
  | Set (ind1,sym1,set1) ->printind_name ind1^printind_symbols sym1^printind_set set1 
  | Rel (ind1,sym1,ind2) ->printind_name ind1^printind_symbols sym1^printind_name ind2 
  | Addint (ind1,ind2,sym1,int) ->printind_name ind1^"="^printind_name ind2^printind_symbols sym1^string_of_int int 
  | Addcst (ind1,ind2,sym1,cst1,ind3) ->printind_name ind1^"="^printind_name ind2^printind_symbols sym1^printind_const cst1^printind_name ind3 
  | EXFORALL ind1 ->"∀"^printind_name ind1 
  | EXEXISTS ind1 ->"∃"^printind_name ind1 
let rec printiopl il = match il with []->""|i::tl->printind_modifs i^","^printiopl tl 
let printi i = printind_name (ind_name i)^" "^printiopl (ind_modifs_list i) 
let printcons v = match cons v with AC -> if sign v then "=" else "≠" | BC -> if sign v then "≥" else "<" 
let rec isppp il = match il with [] -> [] | i::tl -> match i with Ind (P _,_) -> [i] | _ -> isppp tl
let rec isttt il = match il with [] -> [] | i::tl -> match i with Ind (T _,_) -> [i] | _ -> isttt tl
let rec printind_name_list il = match il with []->""|i::tl->printind_name (ind_name i) 
let rec printiopl_list il = match il with []->""|i::tl->printiopl (ind_modifs_list i)
let printglobal_event e = 
  let right = hd (match isppp (index_list e) with [] -> isttt (index_list e) | _ -> isppp (index_list e)) in
  let left = removes_index right (index_list e) in
  printind_name_list left^printcons e^printind_name (ind_name right)^printiopl_list (index_list e)
let printevent_var v = match name v with 
  | X -> "   X"^printglobal_event v
  | B i -> "ERROR B " 
  | T -> "ERROR T " 
  | I -> "   I"^printcons v^printi (hd (index_list v)) 
  | V -> "   V"^printcons v^printi (hd (index_list v)) 
  | N -> "   N"^printcons v^printi (hd (index_list v)) 
  | O -> "   X"^printglobal_event v
let rec printe el = match el with []->"" | e::tl -> match e with  
  |F|IM|FE|R -> "? "^printe tl 
  | T -> printe tl 
  | Var v -> printevent_var v^printe tl

(*IV.2 - Print explanation in LaTex*) 
let printsymtex s = match s with PLUS-> "+"|MINUS->"-"|IN->" \\in "|NEQ->" \\neq "|LEQ->" \\leq "|GEQ->" \\geq "|EQ->"=" 
let printioptex op= match op with 
  | Set (ind1,sym1,set1) ->printind_name ind1^printsymtex sym1^printind_set set1 
  | Rel (ind1,sym1,ind2) ->printind_name ind1^printsymtex sym1^printind_name ind2 
  | Addint (ind1,ind2,sym1,int) ->printind_name ind1^"="^printind_name ind2^printsymtex sym1^string_of_int int 
  | Addcst (ind1,ind2,sym1,cst1,ind3) ->printind_name ind1^"="^printind_name ind2^printsymtex sym1^printind_const cst1^"_{"^printind_name ind3^"}" 
  | EXFORALL ind1 ->"\\forall "^printind_name ind1 
  | EXEXISTS ind1 ->"\\exists "^printind_name ind1 
let rec printiopltex il = match il with []->""|i::[]->printioptex i|i::tl->printioptex i^",~"^printiopltex tl 
let printitex i = printind_name (ind_name i)^(if ind_modifs_list i!=[]then ",~" else "")^printiopltex (ind_modifs_list i) 
let printconstex v = match cons v with AC -> if sign v then "=" else " \\neq " | BC -> if sign v then " \\geq " else "<"
let rec printiopl_listtex il = match il with []->""|i::tl->(if ind_modifs_list i!=[]then ",~" else "")^printiopltex (ind_modifs_list i)^printiopl_listtex tl
let printglobal_eventtex e = 
  let right = hd (isppp (index_list e)@isttt (index_list e)) in
  let left = removes_index right (index_list e) in
  "_{"^printind_name_list left^"}"^printconstex e^printind_name (ind_name right)^""^printiopl_listtex (index_list e)
let printvartex v = match name v with 
  | X -> "X"^printglobal_eventtex v
  | B i -> "ERROR B " 
  | T -> "ERROR T " 
  | I -> "I"^printconstex v^printitex (hd (index_list v)) 
  | V -> "V"^printconstex v^printitex (hd (index_list v)) 
  | N -> "N"^printconstex v^printitex (hd (index_list v)) 
  | O -> "O"^printglobal_eventtex v 
let rec printetex el = match el with []->"" | e::tl -> match e with  
  |F|IM|FE|R -> "? "^printetex tl 
  | T -> printetex tl
  | Var v ->printvartex v^(match tl with []->""|v2::_->match v2 with Var _ -> "~~~~"|_->"")^printetex tl 
let rec printfraqtex el x fic = match el with  
  | [] -> () 
  | e::tl -> fprintf fic "%s" ("$$\\frac{"^e^"}{"^printvartex x^"}$$ ");printfraqtex tl x fic 

(*V - Global constraints*)

(*V.1 -Main explanation functions*)
let explain e dec = 
  let fic = open_out "exp.tex" in 
  let cl = ctr_with_event e dec in  
  let _ = printfraqtex (map (fun l-> printetex l) (removeimp (analysis (EXOR (e,flatten (map (fun c-> map (fun de -> rule0 e de c dec []) (same_name e (decomp_event_list c))) cl)))))) e fic in
  close_out fic 
let rec explainallaux el dec fic =
  match el with []->() | e::tl -> 
    let cl = ctr_with_event e dec in  
    let _ = printfraqtex (map (fun l-> printetex l) (removeimp (analysis (EXOR (e,flatten (map (fun c-> map (fun de -> rule0 e de c dec []) (same_name e (decomp_event_list c))) cl)))))) e fic in
    let e = n e in
    let _ = printfraqtex (map (fun l-> printetex l) (removeimp (analysis (EXOR (e,flatten (map (fun c-> map (fun de -> rule0 e de c dec []) (same_name e (decomp_event_list c))) cl)))))) e fic in
    explainallaux tl dec fic
let explainall el dec str = 
  let fic = open_out str in 
  let _ = explainallaux el dec fic in
  close_out fic 

(*V.2 - Decompositions*)
let alleq  = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, BC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule3, [Decomp_devent (true , (B 1), id, oni); Reified_devent (true, (B 2), id, i_out)]);
              Decomp (2, rule3, [Decomp_devent (false, (B 1), id, oni); Reified_devent (true, (B 3), id, i_out)]);
              Decomp (4, rule4, [Decomp_devent (true , (B 2), id, id); Decomp_devent (true, (B 3), id, id)])]
let alldiff= [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule5, [Decomp_devent (true , (B 1), id, oni)])]
let cumul  = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, BC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule3, [Decomp_devent (true , (B 1), tplusci (C 1), tminusci (C 1)); Decomp_devent (false, (B 1), id, id); Reified_devent (true, (B 2), id, id)]);
              Decomp (3, rule5, [Decomp_devent (true , (B 2), id, oni)])]
let gcc    = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule7, [Decomp_devent (true , (B 1), id, oni)])]
let gccn   = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule6, [Decomp_devent (true , (B 1), id, oni); Reified_devent (true, (B 2), agg_functions [foralli;p_out], agg_functions [i_out;forallp])]);
              Decomp (3, rule1, [Global_devent (true ,  O   , id, id, BC); Reified_devent (true, (B 2), id, id)])]
let incr   = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, BC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule4, [Decomp_devent (false, (B 1), id, id); Decomp_devent (true , (B 1), iminus 1, iplus 1)])]
let decr   = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, BC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule4, [Decomp_devent (true , (B 1), id, id); Decomp_devent (false , (B 1), iminus 1, iplus 1)])]
let elem   = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule1, [Global_devent (true ,  I   , id, id, AC); Reified_devent (true, (B 2), id, id)]);
              Decomp (3, rule1, [Global_devent (true ,  V   , id, id, AC); Reified_devent (true, (B 3), id, id)]);
              Decomp (4, rule4, [Decomp_devent (false, (B 3), foralli, i_out); Decomp_devent (false, (B 2), forallt, t_out); Decomp_devent (true , (B 1), id, id)]);
              Decomp (4, rule4, [Decomp_devent (true , (B 3), foralli, i_out); Decomp_devent (false, (B 2), forallt, t_out); Decomp_devent (false, (B 1), id, id)])] 
let nvalues= [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (1, rule1, [Global_devent (true ,  N   , id, id, AC); Reified_devent (true, (B 4), id, id)]);
              Decomp (2, rule4, [Decomp_devent (true , (B 1), id, oni); Reified_devent (true, (B 2), id, i_out)]);
              Decomp (3, rule7, [Decomp_devent (true , (B 2), id, ont); Reified_devent (true, (B 4), agg_functions [foralli;p_out], agg_functions [i_out;t_out;forallp])])]
let atleastnvalues = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
                      Decomp (1, rule1, [Global_devent (true ,  N   , id, id, BC); Reified_devent (true, (B 4), id, id)]);
                      Decomp (2, rule4, [Decomp_devent (true , (B 1), id, oni); Reified_devent (true, (B 2), foralli, i_out)]);
                      Decomp (3, rule6, [Decomp_devent (true , (B 2), id, ont); Reified_devent (true, (B 4), agg_functions [foralli;p_out], agg_functions [i_out;t_out;forallp])])]
let atmostnvalues  = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
                      Decomp (1, rule1, [Global_devent (true ,  N   , id, id, BC); Reified_devent (true, (B 4), id, id)]);
                      Decomp (2, rule4, [Decomp_devent (true , (B 1), id, oni); Reified_devent (true, (B 2), foralli, i_out)]);
                      Decomp (3, rule5, [Decomp_devent (true , (B 2), id, ont); Reified_devent (false, (B 4), agg_functions [foralli;p_out], agg_functions [i_out;t_out;forallp])])]
let among  = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule4, [Decomp_devent (true , (B 1), id, ontin (D 4)); Reified_devent (true, (B 2), id, t_out)]);
              Decomp (3, rule7, [Decomp_devent (true , (B 2), id, oni)])]
let regular= [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule4, [Decomp_devent (true , (B 1), id, id);Decomp_devent (false, (B 1), agg_functions [iminus 1;tprimin (D 8)], agg_functions [iplus 1;tprimin (D 9)])])]
let roots  = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule7, [Decomp_devent (true , (B 1), id, ontin (D 5))]);
              Decomp (2, rule7, [Decomp_devent (true , (B 1), id, ontin (D 6))])]
let range  = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule6, [Decomp_devent (true , (B 1), id, ontin (D 5))]);
              Decomp (2, rule7, [Decomp_devent (true , (B 1), id, ontin (D 6))])]
let table  = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule3, [Decomp_devent (true , (B 1), id, oni); Reified_devent (true, (B 2), id, agg_functions [i_out])]);
              Decomp (4, rule4, [Decomp_devent (true , (B 2), id, onr)])]

(*TODO: try*)
let binpacking = [Decomp (1, rule1, [Global_devent (true ,  X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
                   Decomp (2, rule5, [Decomp_devent (true , (B 1), id, oni)])]


(*Global_event(boolean, variable name, list of (index, changes to the index), consistancy)*)
let xbc = Global_event (true, X, [Ind (I 1, []); Ind (T 1, [])], BC)
let xac = Global_event (true, X, [Ind (I 1, []); Ind (T 1, [])], AC)
let nbc = Global_event (true, N, [Ind (P 1, [])], BC)
let nac = Global_event (true, N, [Ind (P 1, [])], AC)
let i   = Global_event (true, I, [Ind (I 1, [])], AC)
let v   = Global_event (true, V, [Ind (T 1, [])], AC)
let ngbc= Global_event (true, O, [Ind (T 1, []); Ind (P 1, [])], BC)
let x3ac= Global_event (true, X, [Ind (I 1, []); Ind (T 1, []);Ind (R 1, [])], AC)
let xpac= Global_event (true, X, [Ind (I 1, []); Ind (P 1, [])], AC)

let _ = explain xbc incr
let _ = explainall [xbc] alleq "resultats/allequal.tex"
let _ = explainall [xac] alldiff "resultats/alldifferent.tex"
let _ = explainall [xbc] cumul "resultats/cumulative.tex"
let _ = explainall [xac;ngbc] gccn "resultats/gcc.tex"
let _ = explainall [xbc] decr "resultats/decreasing.tex"
let _ = explainall [xbc] incr "resultats/increasing.tex"
let _ = explainall [xac;i;v] elem "resultats/element.tex"
let _ = explainall [xac;nac] nvalues "resultats/nvalues.tex"
let _ = explainall [xac;nbc] atleastnvalues "resultats/atleastnvalues.tex"
let _ = explainall [xac;nbc] atmostnvalues "resultats/atmostnvalues.tex"
let _ = explainall [xac] among "resultats/among.tex"
let _ = explainall [xac] regular "resultats/regular.tex"
let _ = explainall [xac] roots "resultats/roots.tex"
let _ = explainall [xac] range "resultats/range.tex"
let _ = explainall [x3ac] table "resultats/table.tex"

let _ = explainall [xpac] binpacking "resultats/binpacking.tex"