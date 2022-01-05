type ide = string;;

type exp = CstInt of int
        | CstTrue 
        | CstFalse
        | CstString of string (*+++ definizione dell'espressione stringa +++*)
        | Den of ide
        | Sum of exp * exp
        | Sub of exp * exp
        | Times of exp * exp
        | Ifthenelse of exp * exp * exp
        | Eq of exp * exp
        | Let of ide * exp * exp
        | Fun of ide * exp
        | Letrec of ide * ide * exp * exp
        | Apply of exp * exp 
        (* definizione dell'espressione insieme : ide definisce il tipo, exp list la lista di elementi dell'insieme *)
        | Set of ide * (exp list)
        (* operatore che mi permette di definire un Set vuoto di un tipo preciso *)
        | EmptySet of ide
        (* operatore che mi permette di definire un Set contenente un solo elemento*)
	 	| Singleton of ide * exp
	 	| Union of exp * exp
	 	| Interset of exp * exp
	 	| Diff of exp * exp
	 	| Has_element of exp * exp
 	 	| Insert of exp * exp 
	 	| Remove of exp * exp
	 	| Max of exp
	 	| Min of exp 
	 	| Is_empty of exp
	 	| Is_subset of exp * exp
	 	| ForAll of exp * exp
	 	| Exists of exp * exp
	 	| Map of exp * exp
	 	| Filter of exp * exp
;;

type 'v env = (string * 'v) list;;

type evT = Int of int 
        | Bool of bool 
        | Closure of ide * exp * evT env 
        | RecClosure of ide * ide * exp * evT env 
        | Unbound
    	| String of string (*definizione del tipo di dato stringa*)
        | ValSet of ide * (evT list) (* esprime un Set come ide (tipo) * una lista omogenea di tipo esprimibile*)
    ;;

let emptyEnv  = [ ("", Unbound)] ;;

let bind (s: evT env) (i:string) (x:evT) = ( i, x ) :: s;;

let rec lookup (s:evT env) (i:string) = match s with
	| [] ->  Unbound
	| (j,v)::sl when j = i -> v
	| _::sl -> lookup sl i;;

let typecheck (x, y) = match x with	
	| "int" -> 
	    (match y with 
	       | Int(u) -> true
	       | _ -> false)

	| "bool" -> 
	    (match y with 
	       | Bool(u) -> true
	       | _ -> false)
	      
	| "string" ->
	    (match y with
	       | String(u) -> true
	       | _ -> false)

	|"set" ->
	  	(match y with
	  	  |ValSet(t,u) -> (match t with 
	  		 		| "int" -> true
	  				| "string" -> true
	  				| "bool" -> true
	  				| _ -> false )
	  	  |_ -> false)


	| _ -> failwith ("not a valid type")
;;

(*funzione ausiliaria per controllare che un ide sia di tipo primitivo*)
let is_primitive (x: ide) : bool =
	match x with
	| "int" -> true
	| "string" -> true
	| "bool" -> true
	| _ -> false

(*funzione ausiliaria per controllare che due evT siano set, che abbiano lo stesso tipo e che questo sia primitivo*)
let eq_type_set (s1: evT) (s2: evT) : bool =
	if (typecheck("set",s1) && typecheck("set",s2)) 
		then match(s1,s2) with
			| (ValSet(t1,l1),ValSet(t2,l2)) ->(is_primitive t1 && t1=t2) 
			| (_,_) -> failwith("insiemi istanziati su tipi diversi")
		else failwith("not a set")

(*funzione ausiliaria per controllare che evT passato per parametro sia un set e abbia lo stesso tipo dell'elemento*)
let typecheck_el_set (s: evT) (el: evT) : bool =
	if (typecheck("set",s)) 
		then match s with
			| ValSet(t,l) -> typecheck(t,el) 
			|_ -> failwith ("unexpected")
		else failwith("not a set")


let int_eq(x,y) =   
  match (typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Bool(v = w)
  | (_,_,_,_) -> failwith("run-time error ");;
       
let int_plus(x, y) = 
  match(typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v + w)
  | (_,_,_,_) -> failwith("run-time error ");;

let int_sub(x, y) = 
  match(typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v - w)
  | (_,_,_,_) -> failwith("run-time error ");;

let int_times(x, y) = 
  match(typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v * w)
  | (_,_,_,_) -> failwith("run-time error ");;


let rec eval  (e:exp) (s:evT env) = match e with
	| CstInt(n) -> Int(n)
	| CstTrue -> Bool(true)
	| CstFalse -> Bool(false)
	| CstString(u) -> String(u) (*+++ valutazione del tipo di dato stringa +++*)
	| Eq(e1, e2) -> int_eq((eval e1 s), (eval e2 s))
	| Times(e1,e2) -> int_times((eval e1 s), (eval e2 s))
	| Sum(e1, e2) -> int_plus((eval e1 s), (eval e2 s))
	| Sub(e1, e2) -> int_sub((eval e1 s), (eval e2 s))
	| Ifthenelse(e1,e2,e3) -> let g = eval e1 s in
	      (match (typecheck("bool", g), g) with
	       | (true, Bool(true)) -> eval e2 s
	       | (true, Bool(false)) -> eval e3 s
	       | (_, _) -> failwith ("nonboolean guard"))
	|Den(i) -> lookup s i
	|Let(i, e, ebody) -> eval ebody (bind s i (eval e s))
	|Fun(arg, ebody) -> Closure(arg,ebody,s)
	|Letrec(f, arg, fBody, letBody) -> 
	      let benv = bind (s) (f) (RecClosure(f, arg, fBody,s)) 
	  		in eval letBody benv
	|Apply(eF, eArg) ->
	      let fclosure = eval eF s in 
	      (match fclosure with 
	       | Closure(arg, fbody, fDecEnv) ->
	           let aVal = eval eArg s in
	           let aenv = bind fDecEnv arg aVal in 
	           eval fbody aenv
	       | RecClosure(f, arg, fbody, fDecEnv) ->
	           let aVal = eval eArg s in
	           let rEnv = bind fDecEnv f fclosure in
	           let aenv = bind rEnv arg aVal in 
	           eval fbody aenv
	       | _ -> failwith("non functional value"))


	|Set(tipo,l) -> ValSet (tipo, eval_set tipo l s)

	|EmptySet(tp) -> if (is_primitive tp) then ValSet(tp,[]) else failwith("only primitive types set are allowed")

	|Singleton(tp, el) -> singleton tp el s

	|Union(l1,l2) -> apply_binarySet l1 l2 s unione 

	|Interset(l1,l2) -> apply_binarySet l1 l2 s intersezione

	|Diff(l1,l2) -> apply_binarySet l1 l2 s differenza

	|Has_element(el,where) -> member where el s 
	                                 
	|Insert(el,where) -> checkinsert where el s

	|Remove(el,where) -> checkremove where el s
	 
	|Is_empty(where) -> (let eS = eval where s in
	 							match (typecheck("set",eS),eS) with 
								|(true,ValSet(_,st)) -> if st = [] then Bool(true) else Bool(false)
								|(_,_) -> failwith ("Wrong Type"))

	|Is_subset(l1,l2) -> (let (s1,s2) = (eval l1 s, eval l2 s) in 
	 							match (eq_type_set s1 s2,s1,s2) with
			    				|(true,ValSet(t1,s1),ValSet(t2,s2)) -> Bool(sottoinsieme s1 s2) 
								|(_,_,_) -> failwith("Wrong Type"))

	|Max(where) -> (match eval where s with 
					 	|ValSet("int",st) -> massimo st 
						|_ -> failwith("Wrong Type"))

	|Min(where) -> (match eval where s with 
						|ValSet("int",st) -> minimo st 
						|_ -> failwith("Wrong Type"))

	|ForAll(pred,set) -> (match eval set s with
				 			|(ValSet(tp,s1)) -> (  let myList = applyFunSet pred s1 s in
												   let rec f lis x = 
													match lis with
											 		|[] -> x
											 		|z::zs -> (match (x,z) with 
																|(Bool(b1),Bool(b2)) -> f zs (Bool(b1&&b2))
																|(_,_) -> failwith ("Type error"))
												 	in ( match myList with
													  	 |[]-> Bool(true)
														 |z::zs-> f zs z))
							|_->failwith("Wrong Type"))

	|Exists(pred,set) -> (match eval set s with
				 			|(ValSet(tp,s1)) -> (  let myList = applyFunSet pred s1 s in
										 		   let rec f lis x= 
													match lis with
											   		|[] -> x
											   		|z::zs -> (match (x,z) with 
													 			|(Bool(b1),Bool(b2)) -> f zs (Bool(b1||b2))
													  			|(_,_) -> failwith ("Type error"))
													in ( match myList with
														 |[]-> Bool(false)
														 |z::zs-> f zs z))
							|_->failwith("Wrong Type"))
					
	|Filter(pred,set) -> ( let fClosure = eval pred s in
				 			match eval set s with
				 			|ValSet(t,s1) -> ValSet(t, filter fClosure s1 s)
				 			|_ -> failwith("Wrong Type") )
					
	|Map(func,set) -> ( let fClosure = eval func s in
	 		      match eval set s with
				 |ValSet(t,s1) -> ValSet(t, map  fClosure s1 s)
				 |_ -> failwith("Wrong Type") )
				

	and has_element (e: evT) (st: evT list) : bool =
	    (match st with
		 |[]-> false
		 |x::xs -> if(x=e) then true else has_element e xs)
	  
  	and sottoinsieme (l1: evT list) (l2: evT list) : bool =
		(match (l1,l2) with
		 |([],l) -> true
		 |(l,[]) -> false
		 |(x::xs,l) -> (has_element x l) && sottoinsieme xs l)

  	and massimo (l: evT list) : evT =
		(match l with 
		 |[] -> failwith ("Empty set")
	     |a::ll -> (let rec f lis a = match lis with
       				| [] -> a
        			| x::xs -> if a > x then f xs a
            				else f xs x
      		 		in f ll a))

  	and minimo (l: evT list) : evT =
		(match l with 
		 |[] -> failwith ("Empty Set")
		 |a::ll -> (let rec f lis a = match lis with
       					| [] -> a
        				| x::xs -> if a < x then f xs a
            						else f xs x
      				 in f ll a))

 	and singleton (t: ide) (el: exp) (s: evT env) : evT =
	    (let v = eval el s in 
	    	if (is_primitive t && typecheck(t,v)) 
	    		then ValSet(t,v::[]) 
	    	else failwith("only primitive types set are allowed"))

    and unione (l1: evT list) (l2: evT list) : evT list =
      (match (l1,l2) with
		|([],x) -> x
		|(x,[]) -> x
		|(x::xs,l) -> if (has_element x l )  then unione xs l 
						else x::(unione xs l))
  
    and intersezione ( l1: evT list) (l2: evT list) : evT list = 
      (match (l1,l2) with
		|([],_) -> []
		|(_,[]) -> []
		|(x::xs,l) -> if has_element x l then x::(intersezione xs l)
						else intersezione xs l)

    and differenza (l1: evT list) (l2: evT list) : evT list =
      (match (l1,l2) with 
      	|([],l) -> []
		|(l,[]) -> l
		|(x::xs,l)-> if has_element x l then (differenza xs l)
						else x::(differenza xs l))

  	and applyFunSet (f: exp) (l: evT list) (s: evT env) : evT list = 
	  (let fClosure = eval f s in
	 	match l with 
		 |[]->[]
		 |x::xs -> let res = applyfunction fClosure x s 
		in res::(applyFunSet f xs s))

  	and apply_binarySet (st1: exp) (st2: exp) (s:evT env) f : evT = 
    	let (s1,s2) = (eval st1 s,eval st2 s) in 
  			if(eq_type_set s1 s2) 
  				then match (s1, s2) with 
					|(ValSet(t1,s1),ValSet(t2,s2)) -> ValSet(t1, f s1 s2) 
					|(_,_) -> failwith("Wrong Type")
			else failwith("Wrong Type")  

  	and member (st: exp) (el: exp) (s:evT env)  : evT =
    	let (eV,eS) = (eval el s,eval st s) in 
  			if (typecheck_el_set eS eV) 
  				then match eS with
					|(ValSet(tp,s1)) -> Bool(has_element eV s1) 
					|_-> failwith("Wrong Type")
 			else failwith ("Wrong Type")

  	and checkinsert (st: exp) (el: exp) (s:evT env)  : evT =
    	let (eV,eS) = (eval el s,eval st s) in 
  			if (typecheck_el_set eS eV) 
  				then match eS with
					|(ValSet(tp,s1)) -> if has_element eV s1  then failwith("Duplicate element")
							else ValSet(tp,eV::s1)
					|_-> failwith("Wrong Type")
 			else failwith ("Wrong Type")
 
 	and rimuovi (e: evT) (l: evT list) (s: evT env) : evT list =
      	(match l with
		 |[] -> []
		 |x::xs -> if(e=x) then xs else x::(rimuovi e xs s))

	and checkremove (st: exp) (el: exp) (s:evT env) : evT =
    	let (eV,eS) = (eval el s,eval st s) in 
  			if (typecheck_el_set eS eV) 
  				then match eS with
					|(ValSet(tp,s1)) -> ValSet(tp, rimuovi eV s1 s) 
					|_-> failwith("Wrong Type")
 			else failwith ("Wrong Type")

	and filter (f: evT) (l: evT list) (s: evT env) : evT list =
		(let rec aux (lis: evT list) : evT list =
			match lis with 
			|[] -> []
			|x::xs -> let v = applyfunction f x s in if v=Bool(true) then x::(aux xs) else aux xs
		in aux l)

  	and map (f: evT) (l: evT list) (s: evT env) : evT list =
		(let rec aux (lis: evT list) : evT list =
			match lis with
			|[]->[]
			|x::xs -> let v = applyfunction f x s in v::(aux xs)
		in aux l)

  	and applyfunction (f: evT) (eArg : evT) (s: evT env) : evT = 
		(match f with
			|Closure(arg, fBody, fDecEnv) -> 
				eval fBody (bind fDecEnv arg eArg)
			|RecClosure(g, arg, fBody, fDecEnv) -> 
					let rEnv = (bind fDecEnv g f) in
						let aEnv = (bind rEnv arg eArg) in
							eval fBody aEnv 
			|_ -> failwith("not functional value"))
	
	and eval_set (tipo: ide) (l: exp list) (s: evT env) : evT list =
      	(match l with
       		| [] -> []
       		| x::xs -> (let v = eval x s in
					if (typecheck(tipo, v) && is_primitive tipo) then 
						if (has_element v (eval_set tipo xs s)) then failwith ("Duplicate element")
					 	else v::(eval_set tipo xs s)
					else failwith ("Wrong Type")))
	;;

(*VALUTAZIONE POSITIVA DI UN SET DI TIPO INT*)
let s1= Set("int", [CstInt(2); CstInt(10); CstInt(6);CstInt(0)]);;
eval s1 emptyEnv;; 
(*VALUTAZIONE POSITIVA DI UN SET DI TIPO STRING*)
let s2=Set("string", [CstString("cane"); CstString("gatto"); CstString("kiwi"); CstString("Natale")]);;
eval s2 emptyEnv;;
(*VALUTAZIONE POSITIVA DI UN SET DI TIPO BOOL*)
let s3=Set("bool",[CstTrue;CstFalse]);;
eval s3 emptyEnv;;
(*GENERAZIONE DI UN ERRORE -> PROVO A CREARE UN SET DI UN TIPO NON PRIMITIVO*)
let s3= Set("set",[s1;s2]);;
eval s3 emptyEnv;;
(*GENERAZIONE DI UN ERRORE -> ELEMENTO DUPLICATO*)
let s3 = Set("string", [CstString("robi"); CstString("ciao"); CstString("robi"); CstString("bello")]);;
eval s3 emptyEnv;;
(*GENERAZIONE DI UN ERRORE -> ELEMENTO CON TIPO DIVERSO DAL TIPO DEL SET*)
let s1_3 = Set("int", [CstInt(1); CstInt(2); CstString("pc")]);;
eval s1_3 emptyEnv;;
(*VALUTAZIONE POSITIVA DI UN EMPTY SET INT*)
let s4 = EmptySet("int");;
eval s4 emptyEnv;;
(*GENERAZIONE DI UN ERRORE -> EMPTY SET DI TIPO NON PRIMITIVO*)
let s6= EmptySet("float");;
eval s6 emptyEnv;;
(*VALUTAZIONE POSITIVA DI UN SINGLETON DI TIPO INT*)
let s7 = Singleton("int",CstInt(3));;
eval s7 emptyEnv;;
(*GENERAZIONE DI UN ERRORE -> SINGLETON DI TIPO SET (NON PRIMITIVO)*)
let s77= Singleton("set",s1);;
eval s77 emptyEnv;;
(*VALUTAZIONE POSITIVA DI UN SINGLETON DI TIPO STRING*)
let s8 = Singleton("string",CstString("Natale"));;
eval s8 emptyEnv;;
(*GENERAZIONE DI UN ERRORE -> SINGLETON DI TIPO INT CON ELEMENTO DI TIPO STRING*)
let s9 = Singleton("int",CstString("Natale"));;
eval s9 emptyEnv;;
(*VALUTAZIONE POSITIVA DI UNION*)
let s10 = Union(s1,Singleton("int",CstInt(5)));;
eval s10 emptyEnv;;
(*GENERAZIONE DI UN ERRORE -> UNIONE DI SET DI TIPO DIVERSO  *)
let s11 = Union(s1,s2);;
eval s11 emptyEnv;;
(*VALUTAZIONE POSITIVA DI INTERSET*)
let s12 = Interset(s8,s2);;
eval s12 emptyEnv;;
(*VALUTAZIONE POSITIVA DI DIFF*)
let s14 = Diff(s2,Set("string",[CstString("kiwi");CstString("Natale")]));;
eval s14 emptyEnv;;
(*VALUTAZIONE POSITIVA DI HAS_ELEMENT*)
let s15 = Has_element(CstInt(10),s1);;
eval s15 emptyEnv;;
(*GENERAZIONE DI UN ERRORE -> RICERCA DI UN ELEMENTO DI TIPO STRING IN UN SET DI TIPO INT*)
let s16 = Has_element(CstString("ciao"),s1);;
eval s16 emptyEnv;;
(*VALUTAZIONE POSITIVA DI INSERT*)
let s17 = Insert(CstInt(56),s1);;
eval s17 emptyEnv;;
(*VALUTAZIONE POSITIVA DI REMOVE*)
let s18 = Remove(CstString("kiwi"),s2);;
eval s18 emptyEnv;;
(*VALUTAZIONE POSITIVA DI IS_EMPTY*)
let s19 = Is_empty(s4);;
eval s19 emptyEnv;;
(*VALUTAZIONE POSITIVA DI IS_SUBSET*)
let s20 = Is_subset(Set("int",[CstInt(2);CstInt(0)]),s1);;
eval s20 emptyEnv;;
(*GENERAZIONE DI UN ERRORE -> PASSO UN PARAMETRO CHE NON E' UN SET*)
let s21 = Is_subset(s2,CstString("ciao"));;
eval s21 emptyEnv;;
(*GENERAZIONE DI UN ERRORE -> PASSO SET DI TIPI DIVERSI*)
let s22 = Is_subset(s1,s2);;
eval s22 emptyEnv;;
(*VALUTAZIONE POSITIVA DI MAX*)
let s23 = Max(s1);;
eval s23 emptyEnv;;
(*VALUTAZIONE POSITIVA DI MIN*)
let s24 = Min(s1);;
eval s24 emptyEnv;;
(*GENERAZIONE DI UN ERRORE -> MAX DI UN SET VUOTO*)
let s25 = Min(s4);;
eval s25 emptyEnv;;
(*VALUTAZIONE DI FORALL SU UN SET VUOTO*)
let s26 = ForAll(Fun ("n", Ifthenelse(Eq(Den"n",CstInt(0)),CstTrue,CstFalse)),EmptySet("int"));;
eval s26 emptyEnv;;
(*VALUTAZIONE FORALL -> return false*)
let s27 = ForAll(Fun ("n", Ifthenelse(Eq(Den"n",CstInt(0)),CstTrue,CstFalse)),Set("int",[CstInt(0);CstInt(1)]));;
eval s27 emptyEnv;;
(*VALUTAZIONE FORALL -> return true*)
let s28 = ForAll(Fun ("n", Ifthenelse(Eq(Den"n",CstInt(0)),CstTrue,CstFalse)),Singleton("int",CstInt(0)));;
eval s28 emptyEnv;;
(*VALUTAZIONE EXISTS -> return false*)
let s29 = Exists(Fun ("n", Ifthenelse(Eq(Den"n",CstInt(0)),CstTrue,CstFalse)),Set("int",[CstInt(6);CstInt(1)]));;
eval s29 emptyEnv;;
(*VALUTAZIONE EXISTS -> return true*)
let s30 = Exists(Fun ("n", Ifthenelse(Eq(Den"n",CstInt(0)),CstTrue,CstFalse)),s1);;
eval s30 emptyEnv;;
(*VALUTAZIONE MAP*)
let s31 = Map(Fun("y", Sum(Den "y", CstInt(10))),s1);;
eval s31 emptyEnv;;
(*VALUTAZIONE FILTER*)
let sF= Filter(Fun("n", Ifthenelse(Eq(Den "n", CstInt(0)),CstTrue,CstFalse)),s1);;
eval sF emptyEnv;;



