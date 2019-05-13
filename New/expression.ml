
type expr_tree = NULL | Return | Assign of expr_tree*expr_tree | Call of expr_tree*(expr_tree list) | Var of string | Int of int | F of string

exception Empty 
exception Invalid
exception Invalid2
exception Invalid3
exception Invalid4
exception Not_accesible
exception Variable_Not_Accesible
exception Function_Not_Callable


type fp=Frame of (((((expr_tree*int)) list)ref)*(expr_tree)*((expr_tree) list)*((((expr_tree*int)) list)ref)*(((expr_tree)))) (*Frame of (arguments)x(parent)x(children procedures)x(Defined Variables)x(Store Defined Variables upon call and retrieve upon return)*) 


let (mainfunc:fp)=((Frame(ref([]),NULL,([F("P");F("Q")]),ref([(Var"a",0);(Var"b",0);(Var"c",0)]),(F"Main"))))
let (pfunc:fp )=((Frame(ref([(Var"x",0);(Var"y",0)]),F"Main",([F("R");F("S")]),ref([(Var"z",0);(Var"a",0)]),(F"P"))))
let (qfunc:fp )=( (Frame(ref([(Var"z",0);(Var"w",0)]),F"Main",([F("T");F("U")]),ref([(Var"x",0);(Var"b",0)]),(F"Q"))))
let (rfunc:fp )=( (Frame(ref([(Var"w",0);(Var"i",0)]),F"P",([F("V")]),ref([(Var"j",0);(Var"b",0)]),(F"R"))))
let (sfunc:fp )=( (Frame(ref([(Var"c",0);(Var"k",0)]),F"P",([]),ref([(Var"n",0);(Var"m",0)]),(F"S"))))
let (tfunc:fp )=( (Frame(ref([(Var"a",0);(Var"y",0)]),F"Q",([F("W")]),ref([(Var"m",0);(Var"p",0)]),(F"T"))))
let (ufunc:fp )=( (Frame(ref([(Var"c",0);(Var"z",0)]),F"Q",([]),ref([(Var"p",0);(Var"g",0)]),(F"U"))))
let (vfunc:fp )=( (Frame(ref([(Var"m",0);(Var"n",0)]),F"R",([]),ref([(Var"c",0)]),(F"V"))))
let (wfunc:fp )=( (Frame(ref([(Var"m",0);(Var"p",0)]),F"T",([]),ref([(Var"j",0);(Var"h",0)]),(F"W"))))


            
let get_frame (t:expr_tree)=(match t with
                                F("Main")->mainfunc
                                |F("P")->pfunc
                                |F("Q")->qfunc
                                |F("R")->rfunc
                                |F("S")->sfunc
                                |F("T")->tfunc
                                |F("U")->ufunc
                                |F("V")->vfunc
                                |F("W")->wfunc
                            )

let get_new_frame t=(match t with 
            F"Main"->((Frame(ref([]),NULL,([F("P");F("Q")]),ref([(Var"a",0);(Var"b",0);(Var"c",0)]),(F"Main"))))
|F"P"->((Frame(ref([(Var"x",0);(Var"y",0)]),F"Main",([F("R");F("S")]),ref([(Var"z",0);(Var"a",0)]),(F"P"))))
|F"Q"-> ( (Frame(ref([(Var"z",0);(Var"w",0)]),F"Main",([F("T");F("U")]),ref([(Var"x",0);(Var"b",0)]),(F"Q"))))
|F"R"-> ( (Frame(ref([(Var"w",0);(Var"i",0)]),F"P",([F("V")]),ref([(Var"j",0);(Var"b",0)]),(F"R"))))
|F"S"->( (Frame(ref([(Var"c",0);(Var"k",0)]),F"P",([]),ref([(Var"n",0);(Var"m",0)]),(F"S"))))
|F"T"-> ( (Frame(ref([(Var"a",0);(Var"y",0)]),F"Q",([F("W")]),ref([(Var"m",0);(Var"p",0)]),(F"T"))))
|F"U"->( (Frame(ref([(Var"c",0);(Var"z",0)]),F"Q",([]),ref([(Var"p",0);(Var"g",0)]),(F"U"))))
|F"V"->( (Frame(ref([(Var"m",0);(Var"n",0)]),F"R",([]),ref([(Var"c",0)]),(F"V"))))
|F"W"->( (Frame(ref([(Var"m",0);(Var"p",0)]),F"T",([]),ref([(Var"j",0);(Var"h",0)]),(F"W"))))
)

type stack= Stack of ((fp) list)  (* Stack showing functions called upto this point*)
let (sr:stack ref)=ref (Stack([mainfunc]))   (* Stack showing functions called upto this point*)
type callables= Callables of ((expr_tree) list)  (*List of procedures that can be called at this point*)
let (cr:callables ref)=ref (Callables([F"P";F"Q"])) (*List of procedures that can be called at this point*)
type variables= Variables of (((expr_tree*int)) list) (*List of accesible variables at this point*)
let (vr:variables ref)=ref (Variables([(Var"a",0);(Var"b",0);(Var"c",0)])) (*List of accesible variables at this point*)
type display= Display of (((fp) ref) list)  (*Display Register*)
let (dr:display ref)=ref (Display([ref(mainfunc)])) (*Display Register*)

let rec convert (l1)=(match l1 with
                        ([])->([])
                        | (x0::[])->(match x0 with (Var(str),intvalue) ->([Var(str)]))
                        |(x0::xs)->(match x0 with (Var(str),intvalue) ->(((Var(str)))::(convert xs))))

let rec convert2 (l1)=(match l1 with
                         (x0::[])->(match x0 with (Var(str),intvalue) ->([intvalue]))
                        |(x0::xs)->(match x0 with (Var(str),intvalue) ->(((intvalue))::(convert2 xs))))

let rec find (t:expr_tree) (v:variables)=(match v with Variables(l1)->( match (convert (l1)) with
                                []->false
                                |(x0::xs)->(if (t=x0) then true else (find t (Variables(List.tl l1))))))

let rec do_it t x=(match x with (a,b)->(t,b))

let rec replace (t:expr_tree) (x) (lr) (v:variables) ltemp=(match v with Variables(l1)->(match l1 with []->() | (x0::xs)->(match x0 with (a,b)->if (a=t) then (lr:=(ltemp@[(do_it t x)]@xs)) else (replace t x lr (Variables(List.tl l1)) (ltemp@[x0]) ) ) ))



let rec check (t:expr_tree) (calls:callables)=(match calls with Callables(l1)->( match l1 with
                                []->false
                                |(x0::xs)->(if (t=x0)then true else (check t (Callables(xs))))))

let rec find_parent (t:expr_tree)=(match t with 
                                    (F"Main")->([F"Main"])
|(F(str))->(match (get_frame(t)) with (Frame(l1,l2,l3,l4,l5))->(t::(find_parent l2))))

let rec find_callable (t:expr_tree)=(match (find_parent(t)) with
                                    x0::[]->(match (get_frame x0) with ((Frame(_,_,l3,_,_)))->l3)
                                    |(x0::(y0::xs))->(match (get_frame x0) with ((Frame(_,_,l3,_,_)))->l3@(find_callable(y0)))
                                    )
(* let rec modified l1=(match l1 with (x0::[])->[(!x0)]
                                    |(x0::xs)->((!x0)::(modified xs))) *)

let rec setof (l1:(((expr_tree*int)) list)) (l2:(((expr_tree*int)) list))=(match l1 with (x0::[])->(match (x0) with (Var(str),intvalue)-> if (find (Var(str)) (Variables(l2))) then [] else [x0])
                        |(x0::xs)->(match (x0) with (Var(str),intvalue)-> if (find (Var(str)) (Variables(l2))) then ([]@(setof xs l2)) else ([x0]@(setof xs l2))))
let rec accesible_variables (t)=(match (t) with 
                                            (Display(x::[]))->(match !x with Frame(l1,l2,l3,l4,l5)->((!l1)@(!l4)))
                                            |(Display(x::xs))->(match !x with Frame(l1,l2,l3,l4,l5)->((!l1)@(!l4))@( setof (accesible_variables (Display(xs))) ((!l1)@(!l4)) ) ) )(* (match (a,b,c) with ((Var"a",value1),(Var"b",value2),(Var"c",value3))->)[Var"a",;Var"b";Var"c"] *)

let rec find_inside t l=(match l with ([])->false | (x::xs)->(match x with (a,b)-> if(t=a)then true else (find_inside t xs)))

let rec returnit t l=(match l with (x::xs)->(match x with (a,b)-> if(t=a)then x else (returnit t xs)))

let rec get_variables t a=(match t with Int(num)->(Int(num),num)| Var(str)->(match a with Display(x::xs)->(match !x with Frame(l1,l2,l3,l4,l5)-> if ( find_inside t ((!l1)@(!l4)) ) then (returnit t ((!l1)@(!l4)) ) else (get_variables t (Display(xs))) )))

let get_top l1=(match l1 with []->raise Empty
						|(x::xs)->x)

let rec translate l1 l2 t2 ltemp=(match l2 with ((x0)::[])->(match (x0) with (Var(str),intvalue)->(match ((get_variables(List.hd t2) !dr)) with (alpha,intvalue2) ->l1:=((Var(str),intvalue2)::ltemp)))
                            |(x0::xs)->((match (x0) with (Var(str),intvalue)->(match ((get_variables (get_top t2) (!dr))) with (alpha,intvalue2) ->(translate l1 (List.tl l2) (List.tl t2) (ltemp@([(Var(str),intvalue2)]))) ))))

let get_2 (l1)=(match l1 with (x0::[])->raise Invalid
                    |(x0::(y0::xs))->y0)
 

let rec printflist l1=(match l1 with (F(str)::[])->print_endline (str^" ")
                                    |(F(str)::xs)->(print_endline  (str^" ")); printflist xs)
let rec printvarlist l1=(match ((convert l1), (convert2 l1)) with ((Var(str)::[]),(intvalue::[]))->print_endline  (str^"="^string_of_int(intvalue))
                                    |((Var(str)::xs),(intvalue::ys))->print_endline  (str^"="^string_of_int(intvalue)); printvarlist (List.tl l1))
let rec printfplist l1=(match l1 with (x::[])->(match x with Frame(l0,l2,l3,l4,F(str))->print_endline ((str)^" "))
                                    |(x::xs)->(match x with Frame(l0,l2,l3,l4,F(str))->print_endline  ((str)^" "); printfplist xs))
let rec printfprlist l1=(match l1 with (x::[])->printfplist [(!x)]
						|(x::xs)->printfplist [(!x)] ; printfprlist (xs))
(* Function to evaluate value given the parse tree *)
let rec find_in_list t l1=(match l1 with (x1::xs)->(match x1 with Frame(_,_,_,_,F(str1))->(match t with Frame(_,_,_,_,F(str2))-> if (str1=str2) then x1 else (find_in_list t xs) )))
let rec find_in_stack(t:fp)=(match !sr with Stack(l1)->(find_in_list t l1))
let rec find_link (t:fp)=(match t with Frame(l1,l2,l3,l4,l5)->(if (l5=F"Main") then [] else (ref(find_in_stack(get_frame(l2)))::(find_link(get_frame l2)))))

let rec find_variables t v l=(match l with (x::[])->(match !x with Frame(l1,l2,l3,l4,l5)-> (if (find t (Variables(((!l1))))) then (replace t v l1 (Variables(((!l1)))) [] ) else (if (find t (Variables(((!l4))))) then (replace t v l4 (Variables(((!l4)))) []) else raise Not_accesible )   ) )
								|(x::xs)->(match !x with Frame(l1,l2,l3,l4,l5)-> if (find t (Variables(((!l1))))) then (replace t v l1 (Variables(((!l1)))) []) else (if (find t (Variables(((!l4))))) then (replace t v l4 (Variables(((!l4)))) []) else (find_variables t v xs))  ))
let rec find_in_display (t) (v)=(match !dr with Display(l1)-> find_variables t v l1)

let rec  get_name l=(match l with Frame(l0,l2,l3,l4,l5)->l5)

let rec printsr pr=(match (!pr) with (Stack(l1))->printfplist l1) 
let rec printcr pr=(match (!pr) with (Callables(l1))->printflist l1) 
let rec printvr pr=(match (!pr) with (Variables(l1))->printvarlist l1)
let rec printdr pr=(match (!pr) with (Display(l1))->printfprlist l1)

let rec removesr l=(match (!l) with Stack(l1)->(List.hd l1)  )
let rec eval_tree t = (match t with
    NULL            -> raise Empty
| Return        -> (match !sr with Stack(l1)->((sr:=Stack(List.tl(l1))); dr:=Display((ref(get_2 (l1)))::((find_link ( (get_2 (l1)))))); cr:=Callables(find_callable (get_name(get_2 (l1))));vr:=Variables(accesible_variables (!dr) )))
| Assign(t1,t2) -> (match !vr with (Variables(l1))->(match t1 with 
                        (Var(str))->((if(find ((Var(str))) (Variables(l1)))then
                                        (match t2 with
                                    Int(it)->(find_in_display (Var(str)) (Int(it),it)) 
                                    |Var(str2)->(find_in_display (Var(str)) (get_variables(t2) !dr) ) 
                                        )
                                    else (raise Variable_Not_Accesible));vr:=Variables(accesible_variables (!dr) ))
                        |_->raise Invalid
                                ))
                        
    | Call(t1,t2)   -> (match (!cr,!sr) with (Callables(l6),Stack(l7))-> (if (check ((t1)) (Callables(l6)) )then (
                                match (get_frame(t1)) with
                             ((Frame(l1,l2,l3,l4,l5)))->((if(List.length t2=List.length (!l1))then(sr:=Stack((get_new_frame(t1))::(l7));(match (removesr sr) with Frame (l6,l7,l8,l9,l10)->(translate (l6) (!l6) t2 []));dr:=Display((ref(removesr sr))::((find_link (get_frame t1) )))(*unit type*);cr:=Callables(find_callable t1);vr:=Variables(accesible_variables (!dr)))else(raise Invalid)) 
                                 )
                             )
                        else raise Function_Not_Callable
                        ))
    |_              -> raise Invalid 
                    );print_endline("CallingStack");printsr sr;print_endline("CallableFunctions");printcr cr;print_endline("CallableVariables"); printvr vr;print_endline("StaticRegister"); printdr dr
;;

