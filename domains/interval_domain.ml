(*
  Cours "Typage et Analyse Statique"
  Université Pierre et Marie Curie
  Antoine Miné 2015
*)

(* 
   The interval domain
 *)

open Abstract_syntax_tree
open Value_domain

  
module Intervals = (struct

  
  (* types *)
  (* ***** *)
  type bound =
    | Int of Z.t
    | INF
    | MINF

  let bound_to_string (a:bound) : string = match a with
    | Int a -> Z.to_string a
    | INF -> "INF"
    | MINF -> "MINF"

    (* -a *)
  let bound_neg (a:bound) : bound = match a with
    | MINF -> INF
    | INF -> MINF
    | Int i -> Int (Z.neg i)

  (* a+b *)
  let bound_add (a:bound) (b:bound) : bound = match a,b with
    | MINF, INF | INF, MINF -> invalid_arg "bound_add"
    | MINF,_ | _,MINF -> MINF
    | INF,_ | _,INF -> INF
    | Int i, Int j -> Int (Z.add i j)  

  let bound_mul (a:bound) (b:bound) : bound = match a,b with
    | MINF, INF | INF, MINF -> MINF
    | Int Z.zero,_ | _,Int Z.zero -> Int Z.zero
    | MINF, MINF -> INF
    | MINF, Int x | Int x, MINF -> let x2 = Z.sign x in
      if x2=(-1) then INF
      else if x2=1 then MINF
      else Int Z.zero
    | INF, Int x | Int x, INF -> let x2 = Z.sign x in
      if x2=(-1) then MINF
      else if x2=1 then INF
      else Int Z.zero

  (* compare a et b, retourne -1, 0 ou 1 *)
  let bound_cmp (a:bound) (b:bound) : int = match a,b with
    | MINF, MINF | INF,INF -> 0
    | MINF,_ | _,INF -> -1
    | INF,_ | _,MINF -> 1
    | Int i, Int j -> Z.compare i j

  let bound_min (a:bound) (b:bound) : bound = 
    let x = bound_cmp a b in
      if x=(-1) || x=0 then a
      else b

  let bound_max (a:bound) (b:bound) : bound =
    let x = bound_cmp a b in
      if(x=(-1) || x=0) then b
      else a



  (* type of abstract values *)
  type t =
    | Itv of bound * bound 
    | BOT

  (* utilities *)
  (* ********* *)


  (* lift unary arithmetic operations, from integers to t *)
  let lift1 f x =
    match x with
    | Itv (a,b) -> f a b
    | BOT -> BOT

  (* lift binary arithmetic operations *)
  let lift2 f (x:t) (y:t) :t =
    match x,y with
    | BOT,_ | _,BOT -> BOT
    | Itv (a, b), Itv(c, d) -> Itv(f a c, f b d)
          


  (* interface implementation *)
  (* ************************ *)

  (* bottom value *)
  let bottom = BOT

  (* interval *)
  let rand x y =
    if x=y || x<y then Itv (Int x, Int y)
    else BOT


  (* arithmetic operations *)

  let neg (x:t) : t = lift1 (fun a b -> Itv (bound_neg b, bound_neg a)) x

  let add a b = lift2 (fun  i j k l -> Itv(bound_add i k, bound_add j l) a b

  let sub a b = a, b

  let mul a b = a, b

  let modulo a b = a, b

  let div a b = a, b


  (* set-theoretic operations *)
  
  let join a b = match a,b with
  | BOT,x | x,BOT -> x
  | Itv(i, j), Itv(k, l) -> Itv(bound_min i k, bound_max j l)

  let meet a b : t = match a,b with
  | Itv(i, j), Itv(k, l) -> let maxac = bound_max i k in
      let minbd = bound_min j l in
        let ppoe = bound_cmp maxac minbd in
          if(ppoe=(-1) || ppoe=0) then
            Itv (maxac, minbd)
          else BOT
  | _ -> BOT


  (* no need for a widening as the domain has finite height; we use the join *)
  let widen = join


  (* comparison operations (filters) *)

  let eq a b = a, b

  let neq a b = a, b
      
  let geq (a:t) (b:t) = a, b
      
  let gt a b = a, b


  (* subset inclusion of concretizations *)
  let subset a b = match a,b with
  | BOT,_ -> true
  | _, BOT -> false
  | Itv (a,b), Itv(c,d) -> bound_cmp a c >= 0 && bound_cmp b d <= 0

  (* check the emptyness of the concretization *)
  let is_bottom a =
    a=BOT

  (* prints abstract element *)
  let print fmt (x:t) = match x with
  | BOT -> Format.fprintf fmt "bottom"
  | Itv((a:bound), (b:bound)) -> Format.fprintf fmt "[%s, %s]" (bound_to_string a) (bound_to_string b)


  (* operator dispatch *)
        
  let unary x op = match op with
  | AST_UNARY_PLUS  -> x
  | AST_UNARY_MINUS -> neg x

  let binary x y op = match op with
  | AST_PLUS     -> add x y
  | AST_MINUS    -> sub x y
  | AST_MULTIPLY -> mul x y
  | AST_DIVIDE   -> div x y
  | AST_MODULO   -> modulo x y

  let compare x y op = match op with
  | AST_EQUAL         -> eq x y
  | AST_NOT_EQUAL     -> neq x y
  | AST_GREATER_EQUAL -> geq x y
  | AST_GREATER       -> gt x y
  | AST_LESS_EQUAL    -> let y',x' = geq y x in x',y'
  | AST_LESS          -> let y',x' = gt y x in x',y'


  let bwd_unary x op r = match op with
  | AST_UNARY_PLUS  -> meet x r
  | AST_UNARY_MINUS -> meet x (neg r)

        
  let bwd_binary x y op r = match op with

  | AST_PLUS ->
      (* r=x+y => x=r-y and y=r-x *)      
      meet x (sub r y), meet y (sub r x)

  | AST_MINUS ->
      (* r=x-y => x=y+r and y=x-r *)
      meet x (add y r), meet y (sub y r)
        
  | AST_MULTIPLY ->
      (* r=x*y => (x=r/y or y=r=0) and (y=r/x or x=r=0)  *)
      let contains_zero o = subset (const Z.zero) o in
      (if contains_zero y && contains_zero r then x else meet x (div r y)),
      (if contains_zero x && contains_zero r then y else meet y (div r x))

  | AST_DIVIDE ->
      (* r = x/y  => x=r*y and y=x/r*)
      meet x (mul y r), meet y (div y r)

  | AST_MODULO ->
      x, y
        
      
end : VALUE_DOMAIN)

    
