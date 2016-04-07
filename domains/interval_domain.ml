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

  (* a*b *)
  let bound_mul (a:bound) (b:bound) : bound = match a,b with
    | MINF, INF | INF, MINF -> MINF
    | MINF, MINF | INF, INF -> INF
    | MINF, Int x | Int x, MINF -> let x2 = Z.sign x in
      if x2=(-1) then INF
      else if x2=1 then MINF
      else Int Z.zero
    | INF, Int x | Int x, INF -> let x2 = Z.sign x in
      if x2=(-1) then MINF
      else if x2=1 then INF
      else Int Z.zero
    | Int x, Int y -> Int (Z.mul x y)

  let bound_div (a:bound) (b:bound) : bound = match a,b with
    | _, INF | _, MINF -> Int Z.zero
    | Int z, Int x -> let s = Z.sign x in
      if s=1 then Int(Z.div z x)
      else if s=(-1) then bound_neg (Int (Z.div z x))
      else invalid_arg "bound_div"
    | INF, Int x -> let s = Z.sign x in
      if s=1 then INF
      else if s=(-1) then MINF
      else invalid_arg "bound_div"
    | MINF, Int x -> let s = Z.sign x in
      if s=1 then MINF
      else if s=(-1) then INF
      else invalid_arg "bound_div"

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
    | Itv (a, b), Itv(c, d) -> f a b c d
          


  (* interface implementation *)
  (* ************************ *)

   (* unrestricted value *)
  let top = Itv(MINF, INF)

  (* bottom value *)
  let bottom = BOT

  (* constant *)
  let const c = Itv(Int c, Int c)

  (* interval *)
  let rand x y =
    if x=y || x<y then Itv (Int x, Int y)
    else BOT


  (* arithmetic operations *)

  let neg (x:t) : t = lift1 (fun a b -> Itv (bound_neg b, bound_neg a)) x

  let add (a:t) (b:t) : t = lift2 (fun  i j k l -> Itv(bound_add i k, bound_add j l)) a b

  let sub (a:t) (b:t) : t = lift2 (fun  i j k l -> Itv(bound_add i (bound_neg l), bound_add j (bound_neg k))) a b

  let mul (j:t) (k:t) : t = lift2 (fun  a b c d -> Itv(bound_min (bound_min (bound_mul a c) (bound_mul a d)) (bound_min (bound_mul b c) (bound_mul b d)), 
                                                       bound_max (bound_max (bound_mul a c) (bound_mul a d)) (bound_max (bound_mul b c) (bound_mul b d)))) j k

  (* a%b *)
  let modulo (a:t) (b:t) : t = lift2 (fun  i j k l -> Itv(Int Z.zero, bound_add l (Int Z.one))) a b

  let div (j:t) (k:t) : t = lift2 (fun  a b c d -> 
    let s = bound_cmp (Int Z.one) c in
      if s=0 || s =(-1) then
        Itv(bound_min (bound_div a c) (bound_div a d), bound_max (bound_div b c) (bound_div b d))
      else let s2 = bound_cmp d (Int (Z.neg Z.one)) in
        if s2=0 || s2=(-1) then
          Itv(bound_min (bound_div b c) (bound_div b d), bound_max (bound_div a c) (bound_div a d))
        else BOT) j k

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



  let widen x y = match x,y with
  |  Itv(a,b), Itv(c,d) -> let cmpac = bound_cmp a c in
      let cmpbd = bound_cmp b d in
        if (cmpac=0 || cmpac=(-1)) then
           if (cmpbd=0 || cmpbd=1) then
              Itv(a, b)
            else Itv(a, INF)
        else if (cmpbd=0 || cmpbd=1) then
          Itv(MINF, b)
        else
          Itv(MINF, INF)
  |  BOT,_ | _,BOT -> BOT


  (* comparison operations (filters) *)

  let eq a b = let m = meet a b in m, m

  let neq a b = match a,b with
    | BOT,_ -> BOT,b
    | _,BOT -> a,BOT
    | Itv(i,j), Itv(k,l) -> let cmpik = bound_cmp i k in
        let cmpjk = bound_cmp j k in
          let cmpil = bound_cmp i l in
            let cmpjl = bound_cmp j l in
              if cmpjk=(-1) || cmpil=1 then a,b
              else if cmpik=0 && cmpjl=0 then BOT,BOT
              else if cmpik=(-1) then
                if cmpjk=0 || cmpjk=1 then Itv(i, bound_add k (bound_neg (Int Z.one))), Itv(k,l)
                else BOT,BOT
              else if cmpjl=0 || cmpjl=(-1) then BOT,BOT
              else Itv(bound_add l (Int Z.one) ,j), Itv(k,l)
      
  let geq a b = match a,b with
   | BOT,_ | _,BOT -> BOT, BOT
   | Itv(i,j), Itv(k,l) -> if bound_cmp j k=(-1) then BOT, BOT
                           else if bound_cmp i l=1 then a,b
                           else if bound_cmp j l=1 then Itv(l, j), Itv(bound_min i k, l)
                           else BOT, BOT
      
  let gt a b = match a,b with
   | BOT,_ | _,BOT -> BOT, BOT
   | Itv(i,j), Itv(k,l) -> if bound_cmp j k=(-1) then BOT, BOT
                           else if bound_cmp i l=1 then a,b
                           else if bound_cmp j l=1 then Itv((bound_add l (Int Z.one)), j), Itv(bound_min i k, l)
                           else BOT, BOT


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
      let contains_zero o = subset (Itv(Int Z.zero, Int Z.zero)) o in
      (if contains_zero y && contains_zero r then x else meet x (div r y)),
      (if contains_zero x && contains_zero r then y else meet y (div r x))

  | AST_DIVIDE ->
      (* r = x/y  => x=r*y and y=x/r*)
      meet x (mul y r), meet y (div y r)

  | AST_MODULO ->
      x, y
        
      
end : VALUE_DOMAIN)