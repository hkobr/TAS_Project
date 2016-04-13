open Abstract_syntax_tree
open Parity_domain
open Interval_domain
open Value_domain
open Value_reduction

module ParityIntervalsReduction =
(struct

  module A = Intervals
  module B = Parity

  type t = A.t * B.t

  let pair x = (Z.erem x (Z.of_int 2)) = Z.zero

  let reduce ((itv,par):t) =  let a = A.first itv and b = A.second itv in
   let a2 = Z.add a (Z.of_int 1) and b2 = Z.sub b (Z.of_int 1) in
    match B.is_pair par, pair a, pair b with
      | true, true, true   | false, false, false-> itv, par
      | true, true, false  | false, false, true -> if (Z.gt a b2)  then A.bottom,B.bottom else (A.rand a b2), par
      | true, false, false | false, true, true  -> if (Z.gt a2 b2) then A.bottom,B.bottom else (A.rand a2 b2), par
      | true, false, true  | false, true, false -> if (Z.gt a2 b)  then A.bottom,B.bottom else (A.rand a2 b), par


end : VALUE_REDUCTION)