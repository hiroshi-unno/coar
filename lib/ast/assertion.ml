open Core

type t =
  | Type of Rtype.t
  | FinEff of string Grammar.RegWordExp.t
  | InfEff of string Grammar.RegWordExp.t

type direction = DUp | DDown
type dir_map = (Ident.tvar, direction) Map.Poly.t
type priority = Ident.tvar list
type fronts = (Ident.tvar, Logic.term) Map.Poly.t
