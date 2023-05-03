module type T = sig
  include Ty.T

  type 'a typed = { x : 'a; ty : t } [@@deriving sexp]

  val mk_noty : 'a -> 'a typed
  val ( #: ) : 'a -> t -> 'a typed
  val xmap : ('a -> 'b) -> 'a typed -> 'b typed
  val layout_typed : ('a -> string) -> 'a typed -> string
end

(* module F (Ty : Ty.T) : T with type t = Ty.t = struct *)
(*   include Ty *)

(*   type 'a typed = { x : 'a; ty : Ty.t } [@@deriving sexp] *)

(*   let ( #: ) x ty = { x; ty } *)
(*   let mk_noty x = x #: Ty.default_ty *)
(*   let xmap f { x; ty } = { x = f x; ty } *)
(*   let layout_typed f { x; _ } = f x *)
(* end *)
