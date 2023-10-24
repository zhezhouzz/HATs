type node = int
type btree = int

type effect =
  | CreateTree of (unit -> tree) (* unique tree id *)
  | CreateNode of (unit -> node) (* unique node id *)
  | MemNode of (tree -> node -> bool) (* check membership *)
  | IsLeft of (tree -> node -> node -> bool) (* is left child *)
  | IsRight of (tree -> node -> node -> bool) (* is left child *)
  | GetLeft of (tree -> node -> node option) (* return left child *)
  | GetRight of (tree -> node -> node option) (* return right child *)
  | GetPrarent of (tree -> node -> node option) (* return parent *)
  | AddNode of (tree -> node -> unit) (* add node into tree *)
  | RemoveNode of (tree -> node -> unit) (* remove node from tree *)
  | AddLeft of (tree -> node -> node -> unit) (* add left into tree *)
  | AddRight of (tree -> node -> node -> unit) (* add right into tree *)
  | RemoveLeft of (tree -> node -> unit) (* remove left child from tree *)
  | RemoveRight of (tree -> node -> unit) (* remove left child from tree *)
  | PutLabel of (node -> 'a -> unit)
    (* store a value into node; independent from tree *)
  | GetLabel of (node -> 'a)
(* read a value from node; independent from tree *)

    R_{\Code{contain}}(\Code{i},\Code{v_i}) &\equiv \anyA^*\evoponlyeq{putLabel}{\Code{i}\,\Code{v_i}}{()}\ctxEA{\evop{putLabel}{x\,y}{x = \Code{vid}}}.\anyA^*
    \\R_{\Code{mem}}(\Code{g},\Code{i}) &\equiv \anyA^*\evoponlyeq{addNode}{\Code{g}\,\Code{i}}{()}\ctxEA{\evoponlyeq{removeNode}{\Code{g}\,\Code{i}}{()}}.\anyA^*
    \\R_{\Code{connected'}}(\Code{g},\Code{i},\Code{j}) &\equiv 
    \anyA^*\evoponlyeq{addEdge}{\Code{g}\,\Code{i}\,\Code{j}}{()}\ctxEA{\evoponlyeq{removeEdge}{\Code{g}\,\Code{i}\,\Code{j}}{()}}.\anyA^*
    \\R_{\Code{connected}}(\Code{g},\Code{i},\Code{j}) &\equiv
    R_{\Code{has\_vertex}}(\Code{g},\Code{i}) \land R_{\Code{has\_vertex}}(\Code{g},\Code{j}) \land R_{\Code{connected'}}(\Code{g},\Code{i},\Code{j})
    \\\tau_{\Code{BST}} &\equiv \gv{g}{graph}\gv{i}{vertex}\gv{j}{vertex}\gv{v_i}{int}\gv{v_j}{int}.
    \\&\efftp{\anyA^*}{R_{\Code{connected}}(\Code{g},\Code{i},\Code{j}) \land
    R_{\Code{contain}}(\Code{i},\Code{v_i}) \land R_{\Code{contain}}(\Code{j},\Code{v_j}) \Rrightarrow \evret{\nuot{unit}{\Code{v_i} < \Code{v_j}}}}{unit}
