open Core
open Apak
open CfgIr

module RG = Interproc.RG
module G = RG.G
module K = NewtonDomain.K

include Log.Make(struct let name = "cra_newton" end)
module A = Interproc.MakePathExpr(Cra.K)

external caml_add_wpds_rule: K.t -> int -> int -> unit = "add_wpds_rule"
external set_vertices: int -> int -> unit = "set_vertices_wfa"
external set_cWeight: K.t -> unit = "set_compare_weight"
external caml_add_wpds_call_rule: K.t -> int -> int -> int -> unit = "add_wpds_call_rule"
external caml_add_wpds_epsilon_rule: K.t -> int -> unit = "add_wpds_epsilon_rule"
external caml_add_wpds_error_rule: K.t -> int -> int -> unit = "add_wpds_error_rule"

(*Create a function to call out to the weight maker and create a wpds in c*)
let iter_helper rg vertexa vertexb =
  match RG.classify vertexa with
  | `Atom _ ->
    caml_add_wpds_rule (Cra.weight vertexa) vertexa.did vertexb.did
  | `ParBlock func | `Block func ->
    let vertext = (RG.block_entry rg func) in
    caml_add_wpds_call_rule K.one vertexa.did vertext.did vertexb.did

let block_iter rg b = 
  RG.G.iter_edges (iter_helper rg) (RG.block_body rg b);
  caml_add_wpds_epsilon_rule K.one (RG.block_exit rg b).did

let analyze_basic file =
  match file.entry_points with
  | [main] -> begin
      let rg = Interproc.make_recgraph file in
      let rg =
        if !Cra.forward_inv_gen
        then Log.phase "Forward invariant generation" Cra.decorate rg
        else rg
      in
      BatEnum.iter (block_iter rg) (Interproc.RG.blocks rg);
      Interproc.RG.vertices rg |> BatEnum.iter (fun (_, vertex) ->
          match vertex.dkind with
          | Assert (phi, _) ->
            caml_add_wpds_error_rule
              (K.assume (K.F.negate (NewtonDomain.tr_bexpr phi)))
              vertex.did
              (Def.get_location vertex).Cil.line
          | AssertMemSafe (expr, _) -> begin
              let open NewtonDomain in
              match tr_expr expr with
              | TInt _ -> assert false
              | TPointer p ->
                begin
                  let phi =
                    K.F.conj
                      (K.F.geq p.ptr_pos K.T.zero)
                      (K.F.lt p.ptr_pos p.ptr_width)
                  in
                  caml_add_wpds_error_rule
                    (K.assume (K.F.negate phi))
                    vertex.did
                    (Def.get_location vertex).Cil.line
               end
            end
          | _ -> ()
        );
      set_vertices (RG.block_entry rg main).did (RG.block_exit rg main).did;
      let local _ _ = false in
      let query = A.mk_query rg NewtonDomain.weight local main in
      A.compute_summaries query;
      set_cWeight (A.get_summary query main)
    end
  | _ -> assert false

let _ =
  CmdLine.register_pass
    ("-cra_newton_basic",
     analyze_basic,
     " Compositional recurrence analysis via FWPDS")
