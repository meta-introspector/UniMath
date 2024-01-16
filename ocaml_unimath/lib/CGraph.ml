open Graph
open PartA
open PartB
open PartD
open PartD0
open Preamble
open Propositions
open Sets
open UnivalenceAxiom

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type precgraph =
  (coq_UU, (coq_UU, (__ -> __, __ -> __) dirprod) total2) total2

(** val make_precgraph : ('a2 -> 'a1) -> ('a2 -> 'a1) -> precgraph **)

let make_precgraph s t =
  { pr1 = __; pr2 = { pr1 = __; pr2 =
    (make_dirprod (Obj.magic s) (Obj.magic t)) } }

type node = __

type arc = __

(** val source : precgraph -> arc -> node **)

let source g =
  g.pr2.pr2.pr1

(** val target : precgraph -> arc -> node **)

let target g =
  g.pr2.pr2.pr2

type has_nodeset = node isaset

type has_arcset = arc isaset

type cgraph = (precgraph, (node isaset, arc isaset) dirprod) total2

(** val make_cgraph : precgraph -> node isaset -> arc isaset -> cgraph **)

let make_cgraph g h k =
  { pr1 = g; pr2 = (make_dirprod h k) }

(** val precgraph_of_cgraph : cgraph -> precgraph **)

let precgraph_of_cgraph t =
  t.pr1

(** val isaset_node : cgraph -> node isaset **)

let isaset_node g =
  g.pr2.pr1

(** val node_set : cgraph -> hSet **)

let node_set g =
  make_hSet (isaset_node g)

(** val isaset_arc : cgraph -> arc isaset **)

let isaset_arc g =
  g.pr2.pr2

(** val arc_set : cgraph -> hSet **)

let arc_set g =
  make_hSet (isaset_arc g)

type is_cgraph_mor = (arc -> node paths, arc -> node paths) dirprod

type cgraph_mor = (node -> node, (arc -> arc, is_cgraph_mor) total2) total2

(** val make_cgraph_mor :
    precgraph -> precgraph -> (node -> node) -> (arc -> arc) -> is_cgraph_mor
    -> cgraph_mor **)

let make_cgraph_mor _ _ p_UU2080_ p_UU2081_ h =
  { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_; pr2 = h } }

(** val onnode : precgraph -> precgraph -> cgraph_mor -> node -> node **)

let onnode _ _ t =
  t.pr1

(** val onarc : precgraph -> precgraph -> cgraph_mor -> arc -> arc **)

let onarc _ _ f =
  f.pr2.pr1

(** val preserves_source :
    precgraph -> precgraph -> cgraph_mor -> arc -> node paths **)

let preserves_source _ _ p =
  p.pr2.pr2.pr1

(** val preserves_target :
    precgraph -> precgraph -> cgraph_mor -> arc -> node paths **)

let preserves_target _ _ p =
  p.pr2.pr2.pr2

(** val is_cgraph_mor_id : precgraph -> is_cgraph_mor **)

let is_cgraph_mor_id _ =
  make_dirprod (fun _ -> Coq_paths_refl) (fun _ -> Coq_paths_refl)

(** val cgraph_mor_id : precgraph -> cgraph_mor **)

let cgraph_mor_id g =
  make_cgraph_mor g g idfun idfun (is_cgraph_mor_id g)

(** val is_cgraph_mor_comp :
    precgraph -> precgraph -> precgraph -> cgraph_mor -> cgraph_mor ->
    is_cgraph_mor **)

let is_cgraph_mor_comp g h k p q =
  make_dirprod (fun f ->
    pathscomp0 (source k (onarc h k q (onarc g h p f)))
      (onnode h k q (source h (onarc g h p f)))
      (onnode h k q (onnode g h p (source g f)))
      (preserves_source h k q (onarc g h p f))
      (maponpaths (onnode h k q) (source h (onarc g h p f))
        (onnode g h p (source g f)) (preserves_source g h p f))) (fun f ->
    pathscomp0 (target k (onarc h k q (onarc g h p f)))
      (onnode h k q (target h (onarc g h p f)))
      (onnode h k q (onnode g h p (target g f)))
      (preserves_target h k q (onarc g h p f))
      (maponpaths (onnode h k q) (target h (onarc g h p f))
        (onnode g h p (target g f)) (preserves_target g h p f)))

(** val cgraph_mor_comp :
    precgraph -> precgraph -> precgraph -> cgraph_mor -> cgraph_mor ->
    cgraph_mor **)

let cgraph_mor_comp g h k p q =
  make_cgraph_mor g k (funcomp (onnode g h p) (onnode h k q))
    (funcomp (onarc g h p) (onarc h k q)) (is_cgraph_mor_comp g h k p q)

(** val cgraph_mor_id_left :
    precgraph -> precgraph -> cgraph_mor -> cgraph_mor paths **)

let cgraph_mor_id_left g h p =
  let p_UU2080_ = p.pr1 in
  let pr3 = p.pr2 in
  let p_UU2081_ = pr3.pr1 in
  let h0 = pr3.pr2 in
  pair_path_in2 p_UU2080_ { pr1 =
    (funcomp (onarc g g (cgraph_mor_id g))
      (onarc g h { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_; pr2 = h0 } }));
    pr2 =
    (is_cgraph_mor_comp g g h (cgraph_mor_id g) { pr1 = p_UU2080_; pr2 =
      { pr1 = p_UU2081_; pr2 = h0 } }) } { pr1 = p_UU2081_; pr2 = h0 }
    (pair_path_in2 p_UU2081_
      (is_cgraph_mor_comp g g h (cgraph_mor_id g) { pr1 = p_UU2080_; pr2 =
        { pr1 = p_UU2081_; pr2 = h0 } }) h0
      (dirprod_paths
        (is_cgraph_mor_comp g g h (cgraph_mor_id g) { pr1 = p_UU2080_; pr2 =
          { pr1 = p_UU2081_; pr2 = h0 } }) h0
        (Obj.magic funextsec
          (Obj.magic is_cgraph_mor_comp g g h (cgraph_mor_id g) { pr1 =
            p_UU2080_; pr2 = { pr1 = p_UU2081_; pr2 = h0 } }).pr1
          (Obj.magic h0).pr1 (fun f ->
          Obj.magic pathscomp0rid (source h (p_UU2081_ f))
            (p_UU2080_ (source g f)) (h0.pr1 f)))
        (Obj.magic funextsec
          (Obj.magic is_cgraph_mor_comp g g h (cgraph_mor_id g) { pr1 =
            p_UU2080_; pr2 = { pr1 = p_UU2081_; pr2 = h0 } }).pr2
          (Obj.magic h0).pr2 (fun f ->
          Obj.magic pathscomp0rid (target h (p_UU2081_ f))
            (p_UU2080_ (target g f)) (h0.pr2 f)))))

(** val cgraph_mor_id_right :
    precgraph -> precgraph -> cgraph_mor -> cgraph_mor paths **)

let cgraph_mor_id_right g h p =
  let p_UU2080_ = p.pr1 in
  let pr3 = p.pr2 in
  let p_UU2081_ = pr3.pr1 in
  let h0 = pr3.pr2 in
  pair_path_in2 p_UU2080_ { pr1 =
    (funcomp
      (onarc g h { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_; pr2 = h0 } })
      (onarc h h (cgraph_mor_id h))); pr2 =
    (is_cgraph_mor_comp g h h { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_;
      pr2 = h0 } } (cgraph_mor_id h)) } { pr1 = p_UU2081_; pr2 = h0 }
    (pair_path_in2 p_UU2081_
      (is_cgraph_mor_comp g h h { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_;
        pr2 = h0 } } (cgraph_mor_id h)) h0
      (dirprod_paths
        (is_cgraph_mor_comp g h h { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_;
          pr2 = h0 } } (cgraph_mor_id h)) h0
        (Obj.magic funextsec
          (Obj.magic is_cgraph_mor_comp g h h { pr1 = p_UU2080_; pr2 =
            { pr1 = p_UU2081_; pr2 = h0 } } (cgraph_mor_id h)).pr1
          (Obj.magic h0).pr1 (fun f ->
          Obj.magic maponpathsidfun (h.pr2.pr2.pr1 (p_UU2081_ f))
            (p_UU2080_ (source g f)) (h0.pr1 f)))
        (Obj.magic funextsec
          (Obj.magic is_cgraph_mor_comp g h h { pr1 = p_UU2080_; pr2 =
            { pr1 = p_UU2081_; pr2 = h0 } } (cgraph_mor_id h)).pr2
          (Obj.magic h0).pr2 (fun f ->
          Obj.magic maponpathsidfun (h.pr2.pr2.pr2 (p_UU2081_ f))
            (p_UU2080_ (target g f)) (h0.pr2 f)))))

(** val cgraph_mor_comp_assoc :
    precgraph -> precgraph -> precgraph -> precgraph -> cgraph_mor ->
    cgraph_mor -> cgraph_mor -> cgraph_mor paths **)

let cgraph_mor_comp_assoc g1 g2 g3 g4 p q r =
  let p_UU2080_ = p.pr1 in
  let pr3 = p.pr2 in
  let p_UU2081_ = pr3.pr1 in
  let h = pr3.pr2 in
  let q_UU2080_ = q.pr1 in
  let pr4 = q.pr2 in
  let q_UU2081_ = pr4.pr1 in
  let k = pr4.pr2 in
  let r_UU2080_ = r.pr1 in
  let pr5 = r.pr2 in
  let r_UU2081_ = pr5.pr1 in
  let l = pr5.pr2 in
  pair_path_in2
    (funcomp
      (onnode g1 g3
        (cgraph_mor_comp g1 g2 g3 { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_;
          pr2 = h } } { pr1 = q_UU2080_; pr2 = { pr1 = q_UU2081_; pr2 = k } }))
      (onnode g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 = r_UU2081_; pr2 = l } }))
    { pr1 =
    (funcomp
      (onarc g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_; pr2 = h } })
      (onarc g2 g4
        (cgraph_mor_comp g2 g3 g4 { pr1 = q_UU2080_; pr2 = { pr1 = q_UU2081_;
          pr2 = k } } { pr1 = r_UU2080_; pr2 = { pr1 = r_UU2081_; pr2 = l } })));
    pr2 =
    (is_cgraph_mor_comp g1 g2 g4 { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_;
      pr2 = h } }
      (cgraph_mor_comp g2 g3 g4 { pr1 = q_UU2080_; pr2 = { pr1 = q_UU2081_;
        pr2 = k } } { pr1 = r_UU2080_; pr2 = { pr1 = r_UU2081_; pr2 = l } })) }
    { pr1 =
    (funcomp
      (onarc g1 g3
        (cgraph_mor_comp g1 g2 g3 { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_;
          pr2 = h } } { pr1 = q_UU2080_; pr2 = { pr1 = q_UU2081_; pr2 = k } }))
      (onarc g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 = r_UU2081_; pr2 = l } }));
    pr2 =
    (is_cgraph_mor_comp g1 g3 g4
      (cgraph_mor_comp g1 g2 g3 { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_;
        pr2 = h } } { pr1 = q_UU2080_; pr2 = { pr1 = q_UU2081_; pr2 = k } })
      { pr1 = r_UU2080_; pr2 = { pr1 = r_UU2081_; pr2 = l } }) }
    (pair_path_in2
      (funcomp
        (onarc g1 g3
          (cgraph_mor_comp g1 g2 g3 { pr1 = p_UU2080_; pr2 = { pr1 =
            p_UU2081_; pr2 = h } } { pr1 = q_UU2080_; pr2 = { pr1 =
            q_UU2081_; pr2 = k } }))
        (onarc g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 = r_UU2081_; pr2 = l } }))
      (is_cgraph_mor_comp g1 g2 g4 { pr1 = p_UU2080_; pr2 = { pr1 =
        p_UU2081_; pr2 = h } }
        (cgraph_mor_comp g2 g3 g4 { pr1 = q_UU2080_; pr2 = { pr1 = q_UU2081_;
          pr2 = k } } { pr1 = r_UU2080_; pr2 = { pr1 = r_UU2081_; pr2 = l } }))
      (is_cgraph_mor_comp g1 g3 g4
        (cgraph_mor_comp g1 g2 g3 { pr1 = p_UU2080_; pr2 = { pr1 = p_UU2081_;
          pr2 = h } } { pr1 = q_UU2080_; pr2 = { pr1 = q_UU2081_; pr2 = k } })
        { pr1 = r_UU2080_; pr2 = { pr1 = r_UU2081_; pr2 = l } })
      (dirprod_paths
        (is_cgraph_mor_comp g1 g2 g4 { pr1 = p_UU2080_; pr2 = { pr1 =
          p_UU2081_; pr2 = h } }
          (cgraph_mor_comp g2 g3 g4 { pr1 = q_UU2080_; pr2 = { pr1 =
            q_UU2081_; pr2 = k } } { pr1 = r_UU2080_; pr2 = { pr1 =
            r_UU2081_; pr2 = l } }))
        (is_cgraph_mor_comp g1 g3 g4
          (cgraph_mor_comp g1 g2 g3 { pr1 = p_UU2080_; pr2 = { pr1 =
            p_UU2081_; pr2 = h } } { pr1 = q_UU2080_; pr2 = { pr1 =
            q_UU2081_; pr2 = k } }) { pr1 = r_UU2080_; pr2 = { pr1 =
          r_UU2081_; pr2 = l } })
        (Obj.magic funextsec (fun f ->
          Obj.magic pathscomp0
            (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
            (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
            (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
            (pathscomp0 (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
              (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
              (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                (q_UU2080_ (source g2 (p_UU2081_ f)))
                (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                  q_UU2081_; pr2 = k } } (p_UU2081_ f))))
            (maponpaths (funcomp q_UU2080_ r_UU2080_)
              (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
              (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                p_UU2081_; pr2 = h } } f))) (fun f ->
          Obj.magic pathscomp0
            (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
            (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
            (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
            (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
              r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
            (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
              (q_UU2080_ (p_UU2080_ (source g1 f)))
              (pathscomp0 (source g3 (q_UU2081_ (p_UU2081_ f)))
                (q_UU2080_ (source g2 (p_UU2081_ f)))
                (q_UU2080_ (p_UU2080_ (source g1 f)))
                (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                  q_UU2081_; pr2 = k } } (p_UU2081_ f))
                (maponpaths q_UU2080_ (source g2 (p_UU2081_ f))
                  (p_UU2080_ (source g1 f))
                  (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f))))) (fun f ->
          pathscomp0
            (Obj.magic pathscomp0
              (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
              (pathscomp0 (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                  r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
                (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (source g2 (p_UU2081_ f)))
                  (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f))))
              (maponpaths (funcomp q_UU2080_ r_UU2080_)
                (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                  p_UU2081_; pr2 = h } } f)))
            (Obj.magic pathscomp0
              (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
              (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
              (pathscomp0 (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (source g2 (p_UU2081_ f)))
                  (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                (maponpaths (funcomp q_UU2080_ r_UU2080_)
                  (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                  (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f))))
            (Obj.magic pathscomp0
              (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
              (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
              (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                (q_UU2080_ (p_UU2080_ (source g1 f)))
                (pathscomp0 (source g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (source g2 (p_UU2081_ f)))
                  (q_UU2080_ (p_UU2080_ (source g1 f)))
                  (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f))
                  (maponpaths q_UU2080_ (source g2 (p_UU2081_ f))
                    (p_UU2080_ (source g1 f))
                    (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                      p_UU2081_; pr2 = h } } f)))))
            (pathsinv0
              (Obj.magic pathscomp0
                (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                  r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
                (pathscomp0 (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                  (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (source g2 (p_UU2081_ f)))
                    (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                  (maponpaths (funcomp q_UU2080_ r_UU2080_)
                    (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                    (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                      p_UU2081_; pr2 = h } } f))))
              (Obj.magic pathscomp0
                (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                (pathscomp0 (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                  (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                  (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                    r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
                  (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (source g2 (p_UU2081_ f)))
                    (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f))))
                (maponpaths (funcomp q_UU2080_ r_UU2080_)
                  (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                  (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f)))
              (Obj.magic path_assoc
                (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                  r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
                (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (source g2 (p_UU2081_ f)))
                  (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                (maponpaths (funcomp q_UU2080_ r_UU2080_)
                  (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                  (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f))))
            (maponpaths
              (Obj.magic pathscomp0
                (source g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                (preserves_source g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                  r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f))))
              (pathscomp0 (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (source g2 (p_UU2081_ f)))
                  (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                (maponpaths (funcomp q_UU2080_ r_UU2080_)
                  (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                  (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f)))
              (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                (q_UU2080_ (p_UU2080_ (source g1 f)))
                (pathscomp0 (source g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (source g2 (p_UU2081_ f)))
                  (q_UU2080_ (p_UU2080_ (source g1 f)))
                  (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f))
                  (maponpaths q_UU2080_ (source g2 (p_UU2081_ f))
                    (p_UU2080_ (source g1 f))
                    (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                      p_UU2081_; pr2 = h } } f))))
              (pathsinv0
                (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (p_UU2080_ (source g1 f)))
                  (pathscomp0 (source g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (source g2 (p_UU2081_ f)))
                    (q_UU2080_ (p_UU2080_ (source g1 f)))
                    (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f))
                    (maponpaths q_UU2080_ (source g2 (p_UU2081_ f))
                      (p_UU2080_ (source g1 f))
                      (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f))))
                (pathscomp0 (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                  (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (source g2 (p_UU2081_ f)))
                    (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                  (maponpaths (funcomp q_UU2080_ r_UU2080_)
                    (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                    (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                      p_UU2081_; pr2 = h } } f)))
                (pathscomp0
                  (maponpaths r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (p_UU2080_ (source g1 f)))
                    (pathscomp0 (source g3 (q_UU2081_ (p_UU2081_ f)))
                      (q_UU2080_ (source g2 (p_UU2081_ f)))
                      (q_UU2080_ (p_UU2080_ (source g1 f)))
                      (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 =
                        { pr1 = q_UU2081_; pr2 = k } } (p_UU2081_ f))
                      (maponpaths q_UU2080_ (source g2 (p_UU2081_ f))
                        (p_UU2080_ (source g1 f))
                        (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 =
                          { pr1 = p_UU2081_; pr2 = h } } f))))
                  (pathscomp0
                    (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                    (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                    (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                    (maponpaths r_UU2080_
                      (source g3 (q_UU2081_ (p_UU2081_ f)))
                      (q_UU2080_ (source g2 (p_UU2081_ f)))
                      (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 =
                        { pr1 = q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                    (maponpaths r_UU2080_
                      (q_UU2080_ (source g2 (p_UU2081_ f)))
                      (q_UU2080_ (p_UU2080_ (source g1 f)))
                      (maponpaths q_UU2080_ (source g2 (p_UU2081_ f))
                        (p_UU2080_ (source g1 f))
                        (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 =
                          { pr1 = p_UU2081_; pr2 = h } } f))))
                  (pathscomp0
                    (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                    (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                    (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                    (maponpaths r_UU2080_
                      (source g3 (q_UU2081_ (p_UU2081_ f)))
                      (q_UU2080_ (source g2 (p_UU2081_ f)))
                      (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 =
                        { pr1 = q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                    (maponpaths (funcomp q_UU2080_ r_UU2080_)
                      (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                      (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f)))
                  (maponpathscomp0 (source g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (source g2 (p_UU2081_ f)))
                    (q_UU2080_ (p_UU2080_ (source g1 f))) r_UU2080_
                    (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f))
                    (maponpaths q_UU2080_ (source g2 (p_UU2081_ f))
                      (p_UU2080_ (source g1 f))
                      (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f)))
                  (maponpaths
                    (pathscomp0
                      (r_UU2080_ (source g3 (q_UU2081_ (p_UU2081_ f))))
                      (r_UU2080_ (q_UU2080_ (source g2 (p_UU2081_ f))))
                      (r_UU2080_ (q_UU2080_ (p_UU2080_ (source g1 f))))
                      (maponpaths r_UU2080_
                        (source g3 (q_UU2081_ (p_UU2081_ f)))
                        (q_UU2080_ (source g2 (p_UU2081_ f)))
                        (preserves_source g2 g3 { pr1 = q_UU2080_; pr2 =
                          { pr1 = q_UU2081_; pr2 = k } } (p_UU2081_ f))))
                    (maponpaths r_UU2080_
                      (q_UU2080_ (source g2 (p_UU2081_ f)))
                      (q_UU2080_ (p_UU2080_ (source g1 f)))
                      (maponpaths q_UU2080_ (source g2 (p_UU2081_ f))
                        (p_UU2080_ (source g1 f))
                        (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 =
                          { pr1 = p_UU2081_; pr2 = h } } f)))
                    (maponpaths (funcomp q_UU2080_ r_UU2080_)
                      (source g2 (p_UU2081_ f)) (p_UU2080_ (source g1 f))
                      (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f))
                    (maponpathscomp (source g2 (p_UU2081_ f))
                      (p_UU2080_ (source g1 f)) q_UU2080_ r_UU2080_
                      (preserves_source g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f))))))))
        (Obj.magic funextsec (fun f ->
          Obj.magic pathscomp0
            (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
            (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
            (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
            (pathscomp0 (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
              (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
              (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                (q_UU2080_ (target g2 (p_UU2081_ f)))
                (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                  q_UU2081_; pr2 = k } } (p_UU2081_ f))))
            (maponpaths (funcomp q_UU2080_ r_UU2080_)
              (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
              (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                p_UU2081_; pr2 = h } } f))) (fun f ->
          Obj.magic pathscomp0
            (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
            (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
            (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
            (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
              r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
            (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
              (q_UU2080_ (p_UU2080_ (target g1 f)))
              (pathscomp0 (target g3 (q_UU2081_ (p_UU2081_ f)))
                (q_UU2080_ (target g2 (p_UU2081_ f)))
                (q_UU2080_ (p_UU2080_ (target g1 f)))
                (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                  q_UU2081_; pr2 = k } } (p_UU2081_ f))
                (maponpaths q_UU2080_ (target g2 (p_UU2081_ f))
                  (p_UU2080_ (target g1 f))
                  (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f))))) (fun f ->
          pathscomp0
            (Obj.magic pathscomp0
              (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
              (pathscomp0 (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                  r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
                (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (target g2 (p_UU2081_ f)))
                  (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f))))
              (maponpaths (funcomp q_UU2080_ r_UU2080_)
                (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                  p_UU2081_; pr2 = h } } f)))
            (Obj.magic pathscomp0
              (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
              (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
              (pathscomp0 (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (target g2 (p_UU2081_ f)))
                  (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                (maponpaths (funcomp q_UU2080_ r_UU2080_)
                  (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                  (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f))))
            (Obj.magic pathscomp0
              (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
              (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
              (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
              (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                (q_UU2080_ (p_UU2080_ (target g1 f)))
                (pathscomp0 (target g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (target g2 (p_UU2081_ f)))
                  (q_UU2080_ (p_UU2080_ (target g1 f)))
                  (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f))
                  (maponpaths q_UU2080_ (target g2 (p_UU2081_ f))
                    (p_UU2080_ (target g1 f))
                    (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                      p_UU2081_; pr2 = h } } f)))))
            (pathsinv0
              (Obj.magic pathscomp0
                (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                  r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
                (pathscomp0 (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                  (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (target g2 (p_UU2081_ f)))
                    (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                  (maponpaths (funcomp q_UU2080_ r_UU2080_)
                    (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                    (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                      p_UU2081_; pr2 = h } } f))))
              (Obj.magic pathscomp0
                (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                (pathscomp0 (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                  (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                  (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                    r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
                  (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (target g2 (p_UU2081_ f)))
                    (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f))))
                (maponpaths (funcomp q_UU2080_ r_UU2080_)
                  (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                  (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f)))
              (Obj.magic path_assoc
                (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                  r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f)))
                (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (target g2 (p_UU2081_ f)))
                  (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                (maponpaths (funcomp q_UU2080_ r_UU2080_)
                  (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                  (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f))))
            (maponpaths
              (Obj.magic pathscomp0
                (target g4 (r_UU2081_ (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                (preserves_target g3 g4 { pr1 = r_UU2080_; pr2 = { pr1 =
                  r_UU2081_; pr2 = l } } (q_UU2081_ (p_UU2081_ f))))
              (pathscomp0 (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (target g2 (p_UU2081_ f)))
                  (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                (maponpaths (funcomp q_UU2080_ r_UU2080_)
                  (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                  (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                    p_UU2081_; pr2 = h } } f)))
              (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                (q_UU2080_ (p_UU2080_ (target g1 f)))
                (pathscomp0 (target g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (target g2 (p_UU2081_ f)))
                  (q_UU2080_ (p_UU2080_ (target g1 f)))
                  (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                    q_UU2081_; pr2 = k } } (p_UU2081_ f))
                  (maponpaths q_UU2080_ (target g2 (p_UU2081_ f))
                    (p_UU2080_ (target g1 f))
                    (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                      p_UU2081_; pr2 = h } } f))))
              (pathsinv0
                (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                  (q_UU2080_ (p_UU2080_ (target g1 f)))
                  (pathscomp0 (target g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (target g2 (p_UU2081_ f)))
                    (q_UU2080_ (p_UU2080_ (target g1 f)))
                    (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f))
                    (maponpaths q_UU2080_ (target g2 (p_UU2081_ f))
                      (p_UU2080_ (target g1 f))
                      (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f))))
                (pathscomp0 (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                  (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                  (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (target g2 (p_UU2081_ f)))
                    (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                  (maponpaths (funcomp q_UU2080_ r_UU2080_)
                    (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                    (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 = { pr1 =
                      p_UU2081_; pr2 = h } } f)))
                (pathscomp0
                  (maponpaths r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (p_UU2080_ (target g1 f)))
                    (pathscomp0 (target g3 (q_UU2081_ (p_UU2081_ f)))
                      (q_UU2080_ (target g2 (p_UU2081_ f)))
                      (q_UU2080_ (p_UU2080_ (target g1 f)))
                      (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 =
                        { pr1 = q_UU2081_; pr2 = k } } (p_UU2081_ f))
                      (maponpaths q_UU2080_ (target g2 (p_UU2081_ f))
                        (p_UU2080_ (target g1 f))
                        (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 =
                          { pr1 = p_UU2081_; pr2 = h } } f))))
                  (pathscomp0
                    (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                    (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                    (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                    (maponpaths r_UU2080_
                      (target g3 (q_UU2081_ (p_UU2081_ f)))
                      (q_UU2080_ (target g2 (p_UU2081_ f)))
                      (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 =
                        { pr1 = q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                    (maponpaths r_UU2080_
                      (q_UU2080_ (target g2 (p_UU2081_ f)))
                      (q_UU2080_ (p_UU2080_ (target g1 f)))
                      (maponpaths q_UU2080_ (target g2 (p_UU2081_ f))
                        (p_UU2080_ (target g1 f))
                        (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 =
                          { pr1 = p_UU2081_; pr2 = h } } f))))
                  (pathscomp0
                    (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                    (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                    (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                    (maponpaths r_UU2080_
                      (target g3 (q_UU2081_ (p_UU2081_ f)))
                      (q_UU2080_ (target g2 (p_UU2081_ f)))
                      (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 =
                        { pr1 = q_UU2081_; pr2 = k } } (p_UU2081_ f)))
                    (maponpaths (funcomp q_UU2080_ r_UU2080_)
                      (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                      (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f)))
                  (maponpathscomp0 (target g3 (q_UU2081_ (p_UU2081_ f)))
                    (q_UU2080_ (target g2 (p_UU2081_ f)))
                    (q_UU2080_ (p_UU2080_ (target g1 f))) r_UU2080_
                    (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 = { pr1 =
                      q_UU2081_; pr2 = k } } (p_UU2081_ f))
                    (maponpaths q_UU2080_ (target g2 (p_UU2081_ f))
                      (p_UU2080_ (target g1 f))
                      (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f)))
                  (maponpaths
                    (pathscomp0
                      (r_UU2080_ (target g3 (q_UU2081_ (p_UU2081_ f))))
                      (r_UU2080_ (q_UU2080_ (target g2 (p_UU2081_ f))))
                      (r_UU2080_ (q_UU2080_ (p_UU2080_ (target g1 f))))
                      (maponpaths r_UU2080_
                        (target g3 (q_UU2081_ (p_UU2081_ f)))
                        (q_UU2080_ (target g2 (p_UU2081_ f)))
                        (preserves_target g2 g3 { pr1 = q_UU2080_; pr2 =
                          { pr1 = q_UU2081_; pr2 = k } } (p_UU2081_ f))))
                    (maponpaths r_UU2080_
                      (q_UU2080_ (target g2 (p_UU2081_ f)))
                      (q_UU2080_ (p_UU2080_ (target g1 f)))
                      (maponpaths q_UU2080_ (target g2 (p_UU2081_ f))
                        (p_UU2080_ (target g1 f))
                        (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 =
                          { pr1 = p_UU2081_; pr2 = h } } f)))
                    (maponpaths (funcomp q_UU2080_ r_UU2080_)
                      (target g2 (p_UU2081_ f)) (p_UU2080_ (target g1 f))
                      (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f))
                    (maponpathscomp (target g2 (p_UU2081_ f))
                      (p_UU2080_ (target g1 f)) q_UU2080_ r_UU2080_
                      (preserves_target g1 g2 { pr1 = p_UU2080_; pr2 =
                        { pr1 = p_UU2081_; pr2 = h } } f))))))))))

(** val isaprop_is_cgraph_mor :
    precgraph -> precgraph -> (node -> node) -> (arc -> arc) -> has_nodeset
    -> is_cgraph_mor isaprop **)

let isaprop_is_cgraph_mor g h p_UU2080_ p_UU2081_ h0 =
  isapropdirprod
    (impred_isaprop (fun f ->
      h0 (source h (p_UU2081_ f)) (p_UU2080_ (source g f))))
    (impred_isaprop (fun f ->
      h0 (target h (p_UU2081_ f)) (p_UU2080_ (target g f))))

(** val isaset_cgraph_mor :
    precgraph -> precgraph -> has_nodeset -> has_arcset -> cgraph_mor isaset **)

let isaset_cgraph_mor g h h0 k =
  isaset_total2 (funspace_isaset h0) (fun p_UU2080_ ->
    isaset_total2 (funspace_isaset k) (fun p_UU2081_ ->
      isasetaprop (isaprop_is_cgraph_mor g h p_UU2080_ p_UU2081_ h0)))

(** val cgraph_mor_eq_aux :
    precgraph -> precgraph -> cgraph_mor -> cgraph_mor -> (node -> node)
    paths -> (arc -> arc) paths -> has_nodeset -> cgraph_mor paths **)

let cgraph_mor_eq_aux g h p q _ _ h0 =
  let p_UU2080_ = p.pr1 in
  let pr3 = p.pr2 in
  let p_UU2081_ = pr3.pr1 in
  let pr4 = pr3.pr2 in
  let psource = pr4.pr1 in
  let ptarget = pr4.pr2 in
  let pr5 = q.pr2 in
  let q_UU2081_ = pr5.pr1 in
  let pr6 = pr5.pr2 in
  let qsource = pr6.pr1 in
  let qtarget = pr6.pr2 in
  pair_path_in2 p_UU2080_ { pr1 = p_UU2081_; pr2 = { pr1 = psource; pr2 =
    ptarget } } { pr1 = q_UU2081_; pr2 = { pr1 = qsource; pr2 = qtarget } }
    (pair_path_in2 p_UU2081_ { pr1 = psource; pr2 = ptarget } { pr1 =
      qsource; pr2 = qtarget }
      (pathsdirprod psource qsource ptarget qtarget
        (Obj.magic funextsec psource qsource (fun f ->
          let x = source h (p_UU2081_ f) in
          let x' = p_UU2080_ (source g f) in
          let x0 = psource f in
          let x'0 = qsource f in (Obj.magic h0 x x' x0 x'0).pr1))
        (Obj.magic funextsec ptarget qtarget (fun f ->
          let x = target h (p_UU2081_ f) in
          let x' = p_UU2080_ (target g f) in
          let x0 = ptarget f in
          let x'0 = qtarget f in (Obj.magic h0 x x' x0 x'0).pr1))))

(** val cgraph_mor_eq :
    cgraph -> cgraph -> cgraph_mor -> cgraph_mor -> (node -> node paths) ->
    (arc -> arc paths) -> cgraph_mor paths **)

let cgraph_mor_eq g h p q e_UU2080_ e_UU2081_ =
  cgraph_mor_eq_aux (precgraph_of_cgraph g) (precgraph_of_cgraph h) p q
    (funextfun (onnode (precgraph_of_cgraph g) (precgraph_of_cgraph h) p)
      (onnode (precgraph_of_cgraph g) (precgraph_of_cgraph h) q) e_UU2080_)
    (funextfun (onarc (precgraph_of_cgraph g) (precgraph_of_cgraph h) p)
      (onarc (precgraph_of_cgraph g) (precgraph_of_cgraph h) q) e_UU2081_)
    (isaset_node h)

(** val precgraph_weq_pregraph : (precgraph, pregraph) weq **)

let precgraph_weq_pregraph =
  weqfibtototal (fun _ ->
    weqcomp (weqfibtototal (fun _ -> invweq weqfuntoprodtoprod))
      (weqcomp (Obj.magic display_weq) (Obj.magic weqfunfromdirprod)))
