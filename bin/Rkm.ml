open Ast
open Printf
module T = Type
module S = Solver

let exec name expr =
  print_endline name;
  match Sem.infer Sem.init_context expr with
    | Error xs -> List.iter (printf "  Error: %s\n") xs
    | Ok (e, t, k, _) ->
      match S.solve [k] with
        | Error e ->
          List.iter (fun e -> printf "  Error: %s\n" (S.explain e)) e
        | Ok [] ->
          printf "  Done: %a\n  %a\n" T.output t Core.output e
        | _ ->
          printf "  Error: Certain constraints are not satisfied\n"

let () =
  let cases = [
    "[fail] x", EVar "x";
    "[pass] \\x -> x", EAbs ("x", EVar "x");
    "[fail] \\x -> y", EAbs ("x", EVar "y");
    "[pass] (\\x -> x) (\\x -> x)",
      EApp (EAbs ("x", EVar "x"), EAbs ("x", EVar "x"));
    "[fail] (\\x -> x x)",
      EAbs ("x", EApp (EVar "x", EVar "x"));
    "[fail] \\x -> let bad : \\a b. a -> b; bad = \\y -> x in bad",
      EAbs ("x", ELetA ("bad", T.TPoly ("a", Z.zero, T.TPoly ("b", Z.zero,
                                 T.TArr (T.TRigid ("a", Z.zero), T.TRigid ("b", Z.zero)))),
                        EAbs ("y", EVar "x"),
                        EVar "bad"));
    "[pass] \\x -> let ok = \\y -> x in ok",
      EAbs ("x", ELet ("ok", EAbs ("y", EVar "x"),
                       EVar "ok"));
    "[pass] let id = \\x -> x in (id (), id id)",
      ELet ("id", EAbs ("x", EVar "x"),
            ETup [EApp (EVar "id", ETup []); EApp (EVar "id", EVar "id")]);
    "[fail] let f : \\a b. a -> b; f = \\y -> y in f",
      EAbs ("x", ELetA ("f", T.TPoly ("a", Z.zero, T.TPoly ("b", Z.zero,
                               T.TArr (T.TRigid ("a", Z.zero), T.TRigid ("b", Z.zero)))),
                        EAbs ("y", EVar "y"),
                        EVar "f"));
    "[pass] let f : \\a. a -> a; f = \\y -> y in f",
      ELetA ("f", T.TPoly ("a", Z.zero,
                    T.TArr (T.TRigid ("a", Z.zero), T.TRigid ("a", Z.zero))),
             EAbs ("y", EVar "y"),
             EVar "f");
    "[pass] let f : \\a. a -> a -> (a, a); f = \\x -> \\y -> (x, y) in f",
      ELetA ("f", T.TPoly ("a", Z.zero,
                    T.TArr (T.TRigid ("a", Z.zero),
                      T.TArr (T.TRigid ("a", Z.zero),
                        T.TTup [T.TRigid ("a", Z.zero); T.TRigid ("a", Z.zero)]))),
             EAbs ("x", EAbs ("y", ETup [EVar "x"; EVar "y"])),
             EVar "f");
    "[pass] let f : \\a b. a -> b -> (a, b); f = \\x -> \\y -> (x, y) in f",
      ELetA ("f", T.TPoly ("a", Z.zero, T.TPoly ("b", Z.zero,
                    T.TArr (T.TRigid ("a", Z.zero),
                      T.TArr (T.TRigid ("b", Z.zero),
                        T.TTup [T.TRigid ("a", Z.zero); T.TRigid ("b", Z.zero)])))),
             EAbs ("x", EAbs ("y", ETup [EVar "x"; EVar "y"])),
             EVar "f");
    "[pass] let f = \\x -> \\y -> (x, y) in f",
      ELet ("f", EAbs ("x", EAbs ("y", ETup [EVar "x"; EVar "y"])),
            EVar "f");
  ] in

  List.iter (fun (n, e) -> exec n e; print_endline "") cases
