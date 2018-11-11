let pred_correct =
  QCheck.Test.make ~count:1000 ~name:"pred is correct"
    QCheck.small_int
    (fun x -> (not (x > 0)) || (PRF.eval PRF.pred) [x] = x - 1);;

(* we can check right now the property... *)
QCheck_runner.run_tests ~verbose:true [pred_correct];;
