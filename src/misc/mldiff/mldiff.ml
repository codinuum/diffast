(* $Id: mldiff.ml,v 1.3 2006/05/10 14:51:47 deraugla Exp $ *)
(* Command "diff"
   Parts of Code of GNU diff (analyze.c) translated from C to OCaml
   and adjusted. Basic algorithm described by Eugene W.Myers in:
     "An O(ND) Difference Algorithm and Its Variations" *)

(* 2006/09/06 translated into the standard syntax by codinuum <codinuum@me.com> *)

open Printf

exception DiagReturn of int

let diag fd bd sh xv yv xoff xlim yoff ylim =
  let dmin = xoff - ylim in
  let dmax = xlim - yoff in
  let fmid = xoff - yoff in
  let bmid = xlim - ylim in
  let odd = (fmid - bmid) land 1 <> 0 in
  fd.(sh+fmid) <- xoff;
  bd.(sh+bmid) <- xlim;
  try
    let rec loop fmin fmax bmin bmax =
      let fmin =
        if fmin > dmin then (fd.(sh+fmin-2) <- -1; fmin - 1)
        else fmin + 1
      in
      let fmax =
        if fmax < dmax then (fd.(sh+fmax+2) <- -1; fmax + 1)
        else fmax - 1
      in
      begin
      let rec loop d =
        if d < fmin then ()
        else begin
          let tlo = fd.(sh+d-1) in
          let thi = fd.(sh+d+1) in
          let x = if tlo >= thi then tlo + 1 else thi in
          let x =
            let rec loop xv yv xlim ylim x y =
              if x < xlim && y < ylim && (xv x) == (yv y) then
                loop xv yv xlim ylim (x + 1) (y + 1)
              else x
            in
            loop xv yv xlim ylim x (x - d)
          in
          fd.(sh+d) <- x;
          if odd && bmin <= d && d <= bmax && bd.(sh+d) <= fd.(sh+d) then
            raise (DiagReturn d)
          else loop (d - 2)
        end
      in
      loop fmax
      end;

      let bmin =
        if bmin > dmin then (bd.(sh+bmin-2) <- max_int; bmin - 1)
        else bmin + 1
      in
      let bmax =
        if bmax < dmax then (bd.(sh+bmax+2) <- max_int; bmax + 1)
        else bmax - 1
      in

      begin
      let rec loop d =
        if d < bmin then ()
        else begin
          let tlo = bd.(sh+d-1) in
          let thi = bd.(sh+d+1) in
          let x = if tlo < thi then tlo else thi - 1 in
          let x =
            let rec loop xv yv xoff yoff x y =
              if x > xoff && y > yoff && (xv (x-1)) == (yv (y-1)) then
                loop xv yv xoff yoff (x - 1) (y - 1)
              else x
              in
              loop xv yv xoff yoff x (x - d)
          in
          bd.(sh+d) <- x;
          if not odd && fmin <= d && d <= fmax && bd.(sh+d) <= fd.(sh+d) then
            raise (DiagReturn d)
          else loop (d - 2)
        end
      in
      loop bmax
      end;

      loop fmin fmax bmin bmax
    in
    loop fmid fmid bmid bmid

  with DiagReturn i -> i


let diff_loop a ai b bi n m =
  let fd = Array.make (n + m + 3) 0 in
  let bd = Array.make (n + m + 3) 0 in
  let sh = m + 1 in
  let xvec i = a.(ai.(i)) in
  let yvec j = b.(bi.(j)) in
  let chng1 = Array.make (Array.length a) true in
  let chng2 = Array.make (Array.length b) true in
  for i = 0 to n - 1 do chng1.(ai.(i)) <- false; done;
  for j = 0 to m - 1 do chng2.(bi.(j)) <- false; done;
  let rec loop xoff xlim yoff ylim =
    let xoff, yoff =
      let rec loop xoff yoff =
        if xoff < xlim && yoff < ylim && (xvec xoff) == (yvec yoff) then
          loop (xoff + 1) (yoff + 1)
        else xoff, yoff
        in
        loop xoff yoff
    in
    let xlim, ylim =
      let rec loop xlim ylim =
        if xlim > xoff && ylim > yoff && (xvec (xlim - 1)) == (yvec (ylim - 1))
        then
          loop (xlim - 1) (ylim - 1)
        else xlim, ylim
      in
      loop xlim ylim
    in
    if xoff = xlim then
      for y = yoff to ylim - 1 do chng2.(bi.(y)) <- true; done
    else if yoff = ylim then
      for x = xoff to xlim - 1 do chng1.(ai.(x)) <- true; done
    else begin
      let d = diag fd bd sh xvec yvec xoff xlim yoff ylim in
      let b = bd.(sh+d) in
      loop xoff b yoff (b - d);
      loop b xlim (b - d) ylim;
    end
  in
  loop 0 n 0 m;

  chng1, chng2


(* [make_indexer a b ] returns an array of index of lines of [a] which are
   also present in [b]; this way, the main algorithm can skip lines which,
   anyway, are different. This improves the speed much.
     The same time, this function updates the lines of so that all
   equal lines point to the same string. All lines comparisons in
   the main algorithm can therefore be done with "==" instead of "=",
   what also improves speed. *)

let make_indexer a b =
  let n = Array.length a in
  let htb = Hashtbl.create (10 * Array.length b) in
  Array.iteri
    (fun i e ->
       try b.(i) <- Hashtbl.find htb e with
       Not_found -> Hashtbl.add htb e e)
    b;
  let ai = Array.make n 0 in
  let k =
    let rec loop i k =
      if i = n then k
      else
        let k =
          try
            a.(i) <- Hashtbl.find htb a.(i);
            (* line found (since "Not_found" not raised) *)
            ai.(k) <- i;
            k + 1
          with Not_found -> k
        in
        loop (i + 1) k
      in
      loop 0 0
  in
  Array.sub ai 0 k


let print_result a b chng1 chng2 =
  let rec loop i j =
    if i = Array.length a || j = Array.length b then
      if i < Array.length a then begin
        printf "%dd%d\n" (i + 1) j;
        printf "< %s\n" a.(i);
        loop (i + 1) j
      end
      else if j < Array.length b then begin
        printf "%da%d\n" i (j + 1);
        printf "> %s\n" b.(j);
        loop i (j + 1)
      end
      else ()
    else
      (match (chng1.(i), chng2.(j)) with
       (true, true) -> begin
          let i2 =
            let rec loop i =
              if i = Array.length a || not chng1.(i) then i
              else loop (i + 1)
            in
            loop (i + 1)
          in
          let j2 =
            let rec loop j =
              if j = Array.length b || not chng2.(j) then j
              else loop (j + 1)
            in
            loop (j + 1)
          in
          printf "%d" (i + 1);
          if i2 > i + 1 then printf ",%d" i2 else ();
          printf "c";
          printf "%d" (j + 1);
          if j2 > j + 1 then printf ",%d" j2 else ();
          printf "\n";
          for i = i to i2 - 1 do printf "< %s\n" a.(i); done;
          printf "---\n";
          for j = j to j2 - 1 do printf "> %s\n" b.(j); done;
          loop i2 j2
        end
      | (true, false) -> begin
          let i2 =
            let rec loop i =
              if i = Array.length a || not chng1.(i) then i
              else loop (i + 1)
            in
            loop (i + 1)
          in
          printf "%d" (i + 1);
          if i2 > i + 1 then printf ",%d" i2 else ();
          printf "d%d\n" j;
          for i = i to i2 - 1 do printf "< %s\n" a.(i); done;
          loop i2 j
        end
      | (false, true) -> begin
          let j2 =
            let rec loop j =
              if j = Array.length b || not chng2.(j) then j
              else loop (j + 1)
            in
            loop (j + 1)
          in
          printf "%da%d" i (j + 1);
          if j2 > j + 1 then printf ",%d" j2 else ();
          printf "\n";
          for j = j to j2 - 1 do printf "> %s\n" b.(j); done;
          loop i j2
        end
      | (false, false) ->
          if a.(i) != b.(j) then failwith "internal error"
          else loop (i + 1) (j + 1) );
        flush stdout
  in
  loop 0 0

let diff_them a b =
  let ai = make_indexer a b in
  let bi = make_indexer b a in
  let n = Array.length ai in
  let m = Array.length bi in
  let (chng1, chng2) = diff_loop a ai b bi n m in
  print_result a b chng1 chng2


let read_file f =
  let ic = if f = "-" then stdin else open_in f in
  let rec loop list len =
    match try Some (input_line ic) with End_of_file -> None with
      Some line -> loop (line :: list) (len + 1)
    | None -> begin
        if f = "-" then () else close_in ic;
        let a = Array.make len "" in
        let rec loop i = function
            x :: l -> (a.(i-1) <- x; loop (i - 1) l)
          | [] -> a
        in
        loop len list
      end
    in
    loop [] 0

let diff f1 f2 =
  let a1 = read_file f1 in
  let a2 = read_file f2 in
  diff_them a1 a2


let main () =
  let f1 = Sys.argv.(1) in
  let f2 = Sys.argv.(2) in
  diff f1 f2

(*
let _ = main ()
*)
