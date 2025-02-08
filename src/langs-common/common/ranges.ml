(*
   Copyright 2012-2025 Codinuum Software Lab <https://codinuum.com>

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

[%%prepare_logger]

[%%capture_path
class c ini = object
  val mutable ranges = ini

  method add (st, ed) = ranges <- (st, ed) :: ranges
  method to_list = ranges
  method clear = ranges <- []

  method iter f = List.iter f ranges

  method fuse =
    let sorted =
      List.fast_sort
        (fun (st0, _) (st1, _) -> Stdlib.compare st0 st1)
        ranges
    in

    begin %debug_block
      [%debug_log "before fuse:\n"];
      List.iter (fun (st, ed) -> [%debug_log "range: %d-%d\n" st ed]) sorted
    end;

    let fused = ref [] in
    let rec doit = function
      | [] -> ()
      | [reg] -> fused := !fused @ [reg]
      | (st0, ed0)::(st1, ed1)::rest ->
          if st1 > ed0 + 1 then begin
            fused := !fused @ [(st0, ed0)];
            doit ((st1, ed1)::rest)
          end
          else
            doit ((st0, ed1)::rest)
    in
    doit sorted;

    begin %debug_block
      [%debug_log "after fuse:\n"];
      List.iter (fun (st, ed) -> [%debug_log "range: %d-%d\n" st ed]) !fused
    end;

    ranges <- !fused

end (* of Ranges.c *)
]
