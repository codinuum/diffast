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
class c = object (self)
  val mutable regions = []
  val mutable _LOC = 0

  method clear =
    regions <- [];
    _LOC <- 0

  method add_regions rs = List.iter self#add rs

  method add loc =
    [%debug_log "[%s]" (Astloc.to_string loc)];
    begin
      match regions with
      | (st, ed)::rest -> begin
          let ((st0, ed0) as p) = Astloc.to_offsets loc in
          if st0 = ed + 1 then
            regions <- (st, ed0) :: rest
          else
            regions <- p :: regions
      end
      | [] -> regions <- [Astloc.to_offsets loc]
    end;
    _LOC <- _LOC + (loc.Astloc.end_line - loc.Astloc.start_line + 1)

  method dump =
    if regions <> [] then begin
      Printf.printf "regions(LOC=%d):\n" _LOC;
      List.iter
        (fun (st, ed) ->
          Printf.printf "%d-%d\n" st ed
        ) (List.rev regions)
    end

  method get_LOC = _LOC

  method to_offset_ranges = new Ranges.c (List.rev regions)

  method get_offsets =
    let r = self#to_offset_ranges in
    r#fuse;
    r#to_list


end (* of class Regions.c *)
]
