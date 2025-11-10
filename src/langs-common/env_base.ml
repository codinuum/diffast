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
(* env_base.ml *)

[%%prepare_logger]

module Loc = Astloc
module Xlist = Diffast_misc.Xlist
module Xset = Diffast_misc.Xset
module Xfile = Diffast_misc.Xfile
module Xprint = Diffast_misc.Xprint
module Storage = Diffast_misc.Storage

exception File_found of Storage.file

[%%capture_path
class ['src] c = object (self)
  constraint 'src = #Source_base.c

  val source_stack : 'src Stack.t = Stack.create()
  val source_paths : string Xset.t = Xset.create 0

  val mutable lines_read = 0
  val comment_regions = new Regions.c
  val missed_regions  = new Regions.c
  val ignored_regions = new Regions.c

  val mutable enter_source_callback = fun _ -> Sedlexing.Utf8.from_string ""

  val mutable verbose_flag = false
  val mutable search_path_list = []

  val mutable keep_going_flag = false

  val extra_source_file_tbl = Hashtbl.create 0


  method in_included_file =
    (Stack.length source_stack) > 1


  method add_extra_source_file (f : Storage.file) =
    let fp = f#fullpath in
    if not (Hashtbl.mem extra_source_file_tbl fp) then
      Hashtbl.add extra_source_file_tbl fp f

  method extra_source_files =
    Hashtbl.fold (fun _ f l -> f :: l) extra_source_file_tbl []




  method verbose_flag = verbose_flag
  method _set_verbose_flag b = verbose_flag <- b
  method set_verbose_flag = verbose_flag <- true
  method clear_verbose_flag = verbose_flag <- false

  method verbose_msg : 'a. ('a, unit, string, unit) format4 -> 'a = Xprint.verbose verbose_flag


  method keep_going_flag = keep_going_flag
  method _set_keep_going_flag b = keep_going_flag <- b
  method set_keep_going_flag = keep_going_flag <- true
  method clear_keep_going_flag = keep_going_flag <- false



  method set_search_path_list l = search_path_list <- l
  method add_search_path p =
    if not (List.mem p search_path_list) then begin
      [%debug_log "adding %s" p];
      search_path_list <- p :: search_path_list
    end

  method find_path ?(ignore_case=false) p =
    [%debug_log "%s (ignore_case=%B)" p ignore_case];

    let files =
      try

        if Filename.is_relative p then begin (* searching current dir *)
          try
            let src = Stack.top source_stack in
            self#verbose_msg "searching current dir (\"%s\") for \"%s\"..." src#file#dirname p;
            let ap = Xfile.normpath (Filename.concat src#file#dirname p) in
            if src#tree#exists ~ignore_case ap then begin
              let f = new Storage.file ~ignore_case (Storage.Tree src#tree) ap in
              raise (File_found f)
            end
          with
            Stack.Empty -> ()
        end;

        Stack.iter (* searching paths in search_path_list *)
          (fun src ->
            let tree : Storage.tree = src#tree in
            if Filename.is_relative p then begin
              List.iter
                (fun p0 ->
                  self#verbose_msg "searching \"%s\" for \"%s\"..." p0 p;
                  let path = Xfile.normpath (Filename.concat p0 p) in
                  if tree#exists ~ignore_case path then begin
                    let f = new Storage.file ~ignore_case (Storage.Tree tree) path in
                    raise (File_found f)
                  end
                ) search_path_list
            end
            else begin
              if tree#exists ~ignore_case p then begin
                let f = new Storage.file ~ignore_case (Storage.Tree tree) p in
                raise (File_found f)
              end
            end
          ) source_stack;

        begin (* search further *)
          self#verbose_msg "searching further...";

          let dent_file_list = ref [] in
          let scanned_trees = ref [] in

          Stack.iter
            (fun src ->
              let tree : Storage.tree = src#tree in

              if List.memq tree !scanned_trees then
                ()
              else begin
                let moveon =
                  match tree#kind with
                  | Storage.K_GIT _ -> true
                  | Storage.K_FS -> tree#id <> ""
                  | _ -> false
                in
                if moveon then begin
                  let dent_path_l = tree#search_path ~ignore_case "" p in
                  let dent_file_l =
                    List.map
                      (fun (dent, path) ->
                        dent, new Storage.file ~ignore_case (Storage.Tree tree) path
                      ) dent_path_l
                  in
                  dent_file_list := dent_file_l @ !dent_file_list
                end;
                scanned_trees := tree :: !scanned_trees
              end

            ) source_stack;

          match !dent_file_list with
          | [] -> []
          | [dent, file] -> begin
              let p = dent#path in
              self#verbose_msg "adding search path: \"%s\"" p;
              self#add_search_path p;
              [file]
          end
          | _ -> begin
              let cur_path = self#current_source#file#path in
              let max_len = ref 0 in
              let min_len = ref max_int in
              let l =
                List.map
                  (fun (dent, f) ->
                    let len = String.length (Xfile.common_dir_path [f#path;cur_path]) in
                    let n = String.length f#path in
                    if len >= !max_len then begin
                      max_len := len;
                      if n < !min_len then
                        min_len := n;
                    end;
                    dent, f, len, n
                  ) !dent_file_list
              in
              let dir_file_list =
                Xlist.filter_map
                  (fun (d, f, len, n) ->
                    if len = !max_len && n = !min_len then
                      Some (d#path, f)
                    else
                      None
                  ) l
              in
              match dir_file_list with
              | [p, f] ->
                  self#verbose_msg "adding search path: \"%s\"" p;
                  self#add_search_path p;
                  [f]
              | _ -> List.map (fun (_, f) -> f) dir_file_list
          end
        end
      with
        File_found file -> [file]

    in
    let files =
      List.fast_sort (fun f0 f1 -> Stdlib.compare f0#path f1#path) files
    in

    List.iter (fun f -> self#verbose_msg "found: \"%s\"" f#path) files;

    begin %debug_block
      match files with
      | [f] -> [%debug_log "found: \"%s\" --> \"%s\"" p f#path]
      | [] -> [%debug_log "not found: \"%s\"" p]
      | _ -> begin
          [%debug_log "multiple files found: \"%s\"" p];
          List.iter
            (fun f ->
              [%debug_log "\"%s\"" f#path]
            ) files
      end;
    end;

    files



  method init =
    [%debug_log "called"];
    Stack.clear source_stack;
    self#clear_lines_read;
    comment_regions#clear;
    missed_regions#clear;
    ignored_regions#clear

  method lines_read = lines_read
  method clear_lines_read = lines_read <- 0;
  method add_lines_read n = lines_read <- lines_read + n

  method current_source =
    try
      Stack.top source_stack
    with
      Stack.Empty -> failwith "Env_base.c#current_source"


  method current_filename = self#current_source#filename
  method set_current_filename f = self#current_source#set_filename f
  method current_pos_mgr = self#current_source#pos_mgr

  method source_entered (src : 'src) =
    Xset.mem source_paths src#path

  method enter_source (src : 'src) =
    [%debug_log "source=\"%s\"" src#filename];
    Stack.push src source_stack;
    Xset.add source_paths src#path;
    enter_source_callback src

  method exit_source =
    [%debug_log "called"];
    try
      let src = Stack.pop source_stack in
      Xset.remove source_paths src#path;
      self#add_lines_read src#pos_mgr#lines_read;
      src#close
    with
      Stack.Empty -> failwith "Env_base.c#exit_file"

  method comment_regions = comment_regions
  method missed_regions  = missed_regions
  method ignored_regions = ignored_regions

  method set_enter_source_callback f = enter_source_callback <- f


end (* of class Env_base.c *)
]
