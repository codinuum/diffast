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


class c = object

  val mutable verbose_flag = false

  method verbose_flag = verbose_flag
  method set_verbose_flag = verbose_flag <- true
  method clear_verbose_flag = verbose_flag <- false

  val mutable search_path_list = []

  method search_path_list = search_path_list
  method set_search_path_list l = search_path_list <- l
  method add_search_path (p : string) = search_path_list <- p :: search_path_list


  val extensions = Xset.create 0

  method add_extensions es =
    [%debug_log "[%s]" (String.concat "," es)];
    Xprint.verbose verbose_flag "supported extensions: %s" (String.concat "," es);
    List.iter (Xset.add extensions) es

  method get_extension name =
    try
      Xfile.get_extension (String.lowercase_ascii name)
    with
      Xfile.No_extension _ -> ""

  method is_valid_extension ext =
    Xset.mem extensions ext

  method check_extension _name =
    let b =
      let name = String.lowercase_ascii _name in
      try
        let ext = Xfile.get_extension name in
        Xset.mem extensions ext
      with
        Xfile.No_extension _ -> false
    in
    (*DEBUG_MSG "%s -> %B" _name b;*)
    b

end
