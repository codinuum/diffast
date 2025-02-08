(*
   Copyright 2012-2020 Codinuum Software Lab <https://codinuum.com>

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
(* xthread.ml *)

type functions = 
    { f_enter_critical_section : unit -> unit;
      f_exit_critical_section  : unit -> unit;
    }

let register_functions, get_functions =
  let functions = ref 
      { f_enter_critical_section = (fun () -> ());
	f_exit_critical_section = (fun () -> ());
      }
  in
  let reg fs = functions := fs in
  let get () = !functions in
  reg, get

let enter_critical_section () =
  (get_functions()).f_enter_critical_section ()

let exit_critical_section () =
  (get_functions()).f_exit_critical_section ()

