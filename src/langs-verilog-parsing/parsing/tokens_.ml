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
(* tokens_.ml *)

module T = Tokens.Make (struct
  let env           = Obj.magic () (* new Parser_aux.env *)
  (*let pos_mgr       = Obj.magic () (* new Position.manager *)*)
  let context_stack = Obj.magic () (* new Context.stack env *)
end)

include T
