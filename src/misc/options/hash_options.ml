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


class c = object (self)

  val mutable hash_algo = Xhash.MD5
  method hash_algo = hash_algo
  method set_hash_algo x = hash_algo <- x

  val mutable git_hash_flag = false
  method git_hash_flag = git_hash_flag
  method set_git_hash_flag =
    git_hash_flag <- true;
    self#set_hash_algo Xhash.SHA1
  method clear_git_hash_flag = git_hash_flag <- false

  val mutable path_hash_flag = false
  method path_hash_flag = path_hash_flag
  method set_path_hash_flag =
    path_hash_flag <- true;
    self#set_hash_algo Xhash.SHA1
  method clear_path_hash_flag = path_hash_flag <- false

end
