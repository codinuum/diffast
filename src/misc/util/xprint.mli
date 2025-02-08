(*
   Copyright 2012-2023 Codinuum Software Lab <https://codinuum.com>

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

val cmd_name : string
val failure : ('a, unit, string, 'b) format4 -> 'a
val message : ('a, unit, string, unit) format4 -> 'a
val verbose : bool -> ('a, unit, string, unit) format4 -> 'a
val warning : ?out:out_channel -> ?head:string -> ('a, unit, string, unit) format4 -> 'a
val error   : ?out:out_channel -> ?head:string -> ('a, unit, string, unit) format4 -> 'a
val println : ('a, unit, string, unit) format4 -> 'a
