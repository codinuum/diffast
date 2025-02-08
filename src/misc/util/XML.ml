(*
   Copyright 2012-2024 Codinuum Software Lab <https://codinuum.com>

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
(* XML.ml *)


module C = Compression
module M = Markup

let sprintf = Printf.sprintf

let header = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"

let rules = [
  "&",  "&amp;";
  "<",  "&lt;";
  ">",  "&gt;";
  "\"", "&quot;";
  "'",  "&apos;";
]

let inv_rules = List.map (fun (o, n) -> n, o) rules

let mkpat rules =
  Str.regexp
    (String.concat "\\|"
       (List.map (fun (x, _) -> sprintf "\\(%s\\)" x) rules))

let subst rules =
  let pat = mkpat rules in
  let conv s =
    let ss = Str.matched_string s in
    try
      List.assoc ss rules
    with
      Not_found -> s
  in
  Str.global_substitute pat conv


let encode_string = subst rules

let decode_string = subst inv_rules



(*let unsafe_chars = "'\t\n"^Netencoding.Html.unsafe_chars_html4*)
(*let unsafe_chars = Netencoding.Html.unsafe_chars_html4
let _encode_string = Netencoding.Html.encode ~in_enc:`Enc_utf8 ~out_enc:`Enc_utf8 ~unsafe_chars ()
let _decode_string = Netencoding.Html.decode ~entity_base:`Xml ~in_enc:`Enc_utf8 ~out_enc:`Enc_utf8 ()
let encode_string s =
  let x = String.escaped s in
   _encode_string x

let decode_string s =
  let x = _decode_string s in
  Scanf.unescaped x*)


let get_local_part qualified_name =
  try
    let i = String.rindex qualified_name ':' in
    let len = (String.length qualified_name) - i - 1 in
    String.sub qualified_name (i+1) len
  with
    Not_found -> qualified_name


type name = string * string

exception Attr_not_found of string

let null_name = (("", "") : name)
let conv_name (p, ln) = p^ln

class node
    ?(name=null_name)
    ?(attr_list=[])
    ?(children=[])
    ?(text=[])
    ?(lc=(1,0))
    ()
    =
  object (_ : 'self)
    val localname = snd name
    val tag = conv_name name
    val attr_list_ =
      List.map
        (fun (n, v) ->
          let k = conv_name n in
          k, v
        ) attr_list

    method localname = localname

    method tag = tag

    method raw_attr_list = attr_list
    method attr_list = attr_list_

    method data = String.concat "" text
    method raw_data = text

    method children : 'self list = children

    method iter_children f = List.iter f children

    method get_attr (a : string) =
      try
        List.assoc a attr_list_
      with
        Not_found -> raise (Attr_not_found a)

    method to_string =
      let buf = Buffer.create 0 in
      let add = Buffer.add_string buf in
      add "<";
      add tag;
      List.iter
        (fun (k, v) ->
          add " ";
          add k;
          add "=\"";
          add v;
          add "\""
        ) attr_list_;
      add ">";
      Buffer.contents buf

    method lc = lc
  end

let null_node = new node()

class ns_manager = object
  val tbl = (Hashtbl.create 0 : (string, string) Hashtbl.t)

  method reset () = Hashtbl.clear tbl

  method add_ns pfx ns = Hashtbl.add tbl pfx ns

  method find pfx =
    try
      Some (Hashtbl.find tbl pfx)
    with _ -> None
end


let parse_xchannel ?(ns=new ns_manager) (ch : Xchannel.in_channel) =
  let get_char () =
    try
      Some (ch#input_char())
    with _ -> None
  in
  try
    let parser =
      M.fn get_char
      |> M.parse_xml ~namespace:ns#find
    in
    let get_lc () =
      let l, c = M.location parser in
      (l, c - 1)
    in
    let text text =
      let lc = get_lc() in
      new node ~text ~lc ()
    in
    let element name attr_list children =
      let lc = get_lc() in
      new node ~name ~attr_list ~children ~lc ()
    in
    let root_opt =
      parser
      |> M.signals
      |> M.tree ~text ~element
    in
    match root_opt with
    | Some root -> root
    | None -> null_node
  with
    e -> failwith ("XML.parse_xchannel: "^(Printexc.to_string e))

let parse_file ?(ns=new ns_manager) (fname : string) =
  let comp = C.from_filename fname in
  let ch = new Xchannel.in_channel ~comp (Xchannel.Source.of_file fname) in
  parse_xchannel ~ns ch

