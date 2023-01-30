(*
chunk := block

keywords := | and | break | do | else | elseif | end
	| false | for | function | goto | if | in
	| local | nil | not | or | repeat | return
	| then | true | until | while

var := Name
var := prefixexp "[" exp "]"
var := prefixexp "." Name

block := (stat)*

stat := ";"
stat := "do" block "end"
stat := varlist "=" explist
varlist := var ("," var)*
explist := exp ("," exp)*

stat := "while" exp "do" block "end"
stat := "repeat" block "until" exp
stat := "if" exp "then" block ("elseif" exp "then" block)* ("else" block)? "end"

stat := "goto" Name
stat := label
label := "::" Name "::"

stat := "break"
stat := "return" (explist)? (";")?
// numerical for loop
stat := "for" Name "=" exp "," exp ("," exp)? "do" block "end"
// generic for loop
stat := "for" namelist "in" explist "do" block "end"
namelist := Name ("," Name)*

stat := fncall

stat := "local" attrnamelist ("=" explist)?
attrnamelist := Name (attrib)? ("," Name (attrib)?)*
attrib := "<" Name ">"

exp := prefixexp
exp := nil
exp := false | true
exp := Numeral
exp := LiteralString
exp := functiondef
exp := tableconstructor
exp := "..."
exp := exp binop exp
exp := unop exp
prefixexp := var | functioncall | "(" exp ")"
*)

exception LuaException of string

(*module = LuaChunk*)

module Parse = struct
	module Ctx = struct
		type t = {
			mutable stream: string
		}
	end
	
	type 's parse_fn = (Ctx.t -> 's option)
	
	let is_whitespace (c: char) : bool = (c = ' ' || c = '\t' || c = '\n' || c = '\r')
	
	let is_alpha = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false
	let is_digit = function '0' .. '9' -> true | _ -> false
	
	let rewind_on_fail (parser: 's parse_fn) (ctx: Ctx.t) : ('s option) =
		let prev_stream = ctx.stream
		in match parser ctx with
			| Some res -> Some res
			| None ->
				ctx.stream <- prev_stream;
				None
	
	(** Maps the value of a parser to something else (mapp = map parser! to avoid ambiguity)*)
	let mapp (op: 'a -> 'b) (parser: 'a parse_fn) (ctx: Ctx.t) : 'b option =
		match (parser ctx) with
			| None -> None
			| Some v -> Some (op v)
	
	(** Consumes at least one character *)
	let take_many (atleast_one: bool) (op: char -> bool) (ctx: Ctx.t) : string option =
		if 0 = String.length ctx.stream
		then Some ""
		else
			(* Find first non included index*)
			let new_start_idx = ref 0
			in while !new_start_idx < (String.length ctx.stream) && (op (String.get ctx.stream !new_start_idx)) do
				new_start_idx := !new_start_idx + 1;
			done;
			
			(* If atleast one expected and no character matched return failure *)
			if atleast_one && !new_start_idx = 0
			then None
			else
				(* Get removed text to return *)
				let res_text = String.sub ctx.stream 0 !new_start_idx in
				
				(* Slice text off stream *)
				ctx.stream <- (String.sub ctx.stream !new_start_idx ((String.length ctx.stream) - !new_start_idx));
				
				Some res_text
	
	let char_if (op: char -> bool) (ctx: Ctx.t) : char option =
		if 0 <> (String.length ctx.stream)
		then let first = (String.get ctx.stream 0)
			in if (op first)
			then
				let _ = ctx.stream <- (String.sub ctx.stream 1 ((String.length ctx.stream) - 1))
				in Some first
			else None
		else None
	
	let char_if_map (op: char -> 'a option) (ctx: Ctx.t) : 'a option =
		if 0 <> (String.length ctx.stream)
		then let first = (String.get ctx.stream 0)
			in match (op first) with
				| None -> None
				| Some v ->
					let _ = ctx.stream <- (String.sub ctx.stream 1 ((String.length ctx.stream) - 1))
					in Some v
		else None
	
	let ws (ctx: Ctx.t): string option = take_many false (is_whitespace) ctx
	
	(** Removes leading whitespace from the given parser *)
	let no_ws (parser: 's parse_fn) (ctx: Ctx.t) : 's option =
		let inner ctx =
			let _ = ws ctx
			in parser ctx
		in rewind_on_fail inner ctx
	
	(** Matches the given token or fails *)
	let tok (text: string) (ctx: Ctx.t): string option =
		if String.starts_with ctx.stream ~prefix:text
		then
			let text_len = String.length text
			in ctx.stream <- String.sub ctx.stream text_len ((String.length ctx.stream) - text_len);
			Some text
		else None
	
	let ws_tok (text: string) (ctx: Ctx.t): string option = no_ws (tok text) ctx
	
	let ws_tok_as (text: string) (v: 'a) (ctx: Ctx.t): 'a option =
		mapp (fun _ -> v) (no_ws (tok text)) ctx
	
	let ignore (parser: 's parse_fn) (ctx: Ctx.t) : unit option =
		Option.map (fun _ -> ()) (parser ctx)
	
	let rec any (parsers: 's parse_fn list) (ctx: Ctx.t) : 's option =
		match parsers with
			| [] -> None
			| first :: rest -> match (rewind_on_fail first) ctx with
				| Some res -> Some res
				| None -> any rest ctx
	
	let ident (ctx: Ctx.t) : string option = take_many true (is_alpha) ctx
	
	(** Chains parser functions together for better looking code *)
	let (>>=) (a: 'a parse_fn) (b: 'b parse_fn) : ('a * 'b) parse_fn =
		let inner ctx =
			(*let _ = print_endline ">>= trying left" in*)
			match (a ctx) with
				| None -> None
				| Some a_res -> (*let _ = print_endline ">>= trying right" in*) match (b ctx) with
					| None -> None
					| Some b_res -> Some (a_res, b_res)
		in rewind_on_fail inner
end

module Ast = struct
	type stat_var_decl = {
		var_name: string;
		value_str: string;
	}
	
	type stat =
		| StatVarDecl of stat_var_decl
	
	let parse_stat_var_decl (ctx: Parse.Ctx.t) : stat_var_decl option =
		let open Parse
		in let p = (no_ws ident)
			>>= (no_ws (tok "="))
			>>= (no_ws (ident))
			|> rewind_on_fail
		in match (p ctx) with
			| None -> None
			| Some ((id, _), ex) -> Some {
				var_name = id;
				value_str = ex;
			}
	
	let parse_stat (ctx: Parse.Ctx.t) : stat option =
		Option.map (fun x -> StatVarDecl x) (parse_stat_var_decl ctx)
	
	type ident = string
	
	let parse_ident (ctx: Parse.Ctx.t) : ident option =
		let open Parse
		in ident ctx
	
	type expr =
		| ExprIdent of ident
		| ExprParens of expr_parens
		| ExprUnary of expr_unary
		| ExprBinary of expr_binary
	and expr_parens = {
		inner: expr;
	}
	and expr_unary_op =
		| UnaryOpNot
		| UnaryOpNeg
		| UnaryOpHash
		| UnaryOpTilde
	and expr_unary = {
		op: expr_unary_op;
		inner: expr;
	}
	and expr_bin_op =
		| BinOpExp
		| BinOpMul
		| BinOpDiv
		| BinOpSlashSlash
		| BinOpPerc
		| BinOpAdd
		| BinOpSub
		| BinOpDotDot
		| BinOpShl
		| BinOpShr
		| BinOpAmpersand
		| BinOpTilde
		| BinOpPipe
		| BinOpLt
		| BinOpGt
		| BinOpLte
		| BinOpGte
		| BinOpEq
		| BinOpNe
		| BinOpAnd
		| BinOpOr
	and expr_binary = {
		left: expr;
		op: expr_bin_op;
		right: expr;
	}
	
	(*
	( https://www.lua.org/manual/5.4/manual.html#3.4.8 )
	From higher to lower precedence
		^             (rtl)
		not  -  ~  #  (unary)
		*  /  //  %
		+  -
		..            (rtl)
		<<  >>
		&
		~
		|
		<  >  <=  >=  ~=  ==
		and
		or
	*)
	
	(** Generic template for binary exprs (NOTE: VERY SLOW)*)
	let rec parse_expr_binary_ltr (next_prec: expr Parse.parse_fn) (op_parse: expr_bin_op Parse.parse_fn) (ctx: Parse.Ctx.t) : expr option =
		(*Debug:
		let _ = print_endline "try parse ltr" in*)
		let open Parse
		in let first = (next_prec)
		in let rest = rewind_on_fail ((op_parse) >>= (next_prec))
		
		in let rec process_right' (rest: (expr_bin_op * expr) Parse.parse_fn) (left: expr) (ctx: Parse.Ctx.t) : expr =
			match (rest ctx) with
				| None -> left
				| Some (op, right) ->
					let lhs_expr = ExprBinary {left; op; right}
					in process_right' rest lhs_expr ctx
		
		(* We execute the lhr expr parser only once to avoid exponential explosion*)
		in match first ctx with
			| None -> None
			| Some left -> Some (process_right' rest left ctx)
	
	and parse_expr_binary_rtl (next_prec: expr Parse.parse_fn) (op_parse: expr_bin_op Parse.parse_fn) (ctx: Parse.Ctx.t) : expr option =
		(*Debug:
		let _ = print_endline "try parse ltr" in*)
		let open Parse
		in let first = (next_prec)
		in let rest = rewind_on_fail ((op_parse) >>= (next_prec))
		
		in let rec process_right' (rest: (expr_bin_op * expr) Parse.parse_fn) (left: expr) (ctx: Parse.Ctx.t) : expr =
			match (rest ctx) with
				| None -> left
				| Some (op, right) ->
					let rhs_expr = (process_right' rest right ctx)
					in ExprBinary {left; op; right = rhs_expr}
		
		in match first ctx with
			| None -> None
			| Some left -> Some (process_right' rest left ctx)
		
	and parse_expr_parens (ctx: Parse.Ctx.t) : expr option =
		let open Parse
		in let p = (ws_tok "(")
			>>= (parse_expr)
			>>= (ws_tok ")")
			|> rewind_on_fail
		in match (p ctx) with
			| None -> None
			| Some ((_, inner), _) -> Some (ExprParens {inner})
	
	and parse_expr_ident (ctx: Parse.Ctx.t) : expr option =
		let open Parse
		in (mapp (fun id -> ExprIdent id) (no_ws parse_ident)) ctx
	
	(** Prec 8: atom *)
	and parse_expr_prec_atom (ctx: Parse.Ctx.t) : expr option =
		let open Parse
		in any ([
			(parse_expr_parens);
			(parse_expr_ident);
		]) ctx
	
	(** Prec 7: exp *)
	and parse_expr_prec_exp (ctx: Parse.Ctx.t) : expr option =
		let open Parse
		in let op = (ws_tok_as "^" BinOpExp)
		in parse_expr_binary_rtl (parse_expr_prec_atom) (op) ctx
	
	(** Prec 6: unary (not, neg) *)
	(*
	and parse_expr_prec_unary (ctx: Parse.Ctx.t) : expr option =
		let open Parse
		in let p = (op_parse)
			>>= (parse_expr_prec_exp)
			|> rewind_on_fail
		in match (p ctx) with
			| None -> None
			| Some ((left, op), right) -> Some (ExprBinary {left; op; right})
	*)
	
	(** Prec 5: multiplicative *)
	and parse_expr_prec_multiplicative (ctx: Parse.Ctx.t) : expr option =
		let open Parse
		in let op = (any [
			(ws_tok_as "*" BinOpMul);
			(ws_tok_as "/" BinOpDiv)
		])
		in parse_expr_binary_ltr (parse_expr_prec_exp) (op) ctx
	
	(** Prec 4: additive *)
	and parse_expr_prec_additive (ctx: Parse.Ctx.t) : expr option =
		let open Parse
		in let op = (any [
			(ws_tok_as "+" BinOpAdd);
			(ws_tok_as "-" BinOpSub)
		])
		in parse_expr_binary_ltr (parse_expr_prec_multiplicative) (op) ctx
	
	(** Prec 3: .. *)
	and parse_expr_prec_dotdot (ctx: Parse.Ctx.t) : expr option =
		let open Parse
		in let op = (ws_tok_as ".." BinOpDotDot)
		in parse_expr_binary_ltr (parse_expr_prec_additive) (op) ctx
	
	(** Prec 2: cmp *)
	and parse_expr_prec_cmp (ctx: Parse.Ctx.t) : expr option =
		let open Parse
		in let op = (any [
			(ws_tok_as "<" BinOpLt);
			(ws_tok_as ">" BinOpGt);
			(ws_tok_as "<=" BinOpLte);
			(ws_tok_as ">=" BinOpGte);
			(ws_tok_as "==" BinOpEq);
			(ws_tok_as "~=" BinOpNe)
		])
		in parse_expr_binary_ltr (parse_expr_prec_dotdot) (op) ctx
	
	(** Prec 1: and *)
	and parse_expr_prec_and (ctx: Parse.Ctx.t) : expr option =
		let open Parse
		in let op = (ws_tok_as "and" BinOpAnd)
		in parse_expr_binary_ltr (parse_expr_prec_cmp) (op) ctx
	
	(** Prec 0: or *)
	and parse_expr_prec_or (ctx: Parse.Ctx.t) : expr option =
		let open Parse
		in let op = (ws_tok_as "or" BinOpOr)
		in parse_expr_binary_ltr (parse_expr_prec_and) (op) ctx
	
	and parse_expr (ctx: Parse.Ctx.t) : expr option =
		parse_expr_prec_or ctx
end

module LuaContext = struct
	type t = {dummy: int}
	
	let create = {dummy = 0}
	
	let exec (code: string) (ctx: t) = ();
end

(* Test *)
let _ = LuaContext.create
	|> LuaContext.exec "while 1 == 2 do a = 2 end"

let (pc: Parse.Ctx.t) = {stream = "foo = xyzw"};;
Ast.parse_stat_var_decl pc
