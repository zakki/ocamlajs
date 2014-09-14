(* Pretty-printing of asm.js *)

open Format
open Cmm
open Reg
open Mach
open Proc

(* Layout of the stack frame *)

let stack_offset = ref 0

let frame_size () =
  let sz =
    !stack_offset +
    4 * num_stack_slots.(0) +
    8 * num_stack_slots.(1) +
    8 * num_stack_slots.(2) +
    (if !contains_calls then 4 else 0)
  in Misc.align sz 8

let slot_offset loc cl =
  match loc with
    Incoming n ->
      assert (n >= 0);
      frame_size() + n
  | Local n ->
      if cl = 0
      then !stack_offset + n * 4
      else !stack_offset + num_stack_slots.(0) * 4 + n * 8
  | Outgoing n ->
      assert (n >= 0);
      n

(* Output a stack reference *)

let emit_stack ppf r =
  match r.loc with
  | Stack s ->
      let ofs = slot_offset s (register_class r) in
      fprintf ppf "HEAP32[(sp + %d) >> ???]" ofs
  | _ -> Misc.fatal_error "Emit_arm.emit_stack"

let reg_type r =
  (match r.typ with Addr -> "A" | Int -> "I" | Float -> "F")
let reg ppf r =
  begin match r.loc with
  | Unknown -> ()
  | Reg r ->
      fprintf ppf "%s" (Proc.register_name r)
  | Stack(Local s) ->
      (* fprintf ppf "[s%i]" s *)
      emit_stack ppf r
  | Stack(Incoming s) ->
      (* fprintf ppf "[si%i]" s *)
      emit_stack ppf r
  | Stack(Outgoing s) ->
      (* fprintf ppf "[so%i]" s *)
      emit_stack ppf r
  end

let regs ppf v =
  match Array.length v with
  | 0 -> ()
  | 1 -> reg ppf v.(0)
  | n -> reg ppf v.(0);
         for i = 1 to n-1 do fprintf ppf " %a" reg v.(i) done

let regset ppf s =
  let first = ref true in
  Reg.Set.iter
    (fun r ->
      if !first then begin first := false; fprintf ppf "%a" reg r end
      else fprintf ppf "@ %a" reg r)
    s

let regsetaddr ppf s =
  let first = ref true in
  Reg.Set.iter
    (fun r ->
      if !first then begin first := false; fprintf ppf "%a" reg r end
      else fprintf ppf "@ %a" reg r;
      match r.typ with Addr -> fprintf ppf "*" | _ -> ())
    s

let intcomp = function
  | Isigned c -> Printf.sprintf " %s " (Printcmm.comparison c)
  | Iunsigned c -> Printf.sprintf " %s!!!unsigned!!! " (Printcmm.comparison c)

let floatcomp c =
    Printf.sprintf " %s " (Printcmm.comparison c)

let intop = function
  | Iadd -> " + "
  | Isub -> " - "
  | Imul -> " * "
  | Imulh -> " *h "
  | Idiv -> " div "
  | Imod -> " mod "
  | Iand -> " & "
  | Ior ->  " | "
  | Ixor -> " ^ "
  | Ilsl -> " << "
  | Ilsr -> " >>u "
  | Iasr -> " >>s "
  | Icomp cmp -> intcomp cmp
  | Icheckbound -> " check > "

let test tst ppf arg =
  match tst with
  | Itruetest -> reg ppf arg.(0)
  | Ifalsetest -> fprintf ppf "! %a" reg arg.(0)
  | Iinttest cmp -> fprintf ppf "(%a|0)%s(%a|0)" reg arg.(0) (intcomp cmp) reg arg.(1)
  | Iinttest_imm(cmp, n) -> fprintf ppf "(%a|0)%s(%i|0)" reg arg.(0) (intcomp cmp) n
  | Ifloattest(cmp, neg) ->
      fprintf ppf "%s(+(%a) %s +(%a))"
       (if neg then "! " else "")
       reg arg.(0) (floatcomp cmp) reg arg.(1)
  | Ieventest -> fprintf ppf "%a & 1 == 0" reg arg.(0)
  | Ioddtest -> fprintf ppf "%a & 1 == 1" reg arg.(0)

let heap f reg ppf t =
  let shift = (match t with
  | Byte_unsigned ->
    fprintf ppf "HEAPU8";
    0
  | Byte_signed ->
    fprintf ppf "HEAP8";
    0
  | Sixteen_unsigned ->
    fprintf ppf "HEAPU16";
    1
  | Sixteen_signed ->
    fprintf ppf "HEAP16";
    1
  | Thirtytwo_unsigned ->
    fprintf ppf "HEAPU32";
    2;
  | Thirtytwo_signed ->
    fprintf ppf "HEAP32";
    2;
  | Word ->
    fprintf ppf "HEAP32";
    2
  | Single ->
    fprintf ppf "HEAPF32";
    2
  | Double ->
    (* 64-bit-aligned 64-bit float *)
    fprintf ppf "HEAPF64";
    3
  | Double_u ->
    (* word-aligned 64-bit float *)
    fprintf ppf "HEAPF64";
    3) in
  fprintf ppf "[(%a)>>%d]" f reg shift

let print_live = ref false

let print_specific_operation printreg op ppf arg =
  let open Arch in
  match op with
  | _ -> fprintf ppf "<<dummy>>"

let operation op arg ppf res =
  if Array.length res > 0 then begin
    let r = res.(0) in
    (match r.typ with
    | Addr | Int ->
      fprintf ppf "%a = (" regs res;
    | Float ->
      fprintf ppf "%a = +(" regs res;
    )
  end;
  (match op with
  | Imove -> regs ppf arg
  | Ispill -> fprintf ppf "%a /*spill*/" regs arg
  | Ireload -> fprintf ppf "%a /*reload*/" regs arg
  | Iconst_int n -> fprintf ppf "%s|0" (Nativeint.to_string n)
  | Iconst_blockheader n -> fprintf ppf "/*blockheader*/%s" (Nativeint.to_string n)
  | Iconst_float f -> fprintf ppf "%F" f
  | Iconst_symbol s -> fprintf ppf "_%s" s
  | Icall_ind -> fprintf ppf "call %a" regs arg
  | Icall_imm lbl -> fprintf ppf "/*call*/%s(%a)" lbl regs arg
  | Itailcall_ind -> fprintf ppf "tailcall %a" regs arg
  | Itailcall_imm lbl -> fprintf ppf "tailcall \"%s\" %a" lbl regs arg
  | Iextcall(lbl, alloc) ->
    fprintf ppf "extcall \"%s\" %a%s" lbl regs arg
      (if alloc then "" else " (noalloc)")
  | Istackoffset n ->
    fprintf ppf "offset stack %i" n
  | Iload(chunk, addr) ->
    fprintf ppf "%a"
      (heap (Arch.print_addressing reg addr) arg)  chunk
  | Istore(chunk, addr, is_assign) ->
    fprintf ppf "%a = %a %s"
      (heap
         (Arch.print_addressing reg addr)
         (Array.sub arg 1 (Array.length arg - 1)))
      chunk
      reg arg.(0)
      (if is_assign then "/* assign */" else "/* init */")
  | Ialloc n -> fprintf ppf "alloc(%i)" n
  | Iintop(op) -> fprintf ppf "(%a|0)%s(%a|0)" reg arg.(0) (intop op) reg arg.(1)
  | Iintop_imm(op, n) -> fprintf ppf "(%a|0)%s(%i|0)" reg arg.(0) (intop op) n
  | Inegf -> fprintf ppf "- %a" reg arg.(0)
  | Iabsf -> fprintf ppf "abs(+ %a)" reg arg.(0)
  | Iaddf -> fprintf ppf "(+%a)+(+%a)" reg arg.(0) reg arg.(1)
  | Isubf -> fprintf ppf "(+%a)-(+%a)" reg arg.(0) reg arg.(1)
  | Imulf -> fprintf ppf "(+%a)*(+%a)" reg arg.(0) reg arg.(1)
  | Idivf -> fprintf ppf "(+%a)/(+%a)" reg arg.(0) reg arg.(1)
  | Ifloatofint -> fprintf ppf "floatofint %a" reg arg.(0)
  | Iintoffloat -> fprintf ppf "intoffloat %a" reg arg.(0)
  | Ispecific op ->
    print_specific_operation reg op ppf arg);
  if Array.length res > 0 then begin
    let r = res.(0) in
    (match r.typ with
    | Addr | Int ->
      fprintf ppf ")|0";
    | Float ->
      fprintf ppf ")";
    )
  end;
  fprintf ppf ";"

let rec instr ppf i =
  if !print_live then begin
    fprintf ppf "/*@[<1>{%a" regsetaddr i.live;
    if Array.length i.arg > 0 then fprintf ppf "@ +@ %a" regs i.arg;
    fprintf ppf "}@]*/@,";
  end;
  begin match i.desc with
  | Iend ->
    fprintf ppf "return 0|0;"
  | Iop op ->
      operation op i.arg ppf i.res
  | Ireturn ->
    fprintf ppf "return (%a)|0;" regs i.arg
  | Iifthenelse(tst, ifso, ifnot) ->
      fprintf ppf "@[<v 2>if (%a) {@,%a" (test tst) i.arg instr ifso;
      begin match ifnot.desc with
      | Iend -> ()
      | _ -> fprintf ppf "@;<0 -2>} else {@,%a" instr ifnot
      end;
      fprintf ppf "@;<0 -2>}@]"
  | Iswitch(index, cases) ->
      fprintf ppf "switch %a" reg i.arg.(0);
      for i = 0 to Array.length cases - 1 do
        fprintf ppf "@,@[<v 2>@[";
        for j = 0 to Array.length index - 1 do
          if index.(j) = i then fprintf ppf "case %i:@," j
        done;
        fprintf ppf "@]@,%a@]" instr cases.(i)
      done;
      fprintf ppf "@,endswitch"
  | Iloop(body) ->
      fprintf ppf "@[<v 2>loop@,%a@;<0 -2>endloop@]" instr body
  | Icatch(i, body, handler) ->
      fprintf
        ppf "@[<v 2>catch@,%a@;<0 -2>with(%d)@,%a@;<0 -2>endcatch@]"
        instr body i instr handler
  | Iexit i ->
      fprintf ppf "exit(%d)" i
  | Itrywith(body, handler) ->
      fprintf ppf "@[<v 2>try@,%a@;<0 -2>with@,%a@;<0 -2>endtry@]"
             instr body instr handler
  | Iraise k ->
      fprintf ppf "%s %a" (Lambda.raise_kind k) reg i.arg.(0)
  end;
  if not (Debuginfo.is_none i.dbg) then
    fprintf ppf "%s" (Debuginfo.to_string i.dbg);
  begin match i.next.desc with
    Iend ->
      fprintf ppf "@,return 0|0;"
  | _ -> fprintf ppf "@,%a" instr i.next
  end

let rec fun_vars f =
  let vars = ref Reg.Set.empty in
  instr_iter (fun i ->
    vars :=  Reg.add_set_array !vars i.res
  ) f.fun_body;
  vars := Reg.diff_set_array !vars f.fun_args;
  !vars


let fundecl ppf f =
  let args ppf v =
    let n = Array.length v in
    for i = 0 to n-1 do
      fprintf ppf "%a =" reg v.(i);
      (match v.(i).typ with
      | Addr | Int ->
        fprintf ppf "%a|0;//arg int@," reg v.(i)
      | Float ->
        fprintf ppf "+%a;//arg double@," reg v.(i)
      )
    done in
  let vars ppf vs =
    let n = ref false in
    fprintf ppf "var ";
    Reg.Set.iter (fun r ->
      match r.loc with
      | Stack _ -> ()
      | Unknown -> Misc.fatal_error "emit fundecl Unknown"
      | Reg _ ->
        if !n then
          fprintf ppf ", ";
        n := true;
        fprintf ppf "%a = " reg r;
        (match r.typ with
        | Addr | Int ->
          fprintf ppf "0"
        | Float ->
          fprintf ppf "0.0")) vs;
    fprintf ppf ";@," in
  let dbg =
    if Debuginfo.is_none f.fun_dbg then
      ""
    else
      " " ^ Debuginfo.to_string f.fun_dbg in
  fprintf ppf "@[<v 2>function %s(%a)%s{@,%a%a@,%a@]@.}"
    f.fun_name regs f.fun_args dbg
    args f.fun_args vars (fun_vars f)
    instr f.fun_body

let phase msg ppf f =
  fprintf ppf "*** %s@.%a@." msg fundecl f

let interference ppf r =
  let interf ppf =
   List.iter
    (fun r -> fprintf ppf "@ %a" reg r)
    r.interf in
  fprintf ppf "@[<2>%a:%t@]@." reg r interf

let interferences ppf () =
  fprintf ppf "*** Interferences@.";
  List.iter (interference ppf) (Reg.all_registers())

let preference ppf r =
  let prefs ppf =
    List.iter
      (fun (r, w) -> fprintf ppf "@ %a weight %i" reg r w)
      r.prefer in
  fprintf ppf "@[<2>%a: %t@]@." reg r prefs

let preferences ppf () =
  fprintf ppf "*** Preferences@.";
  List.iter (preference ppf) (Reg.all_registers())
