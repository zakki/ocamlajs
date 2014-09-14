(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* From lambda to assembly code *)

open Format
open Config
open Clflags
open Misc
open Cmm


type error = Assembler_error of string

exception Error of error

let liveness ppf phrase =
  Liveness.fundecl ppf phrase; phrase

let dump_if ppf flag message phrase =
  if !flag then Printmach.phase message ppf phrase

let pass_dump_if ppf flag message phrase =
  dump_if ppf flag message phrase; phrase

let pass_dump_linear_if ppf flag message phrase =
  if !flag then fprintf ppf "*** %s@.%a@." message Printlinear.fundecl phrase;
  phrase

let clambda_dump_if ppf ulambda =
  if !dump_clambda then Printclambda.clambda ppf ulambda; ulambda



module EmitJs = struct
  open Emitaux

  let begin_assembly() =
    (emit_string "function(){\n")

  let end_assembly() =
    (emit_string "}\n")

  let fundecl ppf fundecl =
    (* pass_dump_if ppf dump_live "Liveness analysis" fundecl; *)
    let ppf = Format.formatter_of_out_channel !Emitaux.output_channel in
    Js.phase "" ppf fundecl;
    (* let dump_if ppf flag message phrase = *)
    (* let ppf = Format.formatter_of_out_channel !Emitaux.output_channel in *)
    (* fprintf ppf "*** %s@.%a@." "" fundecl *)
    (* Emitaux.output_channel *)
    (* Printmach.phase message ppf phrase *)
    Format.print_flush ()

  (* Emission of data *)
  let symbol_prefix = "_"

  let emit_symbol s =
    emit_string symbol_prefix; Emitaux.emit_symbol '$' s

  let label_prefix = "L"

  let emit_label lbl =
    emit_string label_prefix; emit_int lbl

  let emit_data_label lbl =
    emit_string label_prefix; emit_string "d"; emit_int lbl

  let word_dir = ".word"
  let skip_dir = ".space"
  let use_ascii_dir = true

  let emit_align =
    (fun n -> (emit_string "	.align	"; emit_int n; emit_char '\n'))

  let emit_nativeint n =
    for i = 0 to 3 do
      let b = Nativeint.logand (Nativeint.shift_right_logical n (i * 8)) 0xFFn in
      (* let b = (Nativeint.shift_right_logical n i) in *)
      (* emit_printf "'%d:%x'" i (Nativeint.to_int b); *)
      emit_int (Nativeint.to_int b);
      emit_string ", "
    done

  let emit_float64 x =
    let lo = Int64.logand x 0xFFFF_FFFFL
    and hi = Int64.shift_right_logical x 32 in
    (* emit_string "/*"; *)
    (* emit_int32 (Int64.to_int32 lo); *)
    (* emit_string "/"; *)
    (* emit_int32 (Int64.to_int32 hi); *)
    (* emit_string "*/"; *)
    emit_nativeint (Int64.to_nativeint lo);
    emit_nativeint (Int64.to_nativeint hi)

  let emit_float32 x =
    emit_nativeint (Nativeint.of_int32 x)


  let emit_item = function
    | Cglobal_symbol s ->
      (emit_string "	.globl	"; emit_symbol s; emit_char '\n');
    | Cdefine_symbol s ->
      (emit_symbol s; emit_string ":\n")
    | Cdefine_label lbl ->
      (emit_data_label lbl; emit_string ":\n")
    | Cint8 n ->
      (emit_string "/*.byte*/"; emit_int n; emit_char '\n')
    | Cint16 n ->
      (emit_char '	'; emit_string word_dir; emit_char '	'; emit_int n; emit_char '\n')
    | Cint32 n ->
      (emit_string "/*int32*/"; emit_nativeint n; emit_char '\n')
    | Cint n ->
      (emit_string "/*int*/"; emit_nativeint n; emit_char '\n')
    | Csingle f ->
      (emit_printf "/*single %f*/" f; emit_float32 (Int32.bits_of_float f));
    | Cdouble f ->
      (emit_printf "/*double %F*/" f; emit_float64 (Int64.bits_of_float f))
    | Csymbol_address s ->
      (emit_string "/*.symbol address*/"; emit_symbol s; emit_char '\n')
    | Clabel_address lbl ->
      (emit_string "/*.label address*/"; emit_data_label lbl; emit_char '\n')
    | Cstring s ->
      if use_ascii_dir
      then emit_string_directive "	.ascii	" s
      else emit_bytes_directive  "	.byte	" s
    | Cskip n ->
      if n > 0 then (emit_string_directive "/*skip*/"; emit_string skip_dir; emit_char '	'; emit_int n; emit_char '\n')
    | Calign n ->
      emit_align n

  let data l =
    (* let ppf = Format.formatter_of_out_channel !Emitaux.output_channel in *)
    (* (emit_string "/* data\n"); *)
    List.iter emit_item l;
    (* (emit_string "data */\n"); *)
    (* Format.print_flush () *)
    ()
end

let rec regalloc ppf round fd =
  if round > 50 then
    fatal_error(fd.Mach.fun_name ^
                ": function too complex, cannot complete register allocation");
  dump_if ppf dump_live "Liveness analysis" fd;
  Interf.build_graph fd;
  if !dump_interf then Printmach.interferences ppf ();
  if !dump_prefer then Printmach.preferences ppf ();
  Coloring.allocate_registers();
  dump_if ppf dump_regalloc "After register allocation" fd;
  let (newfd, redo_regalloc) = Reload.fundecl fd in
  dump_if ppf dump_reload "After insertion of reloading code" newfd;
  if redo_regalloc then begin
    Reg.reinit(); Liveness.fundecl ppf newfd; regalloc ppf (round + 1) newfd
  end else newfd

let (++) x f = f x

let compile_fundecl (ppf : formatter) fd_cmm =
  Proc.init ();
  Reg.reset();
  fd_cmm
  ++ Selection.fundecl
  ++ pass_dump_if ppf dump_selection "After instruction selection"
  ++ Comballoc.fundecl
  ++ pass_dump_if ppf dump_combine "After allocation combining"
  ++ CSE.fundecl
  ++ pass_dump_if ppf dump_cse "After CSE"
  ++ liveness ppf
  ++ Deadcode.fundecl
  ++ pass_dump_if ppf dump_live "Liveness analysis"
  ++ Spill.fundecl
  ++ liveness ppf
  ++ pass_dump_if ppf dump_spill "After spilling"
  ++ Split.fundecl
  ++ pass_dump_if ppf dump_split "After live range splitting"
  ++ liveness ppf
  ++ regalloc ppf 1
  (* ++ Linearize.fundecl *)
  (* ++ pass_dump_linear_if ppf dump_linear "Linearized code" *)
  (* ++ Scheduling.fundecl *)
  (* ++ pass_dump_linear_if ppf dump_scheduling "After instruction scheduling" *)
  ++ EmitJs.fundecl ppf

let compile_phrase ppf p =
  if !dump_cmm then fprintf ppf "%a@." Printcmm.phrase p;
  match p with
  | Cfunction fd -> compile_fundecl ppf fd
  | Cdata dl -> EmitJs.data dl


(* For the native toplevel: generates generic functions unless
   they are already available in the process *)
let compile_genfuns ppf f =
  List.iter
    (function
       | (Cfunction {fun_name = name}) as ph when f name ->
           compile_phrase ppf ph
       | _ -> ())
    (Cmmgen.generic_functions true [Compilenv.current_unit_infos ()])

let compile_implementation ?toplevel prefixname ppf (size, lam) =
  let asmfile =
    (* if !keep_asm_file *)
    (* then prefixname ^ ext_asm *)
    (* else Filename.temp_file "camlasm" ext_asm in *)
    (prefixname ^ ext_obj) in
  let oc = open_out asmfile in
  begin try
    Emitaux.output_channel := oc;
    EmitJs.begin_assembly();
    Closure.intro size lam
    ++ clambda_dump_if ppf
    ++ Cmmgen.compunit size
    ++ List.iter (compile_phrase ppf) ++ (fun () -> ());
    (match toplevel with None -> () | Some f -> compile_genfuns ppf f);

    (* We add explicit references to external primitive symbols.  This
       is to ensure that the object files that define these symbols,
       when part of a C library, won't be discarded by the linker.
       This is important if a module that uses such a symbol is later
       dynlinked. *)

    compile_phrase ppf
      (Cmmgen.reference_symbols
         (List.filter (fun s -> s <> "" && s.[0] <> '%')
            (List.map Primitive.native_name !Translmod.primitive_declarations))
      );

    EmitJs.end_assembly();
    close_out oc
  with x ->
    close_out oc;
    if !keep_asm_file then () else remove_file asmfile;
    raise x
  end;
  (* if Proc.assemble_file asmfile (prefixname ^ ext_obj) <> 0 *)
  (* then raise(Error(Assembler_error asmfile)); *)
  (* if !keep_asm_file then () else remove_file asmfile *)
  ()

(* Error report *)

let report_error ppf = function
  | Assembler_error file ->
      fprintf ppf "Assembler error, input left in file %a"
        Location.print_filename file

let () =
  Location.register_error_of_exn
    (function
      | Error err -> Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )
