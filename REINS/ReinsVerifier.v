(* If the following hold,
	All executable code resides in low memory
	All exported symbols target low memory areas
	No disassembled instructions spans a chunk boundary
	static branches target low memory chunk boundaries
	all computed jumps that do not reference the IAT are 
		immediately preceded by and-masking 
		instruction from Table 1 in the same chunk 
	Computed jumps that read the IAT access a properly 
		aligned IAT entry, and are preceded by an 
		and-mask of the return address (call 
		instructions must end on a chunk boundary 
		rather than requiring a mask, since they push
		their own return address 
	There are no trap instructions; int or syscall 
THEN:
	These properties ensure that any unaligned instruction sequences
concealed within untrusted, executable sections are not reachable
at runtime.
*)


(* Actual algorithm that tests an imaginary binary - image this in 
the light of FastVerifier *)


(*------------------------ COPIED AND PASTED FROM FastVerifier ----------------- *)

(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)


Require Import Coqlib.
Require Import Parser.
Require Import List.
Require Import Bits.
Require Import Decode.
Require Import X86Syntax.
Require Import Int32.
Require Import ReinsVerifierDFA.
Require Import PEFormat.
Require Import PETraversal.

Import X86_PARSER_ARG.
Import X86_PARSER.
Import X86_BASE_PARSER.

Require Coq.MSets.MSetAVL.
Require Coq.Structures.OrdersAlt.
Require Coq.MSets.MSetFacts.
Module New_Int32_OT := (Coq.Structures.OrdersAlt.Update_OT Int32_OT).
Module Int32Set := Coq.MSets.MSetAVL.Make New_Int32_OT.

Definition n_shift_add (b: bool) (x: nat) :=
  (if b then 2 * x + 1 else 2 * x)%nat.

Open Scope Z_scope.

Fixpoint n_of_bits (n: nat) (f: Z -> bool) {struct n}: nat :=
  match n with
  | O => O
  | S m => n_shift_add (f 0) (n_of_bits m (fun i => f (i + 1)))
  end.

(* Maybe tokens as nats isn't best... *)
Definition byte2token (b: int8) : token_id := Zabs_nat (Word.unsigned b).
Definition token2byte (t: token_id) : int8 := Word.repr (Z_of_nat t).

Section BUILT_DFAS.

  (* In this section we will just assume the DFAs are all built;
     that is, non_cflow_dfa should be the result of "make_dfa non_cflow_parser" and
     similarly for dir_cflow_dfa and nacljmp_dfa *)
  Variable non_cflow_dfa : DFA.
  Variable dir_cflow_dfa : DFA.
  Variable reinsjmp_nonIAT_dfa : DFA.
  Variable reinsjmp_IAT_or_RET_dfa : DFA.
  Variable reinsjmp_IAT_CALL_dfa : DFA.
  Variable reinsjmp_nonIAT_mask : parser (pair_t instruction_t instruction_t).
  Variable reinsjmp_IAT_or_RET_mask : parser (pair_t instruction_t instruction_t).
  Variable reinsjmp_IAT_CALL_p : parser instruction_t.

  (* G.T.: may be a good idea to parametrize the DFA w.r.t. the ChunkSize;
     Google's verifier allows it either to be 16 or 32.
   Parameters logChunkSize:nat.
   Hypothesis logChunkSize_range : (0 < logChunkSize <= Word.wordsize 31)%nat.
  *)

  Fixpoint parseloop (ps:X86_PARSER.instParserState) (bytes:list int8) : 
    option ((prefix * instr) * list int8) := 
    match bytes with 
      | nil => None
      | b::bs => match X86_PARSER.parse_byte ps b with 
                   | (ps',nil) => parseloop ps' bs
                   | (_, v::_) => Some (v,bs)
                 end
    end.

  Inductive jumptype : Set :=
  | JMP_t : jumptype
  | JCC_t : jumptype
  | CALL_t: jumptype.

  Definition extract_disp_and_type bytes : option (int32 * jumptype) := 
    match (parseloop Decode.X86_PARSER.initial_parser_state bytes) with
      | Some ((_, JMP true false (Imm_op disp) None), _) => Some (disp, JMP_t)
      | Some ((_, Jcc ct disp), _) => Some (disp, JCC_t)
      | Some ((_, CALL true false (Imm_op disp) None), _) => Some (disp, CALL_t)
      | _ => None
    end.

  (* parseloop, X86_PARSER.parse_byte, and X86_PARSER.instParserState all have a
     too-restrictive type, expecting the underlying parser to parse a prefix and
     an instruction. For our reinsjmp parsers, we are parsing pairs of instructions,
     so we redefine these three functions with that in mind *)

  Record instParserState' := mkPS' {
      inst_ctxt' : ctxt_t;
      inst_regexp' : regexp (pair_t instruction_t instruction_t);
      inst_regexp_wf' : wf_regexp inst_ctxt' inst_regexp'
  }.

  Definition parse_byte' (ps:instParserState') (b:int8) : 
    instParserState' * list (instr * instr) := 
    let cs := byte_explode b in 
    let r' := deriv_parse' (inst_regexp' ps) cs in
    let wf' := wf_derivs (inst_ctxt' ps) cs (inst_regexp' ps) (inst_regexp_wf' ps) in
      (mkPS' (inst_ctxt' ps) r' wf', apply_null (inst_ctxt' ps) r' wf').

  Fixpoint parseloop' (ps:instParserState') (bytes:list int8) : 
    option ((instr * instr) * list int8) := 
    match bytes with 
      | nil => None
      | b::bs => match parse_byte' ps b with 
                   | (ps',nil) => parseloop' ps' bs
                   | (_, v::_) => Some (v,bs)
                 end
    end.


  Definition extract_IAT_jmp_dest bytes : option (option address) :=
    let regexp_pair := parser2regexp reinsjmp_IAT_or_RET_mask in
    let ips := mkPS' (snd regexp_pair) (fst regexp_pair) (p2r_wf reinsjmp_IAT_or_RET_mask _) in
    match (parseloop' ips bytes) with
    | Some ((_, JMP true true (Address_op addr) None), _) => Some (Some addr)
    | Some ((_, RET _ _), _) => Some None
    | _ => None
    end.

  (* parseloop, X86_PARSER.parse_byte, and X86_PARSER.instParserState all have a
     too-restrictive type, expecting the underlying parser to parse a prefix and
     an instruction. For our IAT call extraction, we want a single instruction. *)

  Record instParserState'' := mkPS'' {
      inst_ctxt'' : ctxt_t;
      inst_regexp'' : regexp instruction_t;
      inst_regexp_wf'' : wf_regexp inst_ctxt'' inst_regexp''
  }.

  Definition parse_byte'' (ps:instParserState'') (b:int8) : 
    instParserState'' * list instr := 
    let cs := byte_explode b in 
    let r' := deriv_parse' (inst_regexp'' ps) cs in
    let wf' := wf_derivs (inst_ctxt'' ps) cs (inst_regexp'' ps) (inst_regexp_wf'' ps) in
      (mkPS'' (inst_ctxt'' ps) r' wf', apply_null (inst_ctxt'' ps) r' wf').

  Fixpoint parseloop'' (ps:instParserState'') (bytes:list int8) : 
    option (instr * list int8) := 
    match bytes with 
      | nil => None
      | b::bs => match parse_byte'' ps b with 
                   | (ps',nil) => parseloop'' ps' bs
                   | (_, v::_) => Some (v,bs)
                 end
    end.

  Definition extract_IAT_call_dest bytes : option address :=
    let regexp_pair := parser2regexp (reinsjmp_IAT_CALL_p) in
    let ips := mkPS'' (snd regexp_pair) (fst regexp_pair) (p2r_wf (reinsjmp_IAT_CALL_p) _) in
    match (parseloop'' ips bytes) with
    | Some (CALL true true (Address_op addr) None, _) => Some addr
    | _ => None
    end.

  Definition is_nonIAT_call bytes : bool :=
    let regexp_pair := parser2regexp (reinsjmp_nonIAT_mask) in
    let ips := mkPS' (snd regexp_pair) (fst regexp_pair) (p2r_wf (reinsjmp_nonIAT_mask) _) in
    match (parseloop' ips bytes) with
    | Some ((_, CALL _ _ _ _), _) => true
    | _ => false
    end.


  (* Note: it's important to specify the type of tokens as "list token_id", not
     "list nat", even though token_id is defined to be nat. If a proof environment
     has one value of type "list token_id" and the other of type "list nat", 
     proof scripts such as rewrite or omega may fail since token_id needs to
     be unfolded. *)

  Fixpoint process_buffer_aux (loc: int32) (n: nat) (tokens:list (list token_id))
    (curr_res: Int32Set.t * Int32Set.t * Int32Set.t * Int32Set.t) :=
    match n with
    | O => None 
    | S m =>
      match curr_res with
      | (start_instrs, check_list, iat_check_list, call_check_list) =>
        match tokens with
        | nil => Some curr_res
        | chunk::rest => (* There are left over bytes in the buffer *)
          match chunk with
          | nil => process_buffer_aux loc m rest curr_res
          | _ =>
            match
             (dfa_recognize 256 non_cflow_dfa              chunk,
              dfa_recognize 256 dir_cflow_dfa              chunk,
              dfa_recognize 256 reinsjmp_nonIAT_dfa        chunk,
              dfa_recognize 256 reinsjmp_IAT_or_RET_dfa    chunk,
              dfa_recognize 256 reinsjmp_IAT_CALL_dfa      chunk) with

            (* Non-Control-Flow Only *)
            | (Some (len, remaining), None, None, None, None) => 
              process_buffer_aux (loc +32_n len) m (remaining::rest)
              (Int32Set.add loc start_instrs, check_list, iat_check_list, call_check_list)

            (* Direct Control-Flow (Only) *)
            | (None, Some (len, remaining), None, None, None) => 
              match extract_disp_and_type (List.map token2byte (firstn len chunk)) with
                | Some (disp, JMP_t)
                | Some (disp, JCC_t) => 
                  process_buffer_aux (loc +32_n len) m (remaining::rest)
                  (Int32Set.add loc start_instrs,
                   Int32Set.add (loc +32_n len +32 disp) check_list,
                   iat_check_list,
                   call_check_list)
                | Some (disp, CALL_t) =>
                  process_buffer_aux (loc +32_n len) m (remaining::rest)
                  (Int32Set.add loc start_instrs,
                   Int32Set.add (loc +32_n len +32 disp) check_list,
                   iat_check_list,
                   Int32Set.add (loc +32_n len) call_check_list)
                | _ => None
              end

            (* Non-IAT Indirect Control Flow (with Non-Control-Flow mask) *)
            | (Some res0, None, Some (len, remaining), None, None) => 
              process_buffer_aux (loc +32_n len) m (remaining::rest)
              (if is_nonIAT_call (List.map token2byte (firstn len chunk)) then
                  (Int32Set.add loc start_instrs, check_list, iat_check_list,
                   Int32Set.add (loc +32_n len) call_check_list)
              else
                  (Int32Set.add loc start_instrs, check_list, iat_check_list, call_check_list))

            (* IAT Indirect Jump or Retrun (with Non-Control-Flow mask) *)
            | (Some res0, None, None, Some (len, remaining), None) =>
              match extract_IAT_jmp_dest (List.map token2byte (firstn len chunk)) with
              (* Not an actual IAT jmp or RET (shouldn't happen) *)
              | None => None
              (* IAT jmp *)
              | Some (Some indir) =>
                process_buffer_aux (loc +32_n len) m (remaining::rest)
                (Int32Set.add loc start_instrs, check_list,
                 Int32Set.add (addrDisp indir) iat_check_list,
                 call_check_list)
              (* RET *)
              | Some None =>
                process_buffer_aux (loc +32_n len) m (remaining::rest)
                (Int32Set.add loc start_instrs, check_list, iat_check_list, call_check_list)
              end

            (* IAT Call Only (No Mask necessary) *)
            | (None, None, None, None, Some (len, remaining)) =>
              match extract_IAT_call_dest (List.map token2byte (firstn len chunk)) with
              (* Not actually an IAT call (shouldn't happen) *)
              | None => None
              (* IAT Call *)
              | Some indir =>
                process_buffer_aux (loc +32_n len) m (remaining::rest)
                (Int32Set.add loc start_instrs, check_list,
                Int32Set.add (addrDisp indir) iat_check_list,
                Int32Set.add (loc +32_n len) call_check_list)
              end

            (* None of the DFAs matched or too many DFAs matched *)
            | _ => None
            end
          end
        end
      end
    end.

  (* The idea here is, given a list of int8s representing the code,
     we call process_buffer_aux with n := length of the (flattened)
     list plus one for each sub-list; since each sub-list incurs one
     recursive call, and each instruction is at least one byte long,
     this should be enough calls to process_buffer_aux to process
     everything in the buffer, without us having to worry about
     termination proofs
     Note: one way to avoid the n is would be to show each dfa consumes
     at least one byte.
     *)
  Definition process_buffer (buffer: list (list int8)) :=
    process_buffer_aux
      (Word.repr 0)
      ((List.fold_left (fun a b => a + b)%nat (List.map (fun l => length l + 1)%nat buffer) 0%nat) + 1)
      (List.map (List.map byte2token) buffer) 
      (Int32Set.empty, Int32Set.empty, Int32Set.empty, Int32Set.empty).

  Definition aligned_bool (a:int32):bool := 
    Zeq_bool (Zmod (unsigned a) chunkSize) 0.
  Definition aligned (a:int32) := aligned_bool a = true.

  Require Import Recdef.
  Function checkAligned_aux (p: Int32Set.t * Z * nat) {measure snd p}
    : bool :=
  match p with
    | (_, 0%nat) => true
    | ((startAddrs, next), len) =>
      (Int32Set.mem (repr next) startAddrs &&
       checkAligned_aux (startAddrs, (next + chunkSize), 
                            (len - Zabs_nat chunkSize)%nat))
  end.
  intros. simpl. omega.
  Defined.                          

  (* checking that all aligned addresses between 0 and len is in startAddrs *)
  Definition checkAligned (startAddrs:Int32Set.t) (len: nat) :bool :=
    checkAligned_aux (startAddrs, 0, len).

  (* checking all jump targets are either in startAddrs or are aligned addresses *)
  Definition checkJmpTargets (jmpTargets: Int32Set.t) := 
    Int32Set.for_all aligned_bool jmpTargets.
      
  Definition checkIATAddresses (iat : IATBounds) (iatAddresses : Int32Set.t) : bool :=
    match iat with
    | iatbounds (start, size) =>
        let checkAddress addr :=
	     andb
                (andb (lequ start addr) (lequ addr (start +32 size)))
                (eq (modu (addr -32 start) (repr (Z_of_nat (wordsize 31)))) (repr 0)) in
          Int32Set.for_all checkAddress iatAddresses
    end.

  Definition checkCallAlignment (callAddrs : Int32Set.t) : bool :=
    Int32Set.for_all aligned_bool callAddrs.

  (* A section is in low memory if its end (start + length) is <= lowMemCutoff,
     and the addition doesn't overflow *)
  Definition checkExecSectionLowMemory (start : int32) (length : int32) : bool :=
    andb (int32_lequ_bool (start +32 length) (@repr 31 lowMemCutoff)) (checkNoOverflow start length).


  (* Given an executable section, represented as a list of bytes,
  *  check that the section obeys policy *)
  Definition checkExecSection (iat : IATBounds) (section: int32 * int32 * list (list int8)) : (bool * Int32Set.t) :=
    match section with
    | (start,len,buffer) =>
        if checkExecSectionLowMemory start len then
          match process_buffer buffer with
          | None => (false, Int32Set.empty)
          | Some (start_addrs, check_addrs, iat_check_addrs, call_check_addrs) => 
              (andb (andb (andb (checkAligned start_addrs (length buffer))
                (checkJmpTargets check_addrs)) (checkIATAddresses iat iat_check_addrs))
                (checkCallAlignment call_check_addrs),
              start_addrs)
          end
        else
          (false,Int32Set.empty)
    end.

  (* Given a PE file, check the following properties for each executable section:
   * - All executable sections reside in low memory
   * - All exported symbols target low memory chunk boundaries (checkExports)
   * - No disassembled instruction spans a chunk boundary (checkAligned)
   * - Static branches target low memory chunk boundaries (checkJmpTargets)
   * - Non-IAT computed jumps are masked (reinsjmp_nonIAT_mask)
   * - IAT computed jumps have return addr masked and actually target the iat
   *     (reinsjmp_IAT_or_RET_mask + checkIATAddresses)
   * - Call instructions end on a chunk bounary
   * - No trap instructions (will not parse)
   *)
  Definition checkProgram (data : list (list int8)) : (bool * Int32Set.t) :=
    let exec := getExecutableSections data in
    let iat := getIATBounds data in
    if checkExports data safeMask then
      let exec_check := List.map (checkExecSection iat) exec in
      let pass := List.fold_left andb (List.map (@fst _ _) exec_check) true in
      let addrs :=
        if pass then
          List.fold_left Int32Set.union (List.map (@snd _ _) exec_check) Int32Set.empty
        else
          Int32Set.empty
      in
        (pass,addrs)
    else
      (false,Int32Set.empty).


End BUILT_DFAS.

Require Import CompiledDFAs.

Definition checkProgram' (data : list (list int8)) : (bool * Int32Set.t) :=
    checkProgram
      non_cflow_dfa
      dir_cflow_dfa
      reinsjmp_nonIAT_dfa
      reinsjmp_IAT_JMP_or_RET_dfa
      reinsjmp_IAT_CALL_dfa
      reinsjmp_nonIAT_mask
      reinsjmp_IAT_JMP_or_RET_mask
      reinsjmp_IAT_CALL_p
      data.

Extraction "reinsverif.ml" checkProgram'.
