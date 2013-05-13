(* Copyright (c) 2012. Ben Ferrell, Kenneth Miller, 
 *  Matthew Pettersson, Justin Sahs, and Brett Webster.
 *
 *  This file is part of REINS.
 *
 *  This file is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License as
 *  published by the Free Software Foundation; either version 2 of
 *  the License, or (at your option) any later version.
 *)

Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Bits.
Require Import PETraversal.
Require Import ReinsVerifierDFA.
Require Import Parser.
Require Import X86Syntax.
Require Import Decode.

Import X86_PARSER_ARG.
Import X86_PARSER.
Import X86_BASE_PARSER.



Notation " [ x , .. , y ] " := (List.cons x .. (List.cons y List.nil) ..).
Open Scope nat_scope.

Set Printing Depth 10000.

Time Compute (make_dfa reinsjmp_nonIAT_mask).
Time Compute (make_dfa reinsjmp_IAT_JMP_or_RET_mask).
Time Compute (make_dfa reinsjmp_IAT_CALL_p).
Time Compute (make_dfa dir_cflow_parser).
Time Compute (make_dfa non_cflow_parser).
