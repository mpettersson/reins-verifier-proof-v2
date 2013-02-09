(* Copyright (c) 2012. Ben Ferrell, Kenneth Miller, 
 *  Matthew Pettersson, Justin Sahs, and Brett Webster.
 *
 *  This file is part of REINS.
 *
 *  This file is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License as
 *  published by the Free Software Foundation; either version 2 of
 *  the License, or (at your option) any later version.*)

open Reinsverif;;

let read_byte (file : in_channel) : int option =
  try (Some (input_byte file)) with
    | End_of_file -> None;;

let rec read_bytes (n : int) (file : in_channel) : int list =
  match n with
  | 0 -> []
  | _ -> match (read_byte file) with
      | Some byte -> byte :: read_bytes (n-1) file
      | None -> [];;

(* This version reads the file 'backwards', because all the io is
 * deferred until the recursion resolves itself (i.e. the base case
 * is the first read... I have no idea why... *)
(*let rec read_bin (n : int) (file : in_channel) : (int list) list =
  print_string "reading...\n";
  if (n-3072) <= 0 then
    [read_bytes 3072 file]
  else
    (read_bytes 3072 file) :: read_bin (n-3072) file;;*)

let read_bin (n: int) (file : in_channel) : (int list) list =
  let s = if n mod 3072 == 0 then
            n / 3072
          else
            (n / 3072) + 1
  in
  let l = Array.make s [] in
  for i=0 to (s-1) do
    l.(i) <- read_bytes 3072 file;
  done;
  Array.to_list l;;


let rec print_list' (l : int list) =
  match l with
    | [] -> ()
    | x :: xs -> print_int x; print_string " "; print_list' xs;;

let print_list (l : int list) =
  print_string "["; print_list' l; print_string "]\n";;

let rec print_matr' (l : (int list) list) =
  match l with
    | [] -> ()
    | x :: xs -> print_list x; print_matr' xs;;

let print_matr (l : (int list) list) =
  print_string "["; print_matr' l; print_string "]\n";;

(*let print_dos d =
  print_int (word_to_nat (e_magic     d)); print_newline ();
  print_int (word_to_nat (e_cblp      d)); print_newline ();
  print_int (word_to_nat (e_cp        d)); print_newline ();
  print_int (word_to_nat (e_crlc      d)); print_newline ();
  print_int (word_to_nat (e_cparhdr   d)); print_newline ();
  print_int (word_to_nat (e_minalloc  d)); print_newline ();
  print_int (word_to_nat (e_maxalloc  d)); print_newline ();
  print_int (word_to_nat (e_ss        d)); print_newline ();
  print_int (word_to_nat (e_sp        d)); print_newline ();
  print_int (word_to_nat (e_csum      d)); print_newline ();
  print_int (word_to_nat (e_ip        d)); print_newline ();
  print_int (word_to_nat (e_cs        d)); print_newline ();
  print_int (word_to_nat (e_lfarlc    d)); print_newline ();
  print_int (word_to_nat (e_ovno      d)); print_newline ();
  print_list (List.map word_to_nat (vtolist 4 (e_res d)));
  print_int (word_to_nat (e_oemid     d)); print_newline ();
  print_int (word_to_nat (e_oeminfo   d)); print_newline ();
  print_list (List.map word_to_nat (vtolist 10 (e_res2 d)));
  print_int (ptr_to_nat  (e_lfanew    d)); print_newline ();;*)


let main () =
  let file = open_in Sys.argv.(1) in
  let bin = read_bin (in_channel_length file) file in
  let zs = List.map (List.map z_of_nat) bin in
  let data = List.map (List.map (Word.repr 8)) zs in
    match checkProgram' data with
    | (b,_) -> if b then
                 print_string "Pass\n"
               else
                 print_string "Fail\n";;


main ();;
