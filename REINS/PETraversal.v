(* Copyright (c) 2012. Ben Ferrell, Kenneth Miller, 
 *  Matthew Pettersson, Justin Sahs, and Brett Webster.
 *
 *  This file is part of REINS.
 *
 *  This file is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License as
 *  published by the Free Software Foundation; either version 2 of
 *  the License, or (at your option) any later version.*)


(* TODO need to find out the size of LPBYTE in order to correctly observe 
 * Image Thunk Data structures and others... *)

Require Import Coq.Lists.List.
Require Import PEFormat.
Require Import Bits.
Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinPos.
Require Import Coq.ZArith.Zdiv.

Open Scope vector_scope.

Definition block_size : Z := Z_of_nat 3072.

Definition Z_to_nat (z : Z) : nat :=
    match z with
        | Z0 => 0
        | Zpos p => nat_of_P p
        | Zneg p => 0
    end.

Definition word_to_nat (w : WORD) : nat :=
    Z_to_nat (Word.unsigned w).

Definition dword_to_nat (w : DWORD) : nat :=
    Z_to_nat (Word.unsigned w).

Definition ptr_to_nat {A} (p : Ptr A) : nat :=
    match p with
        | ptr d _ => dword_to_nat d
    end.

Definition word_to_Z (w : WORD) : Z :=
    Word.unsigned w.

Definition dword_to_Z (w : DWORD) : Z :=
    Word.unsigned w.

Definition ptr_to_Z {A} (p : Ptr A) : Z :=
    match p with
        | ptr d _ => dword_to_Z d
    end.

Definition getChunk (data : list (list int8)) (z : Z) : list int8 :=
   nth (Z_to_nat (Zdiv z block_size)) data (cons (Word.repr 0) nil).

(* use to cast int8 as int16 *)
Definition int8_to_int16 (x : int8) : int16 :=
   Word.repr(Word.unsigned x)
.

(* takes two int16 (cast from int8) and turns into WORD *)
Definition bytes_to_word (msb : int16) (lsb : int16) : WORD :=
   Word.add (Word.mul msb (Word.repr 256)) lsb
.

(* 
 * In REINS, we initially used a list of bytes as data 
 * and naturals to reason about the data, for example 
 * the old definition of parseByte was:
 *
 * Definition parseByte (data : list BYTE) (n : nat) : BYTE :=
 *     nth n data (Word.repr 0).
 *
 * However, was irratatingly slow and prompted us to changed the 
 * pile of bytes structre from a list of bytes to a list of list
 * of bytes and use Z for indexing.  
 *)
Definition parseByte (data : list(list BYTE)) (z : Z) : BYTE :=
   let chunk := getChunk data z in
   let n := Z_to_nat (Zmod z block_size) in
   nth n chunk (Word.repr 0)
.

(* takes list of bytes and idx and returns a WORD *)
Definition parseWord (data : list (list BYTE)) (z : Z) : WORD := 
   let chunk := getChunk data z in
   let n := Z_to_nat (Zmod z block_size) in
   bytes_to_word (int8_to_int16 (nth (S n) chunk (Word.repr 0))) 
                 (int8_to_int16 (nth n chunk (Word.repr 0)))  
.

(* use to cast int8 as int32 *)
Definition int8_to_int32 (x : int8) : int32 :=
   Word.repr(Word.unsigned x)
.

(* takes four int32 (cast from int8) and turns into a DWORD *)
Definition bytes_to_dword (w : int32) (x : int32) 
                          (y : int32) (z : int32) 
                          : DWORD :=
   Word.add
      (Word.add (Word.mul w (Word.repr 16777216)) 
                (Word.mul x (Word.repr 65536)))
      (Word.add (Word.mul y (Word.repr 256)) z)
.

(* returns DWORD at idx *)
Definition parseDoubleWord (data : list (list BYTE)) (z : Z) : DWORD :=
   let chunk := getChunk data z in
   let n := Z_to_nat (Zmod z block_size) in
   bytes_to_dword (int8_to_int32 (nth (S (S (S n))) chunk (Word.repr 0)))
                  (int8_to_int32 (nth (S (S n)) chunk (Word.repr 0)))
                  (int8_to_int32 (nth (S n) chunk (Word.repr 0)))
                  (int8_to_int32 (nth n chunk (Word.repr 0)))
.

Definition parsePtr (data : list (list BYTE)) (z : Z) {A : Type} : Ptr A :=
   ptr (parseDoubleWord data z) A
.

Fixpoint parseVector {A : Type} (parse : list (list BYTE) -> Z -> A)
                                (data : list(list BYTE))
                                (size : Z)
                                (n : Z)
                                (count : nat)
                                 : vector count A :=
    match count with
        | 0 => []
        | S count' => (parse data n) :: (parseVector parse data size (n + size) count')
    end.

Fixpoint copySection (data : list (list BYTE)) (start : Z) (size : Z) (n : nat) : list (list BYTE) :=
    match n with
        | O => cons (vtolist (parseVector parseByte data 1 start (Z_to_nat size))) nil
        | S n' => cons (vtolist (parseVector parseByte data 1 start (Z_to_nat block_size)))
             (copySection data (start+block_size) (size - block_size) n')
    end.

Definition parseImageDosHeader (data : list (list BYTE)) : _IMAGE_DOS_HEADER :=
 mkImageDosHeader 
   (parseWord data 0)       (* e_magic *)
   (parseWord data 2)       (* e_cblp *)
   (parseWord data 4)       (* e_cp *)
   (parseWord data 6)       (* e_crlc *)
   (parseWord data 8)       (* e_cparhdr *)
   (parseWord data 10)      (* e_minalloc *)
   (parseWord data 12)      (* e_maxalloc *)
   (parseWord data 14)      (* e_ss *)
   (parseWord data 16)      (* e_sp *)
   (parseWord data 18)      (* e_csum *)
   (parseWord data 20)      (* e_ip *)
   (parseWord data 22)      (* e_cs *)
   (parseWord data 24)      (* e_lfarlc *)
   (parseWord data 26)      (* e_ovno *)
   ((parseWord data 28)::
   (parseWord data 30)::
   (parseWord data 32)::
   (parseWord data 34)::[]) (* e_res *)
   (parseWord data 36)      (* e_oemid *)
   (parseWord data 38)      (* e_oeminfo *)
   ((parseWord data 40)::
   (parseWord data 42)::
   (parseWord data 44)::
   (parseWord data 46)::
   (parseWord data 48)::
   (parseWord data 50)::
   (parseWord data 52)::
   (parseWord data 54)::
   (parseWord data 56)::
   (parseWord data 58)::[]) (* e_res2 *)
   (parsePtr data 60)       (* e_lfanew *)
.

Definition parseImageFileHeader (data : list (list BYTE)) (n : Z) : _IMAGE_FILE_HEADER :=
    mkImageFileHeader
      (parseWord data n) 		    (* Machine *)
      (parseWord data (n+2)) 		(* NumberOfSections *)
      (parseDoubleWord data (n+4)) 	(* TimeDateStamp_IFH *)
      (parseDoubleWord data (n+8)) 	(* PointerToSymbolTable *)
      (parseDoubleWord data (n+12)) (* NumberOfSymbols *)
      (parseWord data (n+16)) 		(* SizeOfOptionalHeader *)
      (parseWord data (n+18)) 		(* Characteristics_IFH *)
.

Definition parseImageDataDirectory (data : list (list BYTE)) (n : Z) : _IMAGE_DATA_DIRECTORY :=
    mkImageDataDirectory
      (parseDoubleWord data n)		    (* VirtualAddress_IDD *)
      (parseDoubleWord data (n + 4))    (* Size *)
.

Definition parseImageOptionalHeader (data : list (list BYTE)) (n : Z) : _IMAGE_OPTIONAL_HEADER :=
    mkImageOptionalHeader
      (parseWord data n)			    (*Magic *)
      (parseByte data (n + 2))			(*MajorLinkerVersion *)
      (parseByte data (n + 3))			(*MinorLinkerVersion *)
      (parseDoubleWord data (n + 4))	(*SizeOfCode *)
      (parseDoubleWord data (n + 8))	(*SizeOfInitializedData *)
      (parseDoubleWord data (n + 12))	(*SizeOfUninitializedData *)
      (parseDoubleWord data (n + 16))	(*AddressOfEntryPoint *)
      (parseDoubleWord data (n + 20))	(*BaseOfCode *)
      (parseDoubleWord data (n + 24))	(*BaseOfData *)
      (parseDoubleWord data (n + 28))	(*ImageBase *)
      (parseDoubleWord data (n + 32))	(*SectionAlignment *)
      (parseDoubleWord data (n + 36))	(*FileAlignment *)
      (parseWord data (n + 40))		    (*MajorOperatingSystemVersion *)
      (parseWord data (n + 42))			(*MinorOperatingSystemVersion *)
      (parseWord data (n + 44))			(*MajorImageVersion *)
      (parseWord data (n + 46))			(*MinorImageVersion *)
      (parseWord data (n + 48))			(*MajorSubsystemVersion *)
      (parseWord data (n + 50))			(*MinorSubsystemVersion *)
      (parseDoubleWord data (n + 52))	(*Win32VersionValue *)
      (parseDoubleWord data (n + 56))	(*SizeOfImage *)
      (parseDoubleWord data (n + 60))	(*SizeOfHeaders *)
      (parseDoubleWord data (n + 64))	(*CheckSum *)
      (parseWord data (n + 68))			(*Subsystem *)
      (parseWord data (n + 70))			(*DllCharacteristics *)
      (parseDoubleWord data (n + 72))	(*SizeOfStackReserve *)
      (parseDoubleWord data (n + 76))	(*SizeOfStackCommit *)
      (parseDoubleWord data (n + 80))	(*SizeOfHeapReserve *)
      (parseDoubleWord data (n + 84))	(*SizeOfHeapCommit *)
      (parseDoubleWord data (n + 88))	(*LoaderFlags *)
      (parseDoubleWord data (n + 92))	(*NumberOfRvaAndSizes *)
      (parseVector parseImageDataDirectory data 8 (n + 96) 16)(*DataDirectory *)
.

Definition parseImageNtHeader (data : list (list BYTE)) (n : Z) : _IMAGE_NT_HEADER :=
    mkImageNtHeader
      (parseDoubleWord data n) 			        (*Signature  *)
      (parseImageFileHeader data (n + 4)) 	    (*FileHeader  *)
      (parseImageOptionalHeader data (n + 24)) 	(*OptionalHeader  *)
.

Definition ISSN : Z := Z_of_nat IMAGE_SIZEOF_SHORT_NAME.

Definition parseImageSectionHeader (data : list (list BYTE)) (n : Z) : _IMAGE_SECTION_HEADER :=
    mkImageSectionHeader
      (parseVector (parseByte) data 1 n IMAGE_SIZEOF_SHORT_NAME)(*Name_ISH *)
      (parseDoubleWord data (n + ISSN))	        (*PhysicalAddressORVirtualSize*)
      (parseDoubleWord data (n + ISSN + 4))	    (*VirtualAddress_ISH *)
      (parseDoubleWord data (n + ISSN + 8))	    (*SizeOfRawData *)
      (parseDoubleWord data (n + ISSN + 12))	(*PointerToRawData *)
      (parseDoubleWord data (n + ISSN + 16))	(*PointerToRelocations *)
      (parseDoubleWord data (n + ISSN + 20))	(*PointerToLinenumbers *)
      (parseWord data (n + ISSN + 24))	        (*NumberOfRelocations *)
      (parseWord data (n + ISSN + 26))	        (*NumberOfLinenumbers *)
      (parseDoubleWord data (n + ISSN + 28))	(*Characteristics_ISH *)
.


Definition parseImageExportDirectory (data : list (list BYTE)) (n : Z) : _IMAGE_EXPORT_DIRECTORY :=
    mkImageExportDirectory
      (parseDoubleWord data n)		(*Characteristics_IED *)
      (parseDoubleWord data (n+4))	(*TimeDateStamp *)
      (parseWord data (n+8))		(*MajorVersion *)
      (parseWord data (n+10))		(*MinorVersion *)
      (parseDoubleWord data (n+12))	(*Name_IED *)
      (parseDoubleWord data (n+16))	(*Base *)
      (parseDoubleWord data (n+20))	(*NumberOfFunctions *)
      (parseDoubleWord data (n+24))	(*NumberOfNames *)
      (parseDoubleWord data (n+28))	(*AddressOfFunctions *)
      (parseDoubleWord data (n+32))	(*AddressOfNames *)
      (parseDoubleWord data (n+36))	(*AddressOfNameOrdinals *)
.

Definition parseImageThunkData (data : list (list BYTE)) (n : Z) : _IMAGE_THUNK_DATA :=
    mkImageThunkData
    	(parseByte data n)		    (*ForwarderString *)
	(parsePtr data (n+1)) 	        (*Function *)
	(parseDoubleWord data (n+5))	(*Ordinal *)
	(parsePtr data (n+9))	        (*AddressOfData *)
.

Fixpoint findSection (data : list (list BYTE)) (rva : DWORD) (n : Z) (num_sec : nat) : option _IMAGE_SECTION_HEADER :=
    match num_sec with
    | 0 => None
    | S n' => let curSection := parseImageSectionHeader data n in
              let v_start := VirtualAddress_ISH curSection in
              let v_end := Word.add v_start (SizeOfRawData curSection) in
              if andb (Word.lequ v_start rva) (Word.ltu rva v_end) then
                 Some curSection
              else
                 findSection data rva (n + 40) n'
    end.


Definition vAddr_to_offset (vaddr : DWORD) (header : _IMAGE_SECTION_HEADER) : DWORD :=
    Word.add (Word.sub vaddr (VirtualAddress_ISH header)) (PointerToRawData header).


Definition derefImageNtHeader (data : list (list BYTE)) (p : Ptr _IMAGE_NT_HEADER) : _IMAGE_NT_HEADER :=
        match p with
            | ptr d _ => parseImageNtHeader data (dword_to_Z d)
        end.

Definition getExports (data : list (list BYTE)) : list DWORD :=
    let dosHeader := parseImageDosHeader data in
    let ntHeader := derefImageNtHeader data (e_lfanew dosHeader) in
    let rva := (VirtualAddress_IDD (nth 0 (vtolist (DataDirectory (OptionalHeader ntHeader)))
                                           {| VirtualAddress_IDD := Word.repr 0; Size := Word.repr 0 |})) in
    match Word.unsigned rva with
    | 0%Z => nil
    | _ =>
           let sectionHeader := findSection data rva
                               ((ptr_to_Z (e_lfanew dosHeader)) + 248)
                               (word_to_nat (NumberOfSections (FileHeader ntHeader))) in
           match sectionHeader with
           | None => nil
           | Some header =>           
               let exportDir := parseImageExportDirectory data (dword_to_Z (vAddr_to_offset rva header)) in
               vtolist (parseVector (parseDoubleWord) data 4
                           (dword_to_Z (vAddr_to_offset (AddressOfFunctions exportDir) header))
                           (dword_to_nat (NumberOfFunctions exportDir))) 
           end
    end.

(* given a file, check that all exported symbols target
 * low memory chunk boundaries *)
Definition checkExports (data : list (list BYTE)) (mask : DWORD) : bool :=
    let exports := getExports data in
    let check (addr : DWORD) : bool :=
        Word.eq addr (Word.and addr mask)
    in
    List.fold_left (andb) (List.map check exports) true
.


Definition derefDataDirectoryIAT optionalHeader : _IMAGE_DATA_DIRECTORY :=
	(nth IMAGE_DIRECTORY_ENTRY_IAT (vtolist (DataDirectory optionalHeader))
		{| VirtualAddress_IDD := Word.repr 0; Size := Word.repr 0 |})
.

Definition derefImageOptionalHeader data : _IMAGE_OPTIONAL_HEADER :=
	let dosHeader := parseImageDosHeader data in
	let ntHeader := derefImageNtHeader data (e_lfanew dosHeader) in
	OptionalHeader ntHeader
.

(* Unused, has a bug
Definition parseImageImportDescriptor (data : list BYTE) (n : nat) : _IMAGE_IMPORT_DESCRIPTOR:=
    mkImageImportDescriptor
    	(parseDoubleWord data n) 	(* OriginalFirstThunk *)
	(parseDoubleWord data (n+4))	(* TimeDataStamp_IDD *)
	(parseDoubleWord data (n+8))	(* Ordinal *)
	(parseDoubleWord data (n+12))	(* AddressOfData *)
.

unused, has a bug
Definition derefImageImportDescriptor (data : list DWORD) 
  (dataDirectory : _IMAGE_DATA_DIRECTORY) : _IMAGE_IMPORT_DESCRIPTOR :=
	(parseImageImportDescriptor data 
		(dword_to_nat dataDirectory[IMAGE_DIRECTORY_ENTRY_IMPORT].VirtualAddress_IDD))
.
*)

Inductive IATBounds : Type :=
    | iatbounds : (DWORD * DWORD) -> IATBounds.

(* this returns the RVA start address and the size as two DWORD elements *)
Definition getIATBounds (data : list (list BYTE)) : IATBounds :=
	let optionalHeader := derefImageOptionalHeader data in
	let IAT := derefDataDirectoryIAT optionalHeader in
	iatbounds ((VirtualAddress_IDD IAT), (Size IAT))
.

(* Grabs executable sections defined in the section headers *)
Fixpoint getExecutableBounds (data : list (list BYTE)) (start : Z) (n : nat) 
                             : list (DWORD * DWORD * list (list BYTE)) :=
   match n with
   | O => nil   
   | S n' =>
             let sectionHeader := parseImageSectionHeader data start in
             let containsExec := Word.eq (Word.and IMAGE_SCN_CNT_CODE (Characteristics_ISH sectionHeader)) IMAGE_SCN_CNT_CODE in
             match containsExec with
             | false => getExecutableBounds data (start+40) n'
             | true => 
                            let rstart := PointerToRawData sectionHeader in
                            let rsize := SizeOfRawData sectionHeader in
                            let numSections := Z_to_nat (Zdiv (Word.unsigned rsize) block_size) in
                             cons (rstart,rsize,copySection data (Word.unsigned rstart) (Word.unsigned rsize) numSections)
                            (getExecutableBounds data (start+40) n')
             end
end.

(* Finds location of section headers, then calls getExecutableBounds to get executable sections *)
Definition getExecutableSections (data : list (list BYTE)) 
                                 : list (DWORD * DWORD * list (list BYTE)) :=
   let dosHeader := parseImageDosHeader data in
   let ntHeader := derefImageNtHeader data (e_lfanew dosHeader) in
   getExecutableBounds data ((ptr_to_Z (e_lfanew dosHeader)) + 248)
                                          (word_to_nat (NumberOfSections (FileHeader ntHeader)))
.

Close Scope vector_scope.
