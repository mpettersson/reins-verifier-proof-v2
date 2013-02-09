(*  Copyright (c) 2012. Ben Ferrell, Kenneth Miller, 
 *  Matthew Pettersson, Justin Sahs, and Brett Webster.
 *
 *  This file is part of REINS.
 *
 *  This file is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License as
 *  published by the Free Software Foundation; either version 2 of
 *  the License, or (at your option) any later version.*)


(* TODO:
 * 1) How to model a C union in Coq equivalently?
 * - IDEA: an inductive type
 * e.g.,
 *   union _x {
 *     WORD field_one;
 *     WORD field_two;
 *   };
 * becomes
 *   Inductive _x : Type :=
 *   | field_one : WORD -> _x
 *   | field_two : WORD -> _x.
 * --doesn't handle the fact that you can initialize as one type, then
 * --dereference as another...
 * - IDEA: simple tuple of all possible types
 *
 * 2) name conflicts: some field names are repeated, but they are global names in
 *    Coq, e.g. _IMAGE_FILE_HEADER and _IMAGE_IMPORT_DESCRIPTOR both have a member
 *    named TimeDateStamp, but there can be only one TimeDateStamp (this is because
 *    Coq creates a function TimeDateStamp : _IMAGE_DOS_HEADER -> DWORD). We need
 *    to come up with a naming convention, or to use some kind of namespace stuff.
 *    This is the only thing currently keeping this file from compiling.
 *)
 
(* For now, as far as the name conflict goes, we don't have to replicate the C version of headers
perfectly-that is for our information as we work with the program. Lets just make the _IMAGE_FILE_HEADER's 
TimeDateStamp member be TimeDateStamp_IFH-this identifies it just fine and still keeps it separate from the 
IMAGE_IMPORT_DESCRIPTOR's, which we can call TimeDateStamp_IID
    -Adam*)
(* Also, when it comes to unions, I think it best if we just keep track of all unions within the series
of structs, and have a function interpret the data that's in it, and have the type actually be another list of bytes,
this way, when anything is assigned to it, the functions always return updated results accordingly.
    -Adam *)

Require Import Bits.

Inductive vector : nat -> Type -> Type :=
| vnil : forall (A : Type), vector 0 A
| vcons : forall (A : Type) (n : nat), A -> vector n A -> vector (S n) A.

Notation "[]" := (vnil _) : vector_scope.
Notation "h :: t" := (vcons _ _ h t) (at level 60, right associativity) : vector_scope.
Notation "t [ n ]" := (vector n t) (at level 90, no associativity) : vector_scope.

Open Scope vector_scope.

Fixpoint vtolist {A : Type} {l : nat} (v : vector l A) : list A :=
    match v with
            | [] => nil
            | h :: t => cons h (vtolist t)
    end.

Definition BYTE := int8.
Definition WORD := int16.
Definition DWORD := int32.

Inductive Ptr : Type -> Type :=
| ptr : DWORD -> forall (A : Type), Ptr A.


Record _IMAGE_DATA_DIRECTORY : Type := mkImageDataDirectory {
 VirtualAddress_IDD : DWORD;
 Size : DWORD
}.

Record _IMAGE_OPTIONAL_HEADER : Type := mkImageOptionalHeader {
	Magic : WORD;
	MajorLinkerVersion : BYTE;
	MinorLinkerVersion : BYTE;
	SizeOfCode : DWORD;
	SizeOfInitializedData : DWORD;
	SizeOfUninitializedData : DWORD;
	AddressOfEntryPoint : DWORD;
	BaseOfCode : DWORD;
	BaseOfData : DWORD;
	ImageBase : DWORD;
	SectionAlignment : DWORD;
	FileAlignment : DWORD;
	MajorOperatingSystemVersion : WORD;
	MinorOperatingSystemVersion : WORD;
	MajorImageVersion : WORD;
	MinorImageVersion : WORD;
	MajorSubsystemVersion : WORD;
	MinorSubsystemVersion : WORD;
	Win32VersionValue : DWORD;
	SizeOfImage : DWORD;
	SizeOfHeaders : DWORD;
	CheckSum : DWORD;
	Subsystem : WORD;
	DllCharacteristics : WORD;
	SizeOfStackReserve : DWORD;
	SizeOfStackCommit : DWORD;
	SizeOfHeapReserve : DWORD;
	SizeOfHeapCommit : DWORD;
	LoaderFlags : DWORD;
	NumberOfRvaAndSizes : DWORD;
	DataDirectory : _IMAGE_DATA_DIRECTORY[16] (* still need to make this 16 long; 
	represents an array of 16 _IMAGE_DATA_DIRECTORY types. Each one of these describes a particular thing per the Definitions above *)
}.

Record _IMAGE_FILE_HEADER : Type := mkImageFileHeader {
	Machine : WORD;
	NumberOfSections : WORD;
	TimeDateStamp_IFH : DWORD;
	PointerToSymbolTable : DWORD; (*should be a pointer, but not needed*)
	NumberOfSymbols : DWORD;
	SizeOfOptionalHeader : WORD;
	Characteristics_IFH : WORD
}.

Record _IMAGE_NT_HEADER : Type := mkImageNtHeader {
	Signature : DWORD;
	FileHeader : _IMAGE_FILE_HEADER;
	OptionalHeader : _IMAGE_OPTIONAL_HEADER
}.

Record _IMAGE_DOS_HEADER : Type  := mkImageDosHeader {
	e_magic: WORD;
	e_cblp : WORD;
	e_cp : WORD;
	e_crlc : WORD;
	e_cparhdr : WORD;
	e_minalloc : WORD;
	e_maxalloc : WORD;
	e_ss : WORD;
	e_sp : WORD;
	e_csum : WORD;
	e_ip : WORD;
	e_cs : WORD;
	e_lfarlc : WORD;
	e_ovno : WORD;
	e_res : WORD[4];
	e_oemid : WORD;
	e_oeminfo : WORD;
	e_res2 : WORD[10];
	e_lfanew : Ptr _IMAGE_NT_HEADER
}.

Definition IMAGE_DIRECTORY_ENTRY_EXPORT := 0.
Definition IMAGE_DIRECTORY_ENTRY_IMPORT := 1.
Definition IMAGE_DIRECTORY_ENTRY_RESOURCE := 2.
Definition IMAGE_DIRECTORY_ENTRY_EXCEPTION :=3.
Definition IMAGE_DIRECTORY_ENTRY_SECURITY :=4.
Definition IMAGE_DIRECTORY_ENTRY_BASERELOC :=5.
Definition IMAGE_DIRECTORY_ENTRY_DEBUG :=6.
Definition IMAGE_DIRECTORY_ENTRY_COPYRIGHT :=7.
Definition IMAGE_DIRECTORY_ENTRY_GLOBALPTR :=8.
Definition IMAGE_DIRECTORY_ENTRY_TLS :=9.
Definition IMAGE_DIRECTORY_ENTRY_LOAD_CONFIG :=10.
Definition IMAGE_DIRECTORY_ENTRY_BOUND_IMPORT :=11.
Definition IMAGE_DIRECTORY_ENTRY_IAT :=12.
Definition IMAGE_DIRECTORY_ENTRY_DELAY_IMPORT :=13.
Definition IMAGE_DIRECTORY_ENTRY_COM_DESCRIPTOR :=14.
Definition IMAGE_DIRECTORY_ENTRY_END :=15.

(*TODO: real definitions *)
Definition LPBYTE := BYTE.

Record _IMAGE_IMPORT_BY_NAME : Type := mkImageImportByName {
 Hint : WORD;
 Name_IIBN : BYTE[16]
}.


(* this needs to be modeled as a union *)
Record _IMAGE_THUNK_DATA : Type := mkImageThunkData{
	ForwarderString : LPBYTE;
	Function : Ptr DWORD;
	Ordinal : DWORD;
	AddressOfData : Ptr _IMAGE_IMPORT_BY_NAME
}.

Record _IMAGE_IMPORT_DESCRIPTOR : Type := mkImageImportDescriptor {
	OriginalFirstThunk : Ptr _IMAGE_THUNK_DATA; (* this was unioned with a characteristics field *)
	TimeDateStamp_IID : DWORD; 
	ForwarderChain : DWORD; 
	Name_IID : DWORD;
	FirstThunk : forall (d : DWORD), _IMAGE_THUNK_DATA
}.

Record _IMAGE_EXPORT_DIRECTORY : Type := mkImageExportDirectory {
	Characteristics_IED : DWORD;
	TimeDateStamp : DWORD;
	MajorVersion : WORD;
	MinorVersion : WORD;
	Name_IED : DWORD;
	Base : DWORD;
	NumberOfFunctions : DWORD;
	NumberOfNames : DWORD;
	AddressOfFunctions : DWORD; (* is an array of pointers to functions *)
	AddressOfNames : DWORD;
	AddressOfNameOrdinals : DWORD
}.
(* TODO: what is IMAGE_SIZEOF_SHORT_NAME? *)
Definition IMAGE_SIZEOF_SHORT_NAME := 8.

Record _IMAGE_SECTION_HEADER : Type := mkImageSectionHeader {
	Name_ISH : BYTE[IMAGE_SIZEOF_SHORT_NAME];
	PhysicalAddressORVirtualSize : DWORD;
	VirtualAddress_ISH : DWORD;
	SizeOfRawData : DWORD;
	PointerToRawData : DWORD;
	PointerToRelocations : DWORD;
	PointerToLinenumbers : DWORD;
	NumberOfRelocations : WORD;
	NumberOfLinenumbers : WORD;
	Characteristics_ISH : DWORD
}.

(* The following list of Definitions are used for the characteristics field, 
 * in order to discern the purpose and capabilities of a section of a PE file
 * Note: Coq doesn't support hex literals, so they are given in decimal *)
Open Scope Z_scope.
Definition IMAGE_SCN_TYPE_NO_PAD            : int32 := Word.repr 8.          (* 0x00000008 obsolete *)
Definition IMAGE_SCN_CNT_CODE               : int32 := Word.repr 32.         (* 0x00000020 The section contains executable code. *)
Definition IMAGE_SCN_CNT_INITIALIZED_DATA   : int32 := Word.repr 64.         (* 0x00000040 section contains initialized data *)
Definition IMAGE_SCN_CNT_UNINITIALIZED_DATA : int32 := Word.repr 128.        (* 0x00000080 section contains uninitialized data *)
Definition IMAGE_SCN_LNK_OTHER              : int32 := Word.repr 256.        (* 0x00000100 reserved *)
Definition IMAGE_SCN_LNK_INFO               : int32 := Word.repr 512.        (* 0x00000200 valid only for object files *)
Definition IMAGE_SCN_LNK_REMOVE             : int32 := Word.repr 2048.       (* 0x00000800 reserved *)
Definition IMAGE_SCN_LNK_COMDAT             : int32 := Word.repr 4096.       (* 0x00001000 contains COMDAT data; valid for object files *)
Definition IMAGE_SCN_NO_DEFER_SPEC_EXC      : int32 := Word.repr 16384.      (* 0x00004000 reset speculative exceptions handling bits in the TLB entries for this section *)
Definition IMAGE_SCN_GPREL                  : int32 := Word.repr 32768.      (* 0x00008000 section contains data referenced through the global pointer *)
Definition IMAGE_SCN_MEM_PURGEABLE          : int32 := Word.repr 131072.     (* 0x00020000 reserved *)
Definition IMAGE_SCN_MEM_LOCKED             : int32 := Word.repr 262144.     (* 0x00040000 reserved *)
Definition IMAGE_SCN_MEM_PRELOAD            : int32 := Word.repr 524288.     (* 0x00080000 reserved *)
Definition IMAGE_SCN_ALIGN_1BYTES           : int32 := Word.repr 1048576.    (* 0x00100000 align data on 1-byte boundary; for obj files *)
Definition IMAGE_SCN_ALIGN_2BYTES           : int32 := Word.repr 2097152.    (* 0x00200000 align data on 2-byte boundary; for obj files *)
Definition IMAGE_SCN_ALIGN_4BYTES           : int32 := Word.repr 3145728.    (* 0x00300000 align data on 4-byte boundary; for obj files *)
Definition IMAGE_SCN_ALIGN_8BYTES           : int32 := Word.repr 4194304.    (* 0x00400000 align data on 8-byte boundary; for obj files *)
Definition IMAGE_SCN_ALIGN_16BYTES          : int32 := Word.repr 5242880.    (* 0x00500000 align data on 16-byte boundary; for obj files *)
Definition IMAGE_SCN_ALIGN_32BYTES          : int32 := Word.repr 6291456.    (* 0x00600000 align data on 32-byte boundary; for obj files *)
Definition IMAGE_SCN_ALIGN_64BYTES          : int32 := Word.repr 7340032.    (* 0x00700000 align data on 64-byte boundary; for obj files *)
Definition IMAGE_SCN_ALIGN_128BYTES         : int32 := Word.repr 8388608.    (* 0x00800000 align data on 128-byte boundary; for obj files *)
Definition IMAGE_SCN_ALIGN_256BYTES         : int32 := Word.repr 9437184.    (* 0x00900000 align data on 256-byte boundary; for obj files *)
Definition IMAGE_SCN_ALIGN_512BYTES         : int32 := Word.repr 10485760.   (* 0x00A00000 align data on 512-byte boundary; for obj files *)
Definition IMAGE_SCN_ALIGN_1024BYTES        : int32 := Word.repr 11534336.   (* 0x00B00000 align data on 1024-byte boundary; for obj files *)
Definition IMAGE_SCN_ALIGN_2048BYTES        : int32 := Word.repr 12582912.   (* 0x00C00000 align data on 2048-byte boundary; for obj files *)
Definition IMAGE_SCN_ALIGN_4096BYTES        : int32 := Word.repr 13631488.   (* 0x00D00000 align data on 4096-byte boundary; for obj files *)
Definition IMAGE_SCN_ALIGN_8192BYTES        : int32 := Word.repr 14680064.   (* 0x00E00000 align data on 8196-byte boundary; for obj files *)
Definition IMAGE_SCN_LNK_NRELOC_OVFL        : int32 := Word.repr 16777216.   (* 0x01000000 section contains extended relocations *)
Definition IMAGE_SCN_MEM_DISCARDABLE        : int32 := Word.repr 33554432.   (* 0x02000000 section can be discarded *)
Definition IMAGE_SCN_MEM_NOT_CACHED         : int32 := Word.repr 67108864.   (* 0x04000000 section cannot be cached *)
Definition IMAGE_SCN_MEM_NOT_PAGED          : int32 := Word.repr 134217728.  (* 0x08000000 section cannot be paged *)
Definition IMAGE_SCN_MEM_SHARED             : int32 := Word.repr 268435456.  (* 0x10000000 section can be shared in memory *)
Definition IMAGE_SCN_MEM_EXECUTE            : int32 := Word.repr 536870912.  (* 0x20000000 section can be executed *)
Definition IMAGE_SCN_MEM_READ               : int32 := Word.repr 1073741824. (* 0x40000000 section can be read *)
Definition IMAGE_SCN_MEM_WRITE              : int32 := Word.repr 4294967295. (* 0x80000000 section can be written to *)

Close Scope Z_scope.
Close Scope vector_scope.
