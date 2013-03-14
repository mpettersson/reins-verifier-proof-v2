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


(* If ReinsVerifier is given any binary and it has all the properties,
then the result holds. If it does not have all of them, then it does 
not hold *)


(* Copyright (c) 2011. Greg Morrisett, Gang Tan, Joseph Tassarotti, 
   Jean-Baptiste Tristan, and Edward Gan.

   This file is part of RockSalt.

   This file is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.
*)

Require Import Classical.
Require Import Coqlib.
Require Import Parser.
Require Import Ascii.
Require Import String.
Require Import List.
Require Import Bits.
Require Import Decode.
Require Import X86Syntax.
Require Import X86Semantics.
Require Import X86Lemmas.
Require Import Monad.
Require Import Int32.
Require Import ReinsVerifierDFA.
Require Import PEFormat.
Require Import PETraversal.
Require Import ReinsVerifier.
Require Import ReinsDFACorrectness.
Require Import REINSjmp.

Import X86_PARSER_ARG.
Import X86_PARSER.
Import X86_BASE_PARSER.
Import X86_RTL.
Import X86_MACHINE.
Import X86_Decode.
Require Import RTL.

Import Tacs.
Require Import Omega.

Definition emptyPrefix := mkPrefix None None false false.

Module Int32SetFacts := Coq.MSets.MSetFacts.Facts ReinsVerifier.Int32Set.

(* Todo: organize the following *)

Lemma chunkSize_gt_0 : chunkSize > 0.
Proof. unfold chunkSize. apply Coqlib.two_power_nat_pos. Qed.

(** ** Properties of aligned *)

Lemma chunkSize_divide_modulus : Znumtheory.Zdivide chunkSize (Word.modulus 31).
Proof. unfold chunkSize, Word.modulus. apply two_power_nat_divide.
  unfold wordsize. unfold logChunkSize. omega.
Qed.

Lemma Zmod_mod_modulus_chunkSize :
  forall x:Z, x mod chunkSize = (x mod (Word.modulus 31)) mod chunkSize.
Proof. intros; apply Znumtheory.Zmod_div_mod.
  apply Zgt_lt. apply chunkSize_gt_0.
    apply Zgt_lt. apply modulus_pos.
    apply chunkSize_divide_modulus.
Qed.

(* if you have two aligned integers, then their sum is also aligned *)
Lemma aligned_plus :
  forall a b:int32, aligned a -> aligned b -> aligned (a +32 b).
Proof. unfold aligned, aligned_bool. intros a b H1 H2.
  apply Zeq_is_eq_bool in H1; apply Zeq_is_eq_bool in H2; 
    apply Zeq_is_eq_bool.
  unfold unsigned in * |- *.
  destruct a as [a' Ha]. destruct b as [b' Hb].
  simpl in * |- *. 
  rewrite <- Zmod_mod_modulus_chunkSize.
  rewrite Zplus_mod. rewrite H1, H2. simpl. apply Zmod_0_l.
Qed.

Lemma aligned_neg :
  forall a:int32, aligned a -> aligned (-32 a).
Proof. unfold aligned, aligned_bool. intros a H.
  apply Zeq_is_eq_bool in H; apply Zeq_is_eq_bool.
  unfold unsigned in * |- *.
  destruct a as [a' Ha]. simpl in * |- *. 
  rewrite <- Zmod_mod_modulus_chunkSize.
  apply Z_mod_zero_opp_full. trivial.
Qed.

Lemma aligned_sub :
  forall a b:int32, aligned a -> aligned b -> aligned (a -32 b).
Proof. intros a b H1 H2. unfold w32sub. rewrite sub_add_opp.
  apply aligned_plus. trivial. apply aligned_neg. trivial.
Qed.

Lemma aligned_chunkSize : aligned (repr chunkSize).
Proof. unfold aligned, aligned_bool.
  apply Zeq_is_eq_bool. simpl.
  rewrite <- Zmod_mod_modulus_chunkSize.
  apply Z_mod_same_full.
Qed.

Lemma aligned_0 : aligned int32_zero.
Proof. unfold aligned, aligned_bool.
  apply Zeq_is_eq_bool. simpl.
  rewrite <- Zmod_mod_modulus_chunkSize.
  apply Zmod_0_l.
Qed.

(* tactic to apply all of these aligned lemmas *)
Ltac aligned_tac := 
  match goal with
    | [ |- aligned (?a +32 ?b)] => 
      apply aligned_plus; (assumption || aligned_tac)
    | [ |- aligned (?a -32 ?b)] => 
      apply aligned_sub; (assumption || aligned_tac)
    | [ |- aligned (-32 ?b)] => 
      apply aligned_neg; (assumption || aligned_tac)
    | [ |- aligned (repr chunkSize)] => apply aligned_chunkSize
    | [ |- aligned int32_zero] => apply aligned_0
    | _ => idtac
  end.

(* If Z is aligned, the chunksize divides Z *)
Lemma aligned_zdivide :
  forall z:Z, aligned (repr z) ->  Znumtheory.Zdivide chunkSize z.
Proof. unfold aligned, aligned_bool. intros a H; apply Zeq_is_eq_bool in H.
  apply Znumtheory.Zmod_divide. generalize chunkSize_gt_0. omega. 
  simpl in H. rewrite <- Zmod_mod_modulus_chunkSize in H. trivial.
Qed.

(* CHANGE Need to put the value of our safeMask here *)
Lemma signed_safemask_eq :
  signed (safeMask) =  268435440.
Proof. vm_compute. reflexivity. Qed.

Lemma unsigned_safemask_eq :
  unsigned safeMask = 268435440.
Proof. vm_compute. reflexivity. Qed.

Lemma unsigned_signed_eq :
  forall (x y : int32), unsigned x = unsigned y <-> signed x = signed y.
Proof.
  intros. split.
    intros. unfold signed. rewrite <- H. reflexivity.
    intros. unfold signed in H.
    destruct (zlt (unsigned x) (half_modulus 31)).
    destruct (zlt (unsigned y) (half_modulus 31)).
      exact H.
      contradict H.
      assert (unsigned y < modulus 31).
        apply unsigned_range.
      assert (0 <= unsigned x).
        apply unsigned_range.
      omega.
    destruct (zlt (unsigned y) (half_modulus 31)).
      contradict H.
      assert (unsigned x < modulus 31).
        apply unsigned_range.
      assert (0 <= unsigned y).
        apply unsigned_range.
      omega.
    omega.
Qed.

(* if you AND any address with safeMask, you will get an aligned address *)
Lemma and_safeMask_aligned : forall (v wd: int32),
  signed wd = signed safeMask -> aligned (Word.and v wd).
Proof.
  intros.
  assert (signed wd = unsigned wd).
    assert (signed safeMask = unsigned safeMask).
      rewrite -> signed_safemask_eq. rewrite -> unsigned_safemask_eq.
      reflexivity.
    rewrite -> H. rewrite -> H0. apply unsigned_signed_eq. omega.
  assert (low_bits_zero 31 (unsigned wd) (Z_of_nat logChunkSize)).
    apply multiple_low_bits_zero. vm_compute. omega.
    rewrite -> H0 in H. rewrite -> H. rewrite -> signed_safemask_eq.
    compute. reflexivity.
  unfold aligned, aligned_bool.
  apply ZOrderedType.Z_as_DT.eqb_eq.
  apply low_bits_zero_multiple with (wordsize_minus_one := 31%nat).
    unfold logChunkSize. compute. omega.
    apply and_low_bits_zero.
      apply inj_le. unfold logChunkSize. compute. omega.
      exact H1.
Qed.

Lemma safeMask_low_mem :
  high_bits_zero (signed safeMask) (Z_of_nat lowMemZeroBits) (wordsize 31).
Proof.
  change lowMemZeroBits with (wordsize 31 - (wordsize 31 - lowMemZeroBits))%nat.
  apply lt_2k_high_bits_zero.
  omega. compute.
    split. intro. contradict H. discriminate. reflexivity.
Qed.

Lemma and_safeMask_low_mem : forall (v wd: int32),
  signed wd = signed safeMask -> unsigned (Word.and v wd) < lowMemCutoff.
Proof.
  intros.
  assert (signed wd = unsigned wd).
    assert (signed safeMask = unsigned safeMask).
      rewrite -> signed_safemask_eq. rewrite -> unsigned_safemask_eq.
      reflexivity.
    rewrite -> H. rewrite -> H0. apply unsigned_signed_eq. omega.
  assert (high_bits_zero (unsigned wd) (Z_of_nat lowMemZeroBits) (wordsize 31)).
    rewrite <- H0. rewrite -> H. apply safeMask_low_mem.
  unfold lowMemCutoff. 
  assert (0 <= unsigned (and v wd) < two_power_nat (wordsize 31 - lowMemZeroBits)).
    apply high_bits_zero_lt_2k with (n := 31%nat).
      apply unsigned_range.
      compute. omega.
      apply and_high_bits_zero.
        simpl. omega.
        simpl. simpl in H1. exact H1.
   omega.
Qed.
(** * proving checkAligned is correct *)

(* Unfolding checkAligned, 
   checks that all multiple of the chunk size is in the list *)
Lemma checkAligned_aux_unfold (startAddrs:Int32Set.t)(next:Z)(len:nat) :
    checkAligned_aux (startAddrs, next, len) = 
    match len with
      | 0%nat => true
      | _ => 
        (Int32Set.mem (repr next) startAddrs &&
         checkAligned_aux ((startAddrs, (next + chunkSize)), 
                          (len - Zabs_nat chunkSize)%nat))
    end.
Proof. 
  rewrite checkAligned_aux_equation.
  destruct len; trivial. 
Qed.

Lemma checkAligned_aux_corr : forall len addr startAddrs x,
  checkAligned_aux (startAddrs, addr, len) = true
    -> Zmod addr chunkSize = 0
    -> addr <= x < addr + Z_of_nat len
    -> Zmod x chunkSize = 0
    -> Int32Set.In (repr x) startAddrs.
Proof. induction len using lt_wf_ind. 
  destruct len. 
  Case "len = 0". prover.
  Case "len > 0". intros.
    rewrite checkAligned_aux_unfold in H0.
    bool_elim_tac.
    destruct H2.
    apply Zle_lt_or_eq in H2.
    destruct H2.
    SCase "addr < x". 
      generalize (chunkSize_gt_0); intro.
      assert (x >= addr + chunkSize).
        use_lemma (Z_div_exact_2 addr) by eassumption.
        use_lemma (Z_div_exact_2 x) by eassumption.
        assert (H10: chunkSize * (addr / chunkSize) < chunkSize * (x / chunkSize))
          by omega.
        rewrite (Zmult_comm chunkSize (addr/chunkSize)) in H10.
        rewrite (Zmult_comm chunkSize (x/chunkSize)) in H10.
        use_lemma (Zmult_lt_reg_r (addr/chunkSize) (x/chunkSize) chunkSize) 
          by omega.
        assert (x/chunkSize >= addr/chunkSize + 1) by omega.
        rewrite H7. rewrite H8.  
        eapply Zge_trans.
          eapply Zmult_ge_compat_l. eassumption. omega.
          ring_simplify. omega.
     assert (H20:Z_of_nat (S len) >= chunkSize) by omega.
     rewrite <- (Zabs_eq chunkSize) in H20 by omega.
     rewrite <- inj_Zabs_nat in H20.
     apply inj_ge_rev in H20.
     assert (x < (addr + chunkSize) + Z_of_nat (S len - Zabs_nat chunkSize)%nat).
       rewrite inj_minus1 by assumption.
       rewrite inj_Zabs_nat.
       rewrite (Zabs_eq chunkSize) by omega.
       ring_simplify. trivial.
     eapply H; try eassumption.
       apply lt_minus. omega. apply inj_lt_rev. simpl. omega.
       rewrite Zplus_mod. rewrite H1. 
         rewrite Z_mod_same_full. simpl. apply Zmod_0_l.
       omega.
    SCase "addr = x". prover.
Qed.

Lemma checkAligned_corr : forall len startAddrs x,
  checkAligned startAddrs len = true
    -> 0 <= x < Z_of_nat len
    -> Zmod x chunkSize = 0
    -> Int32Set.In (repr x) startAddrs.
Proof. unfold checkAligned. intros.
  eapply checkAligned_aux_corr; try eassumption.
  apply Zmod_0_l.
Qed.

(* New Lemmas! *)

Lemma fold_left_andb_forall : forall a l,
   fold_left andb (a::l) true = true ->
   a = true
with fold_left_andb_base : forall a l,
  fold_left andb l a = true ->
  a = true.
Proof.
  intros. simpl in H.
  induction l.
    simpl in H. exact H.
    simpl in H.
    assert ((a && a0) = true).
    apply fold_left_andb_base with (l:=l). exact H.
    rewrite -> andb_true_iff in H0.
    destruct H0. exact H0.
  intros.
  induction l.
    simpl in H. exact H.
    simpl in H.
    apply fold_left_andb_base in H.
    rewrite -> andb_true_iff in H.
    destruct H. exact H.
Qed.

Lemma eq_and_addr_mask : forall addr,
  eq addr (and addr safeMask) = true -> (unsigned addr < lowMemCutoff)%Z /\ aligned addr.
Proof.
  intros.
  rewrite -> int_eq_true_iff2 in H.
  split.
    rewrite -> H. apply and_safeMask_low_mem. reflexivity.
    rewrite -> H. apply and_safeMask_aligned. reflexivity.
Qed.



Lemma checkExports_corr : forall (f : list (list BYTE)) (e e': list DWORD) (a : DWORD),
  e = getExports f ->
  checkExports f safeMask = true ->
  e = a::e' ->
  (unsigned a < lowMemCutoff)%Z /\ (aligned a%Z).
Proof.
  intros.
  unfold checkExports in H0.
  rewrite <- H in H0.
  apply eq_and_addr_mask. rewrite -> H1 in H0. simpl List.map in H0.
  apply fold_left_andb_forall with (l:=List.map (fun addr : DWORD => eq addr (and addr safeMask)) e').
  exact H0.
Qed.

Require Import MSetFacts.

Lemma checkIATAddresses_corr :
   forall (addrs : Int32Set.t) (a b : int32),
   checkIATAddresses (iatbounds (a,b)) addrs = true ->
   forall (addr : int32), Int32Set.In addr addrs ->
   ((Word.unsigned a) <= (Word.unsigned addr) <= (Word.unsigned (Word.add a b))
    /\ modu (addr -32 a) (repr (Z_of_nat (wordsize 31))) = (repr 0)).
Proof.
  intros.
  unfold checkIATAddresses in H.
  apply Int32Set.for_all_spec in H.
  unfold Int32Set.For_all in H.
  do 2 rewrite <- int_lequ_true_iff.
  rewrite <- andb_true_iff.
  rewrite <- int_eq_true_iff2.
  rewrite <- andb_true_iff.
  apply H. exact H0.
  (*in order to apply Int32Set.for_all_spec on "Int32Set.for_all f s",
    we must prove 'compatb f'; this unfolds to 
    Proper (E.eq ==> Logic.eq) f, where E depends on the type of elements
    of s.  This reads as "The respectful morphism applied to E.eq and Logic.eq
    is proper", where,
     - the "respectful morphism applied to binary relations (R : A -> A -> Prop)
          and (R' : B -> B -> Prop)" gives the binary relation
          (Rr : (A -> B) -> (A -> B) -> Prop) := fun f g => R x y -> R' (f x) (g y).
     - a relation (R : A -> A -> Prop) is 'Proper' with respect to some element f
       if (R f f) holds.
    That is, 'compatb f' for (f : A -> B) says that it is possible to transform a
    binary equality relation (R : A -> A -> Prop) to a binary relation over functions
    of type (A -> B) such that f `=` f... that is, f "respects" standard equality*)
  unfold Morphisms.Proper , Morphisms.respectful.
  intros. rewrite -> int_eq_true_iff2 in H1. rewrite -> H1. reflexivity.
Qed.

Lemma checkCallAlignment_corr : forall (callAddrs : Int32Set.t),
  checkCallAlignment callAddrs = true ->
  forall (addr : int32), addr <=32 (repr ((two_power_nat 31) - 2)%Z) ->
  Int32Set.In addr callAddrs ->
  Zmod (Word.unsigned addr) chunkSize = 0%Z.
Proof.
  intros. unfold checkCallAlignment in H. apply Int32Set.for_all_spec in H.
  unfold Int32Set.For_all in H.
  unfold aligned_bool in H.
  rewrite -> Zeq_is_eq_bool.
  apply H. exact H1.
  unfold Morphisms.Proper, Morphisms.respectful.
  intros. apply int_eq_true_iff2 in H2. rewrite -> H2. reflexivity.
Qed.

Lemma checkExecSectionLowMem_corr : forall (start length : int32),
  checkExecSectionLowMemory start length = true ->
  (unsigned start <= unsigned (start +32 length))%Z
    /\ ((Word.unsigned (Word.add start length) <= lowMemCutoff))%Z.
Proof.
  intros. unfold checkExecSectionLowMemory, checkNoOverflow, int32_lequ_bool in H.
  rewrite -> andb_true_iff in H.
  repeat rewrite -> int_lequ_true_iff in H.
  destruct H.
  split.
    exact H0.
    assert (unsigned (@repr 31 lowMemCutoff) = lowMemCutoff).
      apply eqm_small_eq with (wordsize_minus_one:=31%nat).
      apply eqm_unsigned_repr.
      compute. split. intro. contradict H1. discriminate. reflexivity.
      compute. split. intro. contradict H1. discriminate. reflexivity.
    rewrite -> H1 in H. exact H.
Qed.


(*** used to compile to here ***)
Section VERIFIER_CORR.


  (* 20130219 - MCP - Added variables that are used in ReinsVerifier.v *)
  Variable non_cflow_dfa : DFA.
  Variable dir_cflow_dfa : DFA.
  Variable reinsjmp_nonIAT_dfa : DFA.
  Variable reinsjmp_IAT_or_RET_dfa : DFA.
  Variable reinsjmp_IAT_CALL_dfa : DFA.
  Variable reinsjmp_nonIAT_mask : parser (pair_t instruction_t instruction_t).
  Variable reinsjmp_IAT_or_RET_mask : parser (pair_t instruction_t instruction_t).
  Variable reinsjmp_IAT_CALL_p : parser instruction_t.

  (* The trampoline region is a blessed region in the code segment. 
     It's inserted there by the loader and never checked by the validator.
     The idea is that if we jump into the trampoline region and the PC is aligned,
     then that is a safe state.
     This variable marks the limit of the trampoline region *)
  Variable trampoline_limit : int32.

  (* MCP - Updated checkProgram, checkExecSection, process_buffer_aux,
   * and process_buffer to respect ReinsVerifier.checkProgram def *)
  Definition checkProgram := 
    ReinsVerifier.checkProgram 
       non_cflow_dfa
       dir_cflow_dfa
       reinsjmp_nonIAT_dfa
       reinsjmp_IAT_or_RET_dfa
       reinsjmp_IAT_CALL_dfa
       reinsjmp_nonIAT_mask
       reinsjmp_IAT_or_RET_mask.

  Definition checkExecSection :=
    ReinsVerifier.checkExecSection
       non_cflow_dfa
       dir_cflow_dfa
       reinsjmp_nonIAT_dfa
       reinsjmp_IAT_or_RET_dfa
       reinsjmp_IAT_CALL_dfa
       reinsjmp_nonIAT_mask
       reinsjmp_IAT_or_RET_mask.

  Definition process_buffer_aux := 
    ReinsVerifier.process_buffer_aux 
       non_cflow_dfa
       dir_cflow_dfa
       reinsjmp_nonIAT_dfa
       reinsjmp_IAT_or_RET_dfa
       reinsjmp_IAT_CALL_dfa
       reinsjmp_nonIAT_mask
       reinsjmp_IAT_or_RET_mask.

  Definition process_buffer := 
    ReinsVerifier.process_buffer 
       non_cflow_dfa
       dir_cflow_dfa
       reinsjmp_nonIAT_dfa
       reinsjmp_IAT_or_RET_dfa
       reinsjmp_IAT_CALL_dfa
       reinsjmp_nonIAT_mask
       reinsjmp_IAT_or_RET_mask.

  Fixpoint l2ll' {A} (n : nat) (l1 : list A) (l2 : list A) : list (list A) :=
    match l1 with
    | nil => match l2 with
             | nil => nil
             | _ => l2::nil
             end
    | a::l1' => match n with
                | O => (l2 ++ (a :: nil))%list :: (l2ll' 2 l1' nil)
                | S n' => l2ll' n' l1' (l2 ++ (a :: nil))
                end
    end. 

   Definition l2ll {A} (l : list A) : list (list A) :=
     l2ll' 2 l nil.

  (** * Definitions for aiding the verifier correctness proof *)

  (* Basic ideas of developing correctness proof of the fast verifier:
     (1) Define a pseudo instruction to be either a non-control-flow instruction, 
         a direct-jump instruction, or a nacljmp (which corresponds
         to two real instructions);
     (2) Formalize the invariant that should be satisfied between pseudo
         instructions: safeState, which says that pc is one of the
         start addresses of pseudo instructions.
     (3) Introduce a notion of safeInK (k, s, code), which means s will
         reach a safe state within k steps and it won't fail before reaching
         a safe state.
     (4) Show that any safe state also satifies safeInK(k,s,code) for some k>0.
         This proof is by case analysis over the current pseudo instruction. 
         If it is a non-control-flow or direct-jump instruction, then 
         safeInK(1,s,code). If it's a nacljmp, then safeInK(2,s,code). 
     (5) Show the initial state is a safe state. Then using (4), we know
         the initial state will reach a safe state s1; similarly, s1 will
         reach a safe state s2; ... By def of safeInK, none of these
         states (and the intermediate states) will fail.

     Note the above framework is general in that (i) it accommodates other
     pseudo instructions, not just nacljmp; (ii) it acccommodates trampolines;
     we just need an axiom assuming after jumping to a trampoline, the machine
     will come back to a safe state in a finite number of steps (that is,
     safeInK for some k) *)


  (* Checks whether the memory of s starting at addr_offset is equal to buffer *)
  (* In RockSalt:
  Definition eqMemBuffer (buffer: list int8) (s: rtl_state) (addr_offset: int32) :=
    Z_of_nat (length buffer) <= w32modulus /\
    (forall i, (i < length buffer)%nat
      -> nth i buffer Word.zero = (AddrMap.get (addr_offset +32_n i) (rtl_memory s))).*)
  Definition eqMemBuffer (buffer: list (list int8)) (s: rtl_state) (addr_offset: int32) :=
    Z_of_nat (length buffer) <= w32modulus /\
    (forall i, (i < (length buffer))%nat
      -> nth i (list_flatten buffer) Word.zero = (AddrMap.get (addr_offset +32_n i) (rtl_memory s))).


  (* note: needed adjustments if consider the trampoline area *)
  (* note: the range of addresses in the code segment is [CStart s, CStart s + Climit s],
     the length of the code segment is CLimit s + 1 *)
  (* In RockSalt:
  Definition codeLoaded (buffer: list int8) (s:rtl_state) := 
    eqMemBufferRockSalt buffer s (CStart s) /\ 
    Z_of_nat (length buffer) = unsigned (CLimit s) + 1. *)
  Definition codeLoaded (buffer: list (list int8)) (s:rtl_state) := 
    eqMemBuffer buffer s (CStart s) /\ 
    Z_of_nat (length buffer) = unsigned (CLimit s) + 1.


  (* todo: deal with trampolines
  (* Checks if the buffer agrees with the code regon in the state*)
  Definition eqCode_after_trampoline (buffer: list int8) (r: rtl_state) :=
    eqMemBuffer buffer r ((Word.add (CStart r) trampoline_limit)) /\
      ltu trampoline_limit (CLimit r) = true /\
      trampoline_limit +32_n (length buffer) = CLimit r.*)


  (** Check (1) segments do not wrap around the 32-bit address space;
      (2) code segment is disjoint from stack and data segments; *)
  (* C-Code, D-Data, S-Stack, E- , G- *)
  (* CHANGE : check whether changed segments are allowed in Reins *)
  Definition checkSegments (s: rtl_state) := 
    (checkNoOverflow (CStart s) (CLimit s) &&
      checkNoOverflow (DStart s) (DLimit s) &&
      checkNoOverflow (SStart s) (SLimit s) &&
      checkNoOverflow (EStart s) (ELimit s) &&
      checkNoOverflow (GStart s) (GLimit s) &&
      disjointRegions (CStart s) (CLimit s) (DStart s) (DLimit s) &&
      disjointRegions (CStart s) (CLimit s) (SStart s) (SLimit s) &&
      disjointRegions (CStart s) (CLimit s) (EStart s) (ELimit s) &&
      disjointRegions (CStart s) (CLimit s) (GStart s) (GLimit s))%bool.

  (* Invariants include the segment register starts and limits, and the code *)
  Definition Inv := 
     (fmap segment_register int32 * fmap segment_register int32 * list int8)%type.

  (* An appropriate state is one that segment registers are the same as the initial
     state and code is the same as the initial state *)
  Definition appropState (s:rtl_state) (inv:Inv) :=
    let (sregs, code) := inv in 
    let (sregs_starts, sregs_limits) := sregs in
      seg_regs_starts (rtl_mach_state s) = sregs_starts /\
      seg_regs_limits (rtl_mach_state s) = sregs_limits /\
      codeLoaded (l2ll code) s /\
      checkSegments s = true.

  (* COMPILES TO HERE *)

  (* The invariant that should be satisfied between pseudo instructions*)
  (* CHANGE *)
  Definition safeState (s:rtl_state) (inv:Inv) :=
    let (sregs,  code) := inv in 
    let cpRes := checkProgram' (l2ll code) in
      appropState s inv /\
      fst cpRes = true /\
      (Int32Set.In (PC s) (snd cpRes) \/ ~ inBoundCodeAddr (PC s) s).

  (* state s does not step to a failed state *)
  Definition nextStepNoFail (s: rtl_state) := 
    forall s', step s <> (Fail_ans _, s').

  (* The initial state can reach a safe state within k steps; the
     definition does not assume the step relation is
     deterministic; so the initial state may reach a safe state
     in different number of steps along different paths *)
  Fixpoint safeInK (k:nat) (s:rtl_state) (inv:Inv) := 
    match k with 
      | O => False
      | S k => appropState s inv /\ nextStepNoFail s /\
        forall s', s ==> s' -> safeState s' inv \/ safeInK k s' inv
    end.

  Definition safeInSomeK (s:rtl_state) (inv:Inv) := 
    exists k, safeInK k s inv.

  (* An equivalence relation between states that says the code
     region is immutable *)
  (* Checks that two code regions are equal *)
  Definition eqCodeRegion (s s':rtl_state) :=
    CStart s = CStart s' /\ CLimit s = CLimit s' /\
    noOverflow ((CStart s)::(CLimit s)::nil) /\
    agree_over_addr_region (segAddrs CS s) s s'.

  (** Check region [start1, start1+limit1] is a subset of
     [start2, start2+limit2]; For simplicity, neither region can wrap
     around the 32-bit address space. *)
  Definition subsetRegion (start1 limit1 start2 limit2:int32) : bool :=
    andb (int32_lequ_bool start2 start1)
      (int32_lequ_bool (start1 +32 limit1) (start2 +32 limit2)).

  Definition goodDefaultPC (default_pc:int32) 
    (startAddrs: Int32Set.t) (codeSize:nat) :=
    Int32Set.In default_pc startAddrs \/ default_pc = int32_of_nat codeSize.

  (* Checks whether target is in startAddrs or is aligned *)
  Definition goodJmpTarget (target:int32) (startAddrs: Int32Set.t) :=
    Int32Set.mem target startAddrs  || aligned_bool target.

  (* Direct jumps, checking if they are good *)
  Definition goodJmp (ins:instr) (default_pc:int32) (startAddrs: Int32Set.t) := 
    match ins with
      | JMP true false (Imm_op disp) None => 
        goodJmpTarget (default_pc +32 disp) startAddrs
      | Jcc ct disp => goodJmpTarget (default_pc +32 disp) startAddrs
      | CALL true false (Imm_op disp) None => 
        goodJmpTarget (default_pc +32 disp) startAddrs
      | _ => false
    end.

  (** * Fast verifier correctness proof *)
  
  (** ** Auxliary lemmas about lists, skipn, and firstn *)

  Lemma nth_nil : forall (A:Type) n (default:A),
    nth n nil default = default.
  Proof. destruct n; prover. Qed.

  Lemma length_cons : forall (A:Type) (x:A) l,
    length (x :: l) = S (length l).
  Proof. trivial. Qed.

  Lemma skipn_map: forall n (A B:Type) (l:list A) (f: A -> B) ,
    List.map f (skipn n l) = skipn n (List.map f l).
  Proof. induction n. prover.
    destruct l; prover.
  Qed.

  Lemma skipn_nth : forall (A:Type) n k  (l:list A) default,
    nth n (skipn k l) default = nth (n+k)%nat l default.
  Proof. induction k. rewrite plus_0_r. prover.
    destruct l. 
      intros. compute [skipn]. do 2 rewrite nth_nil. trivial.
      intros. rewrite cons_nth by omega.
      assert (n + S k - 1 = n + k)%nat by omega.
      rewrite H. simpl. apply IHk.
  Qed.

  Lemma skipn_length : forall n (A:Type) (l:list A),
    (n < length l -> length (skipn n l) + n = length l)%nat.
  Proof. induction n. prover.
    Case "S n". intros.
      destruct l. prover.
      simpl. erewrite <- IHn with (l:=l) by prover.
      omega.
  Qed.

  Lemma skipn_nil : forall n (A:Type) (l:list A),
    (n >= length l)%nat -> skipn n l = nil.
  Proof. induction n. 
    Case "n=0". destruct l; prover.
    Case "S n". intros. destruct l. prover.
      simpl. apply IHn. prover.
  Qed.

  Lemma skipn_length_leq : forall n (A:Type) (l:list A),
    (length (skipn n l) <= length l)%nat.
  Proof. intros.
    destruct (le_or_lt (length l) n).
    Case "length l <= n".
      assert (n >= length l)%nat by omega.
      apply skipn_nil in H0. prover.
    Case "n < length l".
      apply skipn_length in H. omega.
  Qed.

  Lemma skipn_length_geq : forall n (A:Type) (l:list A),
    (length (skipn n l) + n >= length l)%nat.
  Proof. induction n. prover.
    intros. destruct l. prover.
    simpl. generalize (IHn _ l). intros. omega.
  Qed.

  Lemma skipn_list_app : forall (A:Type) n (l1 l2:list A),
    length l1 = n -> skipn n (l1 ++ l2) = l2.
  Proof. induction n. destruct l1; prover.
    destruct l1. prover.
      intros.
      rewrite <- app_comm_cons.
      simpl. f_equal. auto.
  Qed.

  Lemma firstn_list_app : forall (A:Type) n (l1 l2:list A),
    length l1 = n -> firstn n (l1 ++ l2) = l1.
  Proof. induction n. destruct l1; prover.
    destruct l1. prover.
      intros.
      rewrite <- app_comm_cons.
      simpl. f_equal. auto.
  Qed.
  
  Lemma firstn_S_cons : forall (A:Type) n (x:A) l, 
    firstn (S n) (x :: l) = x :: firstn n l.
  Proof. intros. trivial. Qed.

  Lemma nth_firstn : forall n (A:Type) i (l:list A) default,
    (i < n)%nat -> nth i (firstn n l) default = nth i l default.
  Proof. induction n. intros. contradict H; prover.
    destruct l. prover.
      destruct i; prover.
  Qed.

  Lemma firstn_twice_eq : forall (A:Type) n m (l:list A),
    (n <= m)%nat -> firstn n (firstn m l) = firstn n l. 
  Proof. induction n. prover.
    intros. destruct m. prover.
      destruct l. prover.
        repeat (rewrite firstn_S_cons).
        f_equal. eapply IHn. omega.
  Qed.

  Lemma firstn_map : forall (A B:Type) n (f: A -> B) (l:list A),
    firstn n (List.map f l) = List.map f (firstn n l).
  Proof. induction n. prover.
    destruct l; prover.
  Qed.

  (** ** Properties of codeLoaded *)
  (* Our code segment will not be greater than 2^32 *) 
  Lemma codeLoaded_length : forall code s,
    codeLoaded code s -> Z_of_nat (length code) <= w32modulus.
  Proof. unfold codeLoaded. intros.
    destruct H. int32_simplify. omega.
  Qed.

  (* If RTL state has code segment loaded, basically says it resides in memory *)
  (* If you find the ith element in code list, it's also in memory *)
  Lemma codeLoaded_lookup : forall code s i,
    codeLoaded code s -> (i < length code)%nat
      -> nth i (list_flatten code) Word.zero = AddrMap.get (CStart s +32_n i) (rtl_memory s).
  Proof. unfold codeLoaded, eqMemBuffer. intros.
    destruct H as [[H10 H11] H12].    
    apply H11. trivial.
  Qed.


  (** ** Properties of dfa_recognize *)
  (*  *)
  Local Ltac dfaprover :=
     simtuition ltac:(auto with *); autorewrite with dfaRecDB in *;
       rewriter; simtuition ltac:(auto with *).

  Require Coqlib.
  Hint Rewrite minus_diag : dfaRecDB.

  (* By going thru dfa_loop, you can't consume a negative number of bytes *)
  (* count1 - count = #of bytes consumed *)
  Lemma dfa_loop_inv : forall numOfTokens dfa ts s count count1 ts1,
      dfa_loop numOfTokens dfa s count ts = Some (count1, ts1) ->
        ts1 = List.skipn (count1-count) ts /\ (count1 >= count)%nat /\
        (length ts = count1 - count + length ts1)%nat.
  Proof. induction ts; intros; simpl in H.
        Case "ts=nil". 
          destruct_head in H; [dfaprover | discriminate].
        Case "a::ts".
          destruct_head in H.
            dfaprover.
            apply IHts in H.
            assert (count1 - S count = count1 - count - 1)%nat by intuition.
            rewrite Coqlib.skipn_gt_0; dfaprover.
  Qed.

  (* Same invariant, but simpler *)
  Lemma dfa_recognize_inv : forall numOfTokens dfa ts len ts',
      dfa_recognize numOfTokens dfa ts = Some (len, ts')
        -> (ts' = List.skipn len ts /\ length ts = len + length ts')%nat.
  Proof. unfold dfa_recognize.
        intros. apply dfa_loop_inv in H. 
        rewrite <- minus_n_O in H. prover.
  Qed.

  (** ** Properties of safeInK and safeInSomeK *)
  Lemma safeInSomeK_no_fail : forall s inv,
    safeInSomeK s inv -> nextStepNoFail s.
  Proof. unfold safeInSomeK. intros. destruct H as [k H]. destruct k; prover. Qed.
  
  Lemma safeInK_step_dichotomy : forall k s inv s',
    safeInK k s inv -> s ==> s' -> safeState s' inv \/ safeInSomeK s' inv.
  Proof. destruct k. prover.
    intros. simpl in H.
    assert (safeState s' inv \/ safeInK k s' inv) by prover.
    destruct H1. prover. 
      right. unfold safeInSomeK. exists k; assumption.
  Qed.

  Lemma safeInK_intro_one : forall s inv,
    appropState s inv -> nextStepNoFail s 
      -> (forall s', s ==> s' -> safeState s' inv)
      -> safeInK 1%nat s inv.
  Proof. prover. Qed.

  (** ** Properties of subsetRegion *)
  Ltac subsetRegion_intro_tac :=
    unfold subsetRegion; bool_intro_tac.

  (* subsetRegion works like it is supposed to *)
  Lemma subsetRegion_sound : forall start1 limit1 start2 limit2,
    noOverflow (start1::limit1::nil) -> noOverflow (start2::limit2::nil)
      -> subsetRegion start1 limit1 start2 limit2 = true
      -> Ensembles.Included _ (addrRegion start1 limit1)
           (addrRegion start2 limit2).
  Proof.
  Admitted.

 (*unfold subsetRegion, Ensembles.Included. intros.
   unfold Ensembles.In, addrRegion in *.
   bool_elim_tac.
   destruct H2 as [i [H6 H8]].
   exists (start1 -32 start2 +32 i).
   split. unfold w32add. rewrite <- add_assoc. 
     rewrite <- add_sub_assoc. rewrite sub_add_l.
     rewrite sub_idem. rewrite zero_add. assumption.
   int32_simplify; omega.
  Qed.*)

  (** ** Properties of checkSegments *)
  (* If two segments are identical, then if one passes checkSegments *)
  (* the other does as well *)

  Lemma checkSegments_inv : forall (s s':rtl_state),
    Same_Seg_Regs_Rel.brel s s'
      -> checkSegments s = true
      -> checkSegments s' = true.
  Proof. unfold Same_Seg_Regs_Rel.brel, checkSegments.  intros.
    bool_elim_tac. bool_intro_tac; prover.
  Qed.

  (* RTL A is a transition from one state to another *)
  (* Given the state monad RTL, by taking a step, you do not change the *)
  (* segment registers *)

  Lemma checkSegments_inv2 : forall (A:Type) (c:RTL A) (s s':rtl_state) (v':A),
    same_seg_regs c
      -> c s = (Okay_ans v', s')
      -> checkSegments s = true
      -> checkSegments s' = true.
  Proof. unfold same_seg_regs.  intros.
    eapply checkSegments_inv; try eassumption. eauto.
  Qed.

  Ltac checkSegments_backward :=
    match goal with
      | [H: ?c1 ?s = (Okay_ans _, ?s') |- checkSegments ?s' = true] => 
        eapply checkSegments_inv2 with (c:=c1); 
          [same_seg_regs_tac | eassumption | idtac]
    end.

  Lemma checkSegments_disj_code_data : forall s,
    checkSegments s = true
      -> Ensembles.Disjoint _ (segAddrs CS s) (segAddrs DS s).
  Proof. intros. unfold checkSegments in H. repeat bool_elim_tac.
    apply disjointRegions_sound; try assumption.
  Qed.

  Lemma checkSegments_disj_code_stack : forall s,
    checkSegments s = true
      -> Ensembles.Disjoint _ (segAddrs CS s) (segAddrs SS s).
  Proof. intros. unfold checkSegments in H. repeat bool_elim_tac.
    apply disjointRegions_sound; try assumption.
  Qed.

  Lemma checkSegments_disj_code_eseg : forall s,
    checkSegments s = true
      -> Ensembles.Disjoint _ (segAddrs CS s) (segAddrs ES s).
  Proof. intros. unfold checkSegments in H. bool_elim_tac.
    apply disjointRegions_sound; try assumption.
  Qed.

  Lemma checkSegments_disj_code_gseg : forall s,
    checkSegments s = true
      -> Ensembles.Disjoint _ (segAddrs CS s) (segAddrs GS s).
  Proof. intros. unfold checkSegments in H. bool_elim_tac.
    apply disjointRegions_sound; try assumption.
  Qed.

  (** ** Properties about eqCodeRegion *)
  (* Checks that for two RTL states, they have the same code region limits *) 
  Lemma eqCodeRegion_intro : forall s s',
      Same_Seg_Regs_Rel.brel s s'
        -> checkSegments s = true
        -> (agree_outside_addr_region (segAddrs DS s) s s' \/
            agree_outside_addr_region (segAddrs SS s) s s' \/
            agree_outside_addr_region (segAddrs GS s) s s' \/
            agree_outside_addr_region (segAddrs ES s) s s')
        -> eqCodeRegion s s'. 
  Proof. unfold eqCodeRegion. intros. dupHyp H0.
    unfold checkSegments in H0.
    bool_elim_tac.
    unfold Same_Seg_Regs_Rel.brel in H.
    split. prover. 
    split. prover.
    split. apply checkNoOverflow_equiv_noOverflow. trivial.
    destruct H1.
      Case "agree_outside_seg DS c".
        eapply agree_over_outside. 
          apply checkSegments_disj_code_data; assumption.
          trivial.
      destruct H1.
      Case "agree_outside_seg SS c".
        eapply agree_over_outside. 
          apply checkSegments_disj_code_stack; assumption.
          trivial.
      destruct H1.
      Case "agree_outside_seg GS c".
        eapply agree_over_outside. 
          apply checkSegments_disj_code_gseg; assumption.
          trivial.
      Case "agree_outside_seg ES c".
        eapply agree_over_outside. 
          apply checkSegments_disj_code_eseg; assumption.
          trivial.
  Qed.
  
  (* If a state has good segments, then by taking an RTL step,
     then the states agree on the same code region *)  
  Lemma eqCodeRegion_intro2 : 
    forall (A:Type) (c:RTL A) (s s':rtl_state) (v':A),
      checkSegments s = true -> c s = (Okay_ans v', s')
        -> same_seg_regs c
        -> (agree_outside_seg DS c \/ agree_outside_seg SS c \/
            agree_outside_seg GS c \/ agree_outside_seg ES c)
        -> eqCodeRegion s s'. 
  Proof. intros.
    apply eqCodeRegion_intro.
    eauto using H1. assumption.
    destruct H2. left. eapply H2. eassumption.
    destruct H2. right. left. eapply H2. eassumption.
    destruct H2. right. right. left. eapply H2. eassumption.
      right. right. right. eapply H2. eassumption.
  Qed.

  (* reflexive lemma, the code region of s agrees with the code 
     region of s *)
  Lemma eqCodeRegion_refl : forall s,
    checkSegments s = true -> eqCodeRegion s s.
  Proof. intros. unfold eqCodeRegion. repeat split; try congruence.
    unfold checkSegments in H. bool_elim_tac.
    apply checkNoOverflow_equiv_noOverflow. assumption.
  Qed.
 
  (* Transitivity *)
  Lemma eqCodeRegion_trans : forall s1 s2 s3,
    eqCodeRegion s1 s2 -> eqCodeRegion s2 s3
      -> eqCodeRegion s1 s3.
  Proof. unfold eqCodeRegion; intros. 
    repeat genSimpl; try congruence.
    assert (segAddrs CS s1 = segAddrs CS s2) as H10.
      unfold segAddrs. congruence.
    rewrite H10 in *.
    eapply agree_over_addr_region_trans; eassumption.
  Qed.

  (** ** Properties abour parse_instr *)
  Opaque Decode.X86_PARSER.parse_byte.

  (* Give it a chunk of memory and it gives the instruction at that location
     if you apply 'this' function it will not change the RTL state *)
  Lemma parse_instr_aux_same_state : forall n pc len ps,
    same_rtl_state (parse_instr_aux n pc len ps).
  Proof. unfold same_rtl_state.
    induction n. intros. discriminate.
    intros. simpl in H.
    remember_destruct_head in H as pr.
    destruct l. eauto. prover.
  Qed.

  Lemma parse_instr_same_state : forall pc, same_rtl_state (parse_instr pc).
  Proof. unfold same_rtl_state, parse_instr. intros.
    rtl_okay_elim.  eapply parse_instr_aux_same_state. eassumption.
  Qed.

  Lemma parse_instr_aux_len : forall n pc len ps s pi len' s',
    parse_instr_aux n pc len ps s = (Okay_ans (pi, len'), s')
      -> Zpos len <= Zpos len' < Zpos len + Z_of_nat n.
  Proof. induction n. discriminate.
    intros. simpl in H.
    remember_destruct_head  in H as pr.
    destruct l. 
    Case "l=nil". 
      use_lemma IHn by eassumption. 
      rewrite Zpos_plus_distr in H0. 
      rewrite inj_S. omega.
    Case "l>>nil". inversion_clear H. 
      rewrite inj_S. omega.
  Qed.  

  Lemma parse_instr_len : forall pc s pi len s',
    parse_instr pc s = (Okay_ans (pi, len), s') -> 1 <= Zpos len < 16.
  Proof. unfold parse_instr. intros.
    rtl_okay_elim. apply parse_instr_aux_len in H. simpl in H. omega.
  Qed.

  Lemma parse_instr_aux_same_seg_regs : forall n loc len ps,
     same_seg_regs (parse_instr_aux n loc len ps).
  Proof. unfold parse_instr_aux.
    induction n; intros. same_seg_regs_tac.
      fold parse_instr in *. same_seg_regs_tac.
  Qed.

  Hint Immediate parse_instr_aux_same_seg_regs : same_seg_regs_db.
(*
  Lemma parse_instr_aux_no_fail : forall n loc len ps,
     no_fail (parse_instr_aux n loc len ps).
  Proof. unfold parse_instr_aux.
    induction n; intros. no_fail_tac.
      fold parse_instr in *. no_fail_tac.
  Qed.

  Hint Immediate parse_instr_aux_no_fail : no_fail_db.
*)
  Lemma parse_instr_aux_code_inv : forall s1 s1' s2 n pc len len' pi ps,
    eqCodeRegion s1 s2
      -> parse_instr_aux n pc len ps s1 = (Okay_ans (pi, len'), s1')
      -> Ensembles.Included _ (addrRegion pc (repr (Zpos len' - Zpos len)))
           (segAddrs CS s1)
      -> noOverflow (pc :: repr (Zpos len' - Zpos len) ::nil)
      -> Zpos len' - Zpos len < w32modulus
      -> parse_instr_aux n pc len ps s2 = (Okay_ans (pi, len'), s2).
  Proof. induction n; intros.
    Case "n=0". discriminate.
    Case "S n". simpl in H0. simpl.
      assert (AddrMap.get pc (rtl_memory s1)
                = AddrMap.get pc (rtl_memory s2)) as H10.
        unfold eqCodeRegion in H. repeat genSimpl.
        apply H6. apply H1. apply addrRegion_start_in.
      rewrite <- H10.
      remember_destruct_head as pr.
      destruct l. 
      SCase "l=nil".
        use_lemma parse_instr_aux_len by eassumption.
        assert (noOverflow (add pc (repr 1)::repr (Zpos len' - (Zpos len + 1))::nil))
          by int32_prover.
        eapply IHn; try eassumption.
        apply included_trans with (r2:= addrRegion pc (repr (Zpos len' - Zpos len))).
          apply subsetRegion_sound; try assumption.
            subsetRegion_intro_tac; int32_prover.
            assumption.
          rewrite Zpos_plus_distr; omega.
      SCase "l<>nil". prover.
  Qed.

  (* this can be proved as a corollary of the above lemma, given that
     n -1 < Zpos len' - Zpos len
  Lemma parse_instr_aux_code_inv_2 : forall s1 s1' s2 n pc len res ps,
    eqCodeRegion s1 s2
      -> Ensembles.Included _ (addrRegion pc (int32_of_nat (n-1)))
           (segAddrs CS s1)
      -> noOverflow (pc::int32_of_nat (n-1)::nil)
      -> Z_of_nat n <= w32modulus
      -> parse_instr n pc len ps s1 = (Okay_ans res, s1')
      -> parse_instr n pc len ps s2 = (Okay_ans res, s2).
  *)

  Lemma parse_instr_code_inv : forall s1 s1' s2 pc len' pi,
    eqCodeRegion s1 s2
      -> parse_instr pc s1 = (Okay_ans (pi, len'), s1')
      -> Ensembles.Included _ 
           (addrRegion (CStart s1 +32 pc) (repr (Zpos len' - 1)))
           (segAddrs CS s1)
      -> noOverflow ((CStart s1 +32 pc) :: repr (Zpos len' - 1) ::nil)
      -> Zpos len' - 1 < w32modulus
      -> parse_instr pc s2 = (Okay_ans (pi, len'), s2).
  Proof. unfold parse_instr. intros.
    dupHyp H. unfold eqCodeRegion in H. simplHyp.
    rtl_okay_elim. rtl_okay_intro.
    compute [get_location look]. rewrite  <- H. 
    eapply parse_instr_aux_code_inv; eassumption.
  Qed.

  Transparent Decode.X86_PARSER.parse_byte.

  (** ** Misc. lemmas *)

  Lemma Int32Set_in_dichotomy : forall x y A B,
    Int32Set.In x (Int32Set.diff A B)
      -> (x=y \/ Int32Set.In x (Int32Set.diff A (Int32Set.add y B))).
  Proof. intros. destruct (eq_dec x y). prover.
      rewrite Int32Set.diff_spec in *. rewrite Int32Set.add_spec.
      int32_to_Z_tac. prover.
  Qed.

  (** ** Properties of process_buffer *)

  (* process buffer prover *)
  (*Local Ltac pbprover :=
    simtuition ltac:(auto with arith zarith); autorewrite with pbDB in *; 
      rewriter; simtuition ltac:(auto with arith zarith). *)
  
  Hint Rewrite Int32Set.diff_spec : pbDB.
  Hint Rewrite Int32SetFacts.empty_iff : pbDB.

  Lemma process_buffer_aux_nil: forall start n currStartAddrs currJmpTargets,
    process_buffer_aux start n nil (currStartAddrs, currJmpTargets) = 
    Some (currStartAddrs, currJmpTargets).
  Proof. destruct n; auto. Qed.
  Hint Rewrite process_buffer_aux_nil : pbDB.

(*
  Lemma process_buffer_aux_nil_contra :
    forall start n currStartAddrs currJmpTargets allStartAddrs allJmpTargets pc
      (p:Prop),
    process_buffer_aux start n nil (currStartAddrs, currJmpTargets) =
      Some(allStartAddrs, allJmpTargets)
      -> Int32Set.In pc (Int32Set.diff allStartAddrs currStartAddrs)
      -> p.
  Proof. intros. pbprover. Qed.
*)

  (** a special tactic for performing case analysis over process_buffer_aux *)
  (* CHANGE *)
  Ltac process_buffer_aux_Sn_tac := 
    match goal with
      | [H: process_buffer_aux ?start (S ?n) ?tokens (?cSA, ?cJT)
          = Some (?aSA, ?aJT) |- _] =>
        simpl in H;
        repeat match goal with
           | [ H: match ?X with Some _ => _ | None => _ end = _ |- _] =>
                 match X with
                   | dfa_recognize _ non_cflow_dfa ?T => 
                     let dfa := fresh "d1" in let len := fresh "len1" in 
                       let remaining := fresh "remaining1" in
                         remember_rev X as dfa; destruct dfa as [(len, remaining)|]
                   | dfa_recognize _ dir_cflow_dfa ?T => 
                     let dfa := fresh "d2" in let len := fresh "len2" in 
                       let remaining := fresh "remaining2" in
                         remember_rev X as dfa; destruct dfa as [(len, remaining)|]
                   | dfa_recognize _ nacljmp_dfa ?T => 
                     let dfa := fresh "d3" in let len := fresh "len3" in 
                       let remaining := fresh "remaining3" in
                         remember_rev X as dfa; destruct dfa as [(len, remaining)|]
                 end
               end; try (discriminate H)
    end.

  Ltac process_buffer_aux_tac := 
    match goal with
      | [H: process_buffer_aux ?start ?n ?tokens (?cSA, ?cJT)
          = Some (?aSA, ?aJT) |- _] =>
      let t := fresh "t1" in let tokens' := fresh "tokens1" in
        destruct tokens as [| t tokens'];
          [idtac | process_buffer_aux_Sn_tac]
    end.


  (* Some arithmetic facts used many times in the proofs about process_buffer *)
  Lemma process_buffer_arith_facts : 
    forall start len (tokens remaining:list token_id),
    noOverflow (start :: int32_of_nat (length tokens -1)%nat :: nil)
      -> Z_of_nat (length tokens) <= w32modulus
      -> (length tokens >=1)%nat
      -> (length remaining >=1)%nat
      -> (length tokens = len + length remaining)%nat
      -> noOverflow (start :: int32_of_nat len :: nil) /\
         noOverflow ((start +32_n len)
           :: int32_of_nat (length remaining - 1) :: nil) /\
         Z_of_nat (length remaining) <= w32modulus.
  Proof. intros. int32_simplify. lia. Qed.

  Lemma process_buffer_aux_addrRange :
   forall n start tokens currStartAddrs currJmpTargets allStartAddrs allJmpTargets pc,
    process_buffer_aux start n tokens (currStartAddrs, currJmpTargets) =
      Some(allStartAddrs, allJmpTargets)
      -> noOverflow (start :: int32_of_nat (length tokens - 1) :: nil)
      -> Z_of_nat (length tokens) <= w32modulus
      -> Int32Set.In pc (Int32Set.diff allStartAddrs currStartAddrs)
      -> unsigned start <= unsigned pc < unsigned start + Z_of_nat (length tokens).
  Proof. induction n. intros.
    Case "n=0". intros. destruct tokens; pbprover.
    Case "S n". intros.
      destruct tokens as [| t tokens']. pbprover.
      SCase "tokens<>nil".
        assert (length (t::tokens') >= 1)%nat by (simpl; omega).
        destruct (@Int32Set_in_dichotomy pc start _ _ H2). 
        SSCase "pc=start".  rewrite H4. omega.
        SSCase "pc in (allStartAddrs - ({start} \/ currStartAddrs)".
         process_buffer_aux_Sn_tac.
         SSSCase "nacljmp_dfa matches". clear Hd1 Hd2.
           assert (length remaining3 > 0)%nat by (destruct remaining3; pbprover).
           use_lemma dfa_recognize_inv by eassumption. simplHyp.
           use_lemma process_buffer_arith_facts by eassumption. simplHyp.
           apply IHn with (pc:=pc) in H; try (assumption || omega). clear IHn. 
           int32_simplify. lia.
        SSSCase "non_cflow_dfa matches". clear Hd2 Hd3.
           assert (length remaining1 > 0)%nat by (destruct remaining1; pbprover).
           use_lemma dfa_recognize_inv by eassumption. simplHyp.
           use_lemma process_buffer_arith_facts by eassumption. simplHyp.
           apply IHn with (pc:=pc) in H; try (assumption || omega). clear IHn.
           int32_simplify. lia.
        SSSCase "dir_cflow_dfa matches". clear Hd1 Hd3.
           destruct_head in H; try discriminate.
           assert (length remaining2 > 0)%nat by (destruct remaining2; pbprover).
           use_lemma dfa_recognize_inv by eassumption. simplHyp.
           use_lemma process_buffer_arith_facts by eassumption. simplHyp.
           apply IHn with (pc:=pc) in H; try (assumption || omega). clear IHn.
           int32_simplify. lia.
  Qed.

  Lemma process_buffer_addrRange : forall buffer startAddrs jmpTargets pc,
    process_buffer buffer = Some (startAddrs, jmpTargets)
      -> Z_of_nat (length buffer) <= w32modulus
      -> Int32Set.In pc startAddrs
      -> 0 <= unsigned pc < Z_of_nat (length buffer).
  Proof. intros. unfold process_buffer, FastVerifier.process_buffer in H.
    assert (length (List.map byte2token buffer) = length buffer) as H10
      by (apply list_length_map).
    assert (noOverflow (repr 0 ::
      int32_of_nat (Datatypes.length (List.map byte2token buffer) - 1) :: nil)).
      rewrite H10. 
      destruct buffer as [| b buffer']. simpl. 
        int32_simplify. simpl. rewrite int32_modulus_constant. omega.
        assert (length (b::buffer') >= 1)%nat by (simpl; omega).
        int32_prover.
    apply process_buffer_aux_addrRange with (pc:=pc) in H;
      [idtac | assumption | (rewrite list_length_map; trivial) | pbprover].
    rewrite list_length_map in *; int32_prover.
  Qed.

  Hint Rewrite Zminus_diag:pbDB.
  
  Lemma Int32Set_subset_add : forall x s,
    Int32Set.Subset s (Int32Set.add x s).
  Proof. unfold Int32Set.Subset.
    generalize Int32Set.add_spec. prover.
  Qed.

  Lemma process_buffer_aux_subset : 
    forall n start tokens currStartAddrs currJmpTargets allStartAddrs allJmpTargets,
      process_buffer_aux start n tokens (currStartAddrs, currJmpTargets) =
        Some (allStartAddrs, allJmpTargets)
        -> Int32Set.Subset currStartAddrs allStartAddrs /\
           Int32Set.Subset currJmpTargets allJmpTargets.
  Proof. induction n. intros.
    Case "n=0". intros. destruct tokens; pbprover.
    Case "S n". intros.
      destruct tokens as [| t tokens']. pbprover.
      SCase "tokens<>nil".
        assert (length (t::tokens') >= 1)%nat by (simpl; omega).
        process_buffer_aux_Sn_tac.
        SSCase "nacljmp_dfa matches". clear Hd1 Hd2.
          use_lemma IHn by eassumption.
          simplHyp.
          split.
            eapply Int32SetFacts.Subset_trans; [idtac | eassumption].
              apply Int32Set_subset_add.
            eapply Int32SetFacts.Subset_trans; [idtac | eassumption].
              apply Int32SetFacts.Subset_refl.
        SSCase "non_cflow_dfa matches". clear Hd2 Hd3.
          use_lemma IHn by eassumption.
          simplHyp.
          split.
            eapply Int32SetFacts.Subset_trans; [idtac | eassumption].
              apply Int32Set_subset_add.
            eapply Int32SetFacts.Subset_trans; [idtac | eassumption].
              apply Int32SetFacts.Subset_refl.
        SSCase "dir_cflow_dfa matches". clear Hd1 Hd3.
          destruct_head in H; try discriminate.
          use_lemma IHn by eassumption.
          simplHyp.
          split.
            eapply Int32SetFacts.Subset_trans; [idtac | eassumption].
              apply Int32Set_subset_add.
            eapply Int32SetFacts.Subset_trans; [idtac | eassumption].
              apply Int32Set_subset_add.
  Qed.

  Lemma process_buffer_aux_start_in : 
    forall n start tokens currStartAddrs currJmpTargets allStartAddrs allJmpTargets,
      process_buffer_aux start n tokens (currStartAddrs, currJmpTargets) =
        Some(allStartAddrs, allJmpTargets)
        -> (length (tokens) > 0)%nat
        -> Int32Set.In start allStartAddrs.
  Proof. intros. destruct tokens as [| t tokens']. 
    Case "tokens=nil". simpl in H0. contradict H0. omega.
    Case "tokens<>nil".
      assert (length (t::tokens') >= 1)%nat by (simpl; omega).
      destruct n.
      SCase "n=0". discriminate.
      SCase "S n".
        process_buffer_aux_Sn_tac.
        SSCase "nacljmp_dfa matches". clear Hd1 Hd2.
          use_lemma process_buffer_aux_subset by eassumption.
          unfold Int32Set.Subset in *.
          apply H2. apply Int32SetFacts.add_1. apply int_eq_refl.
        SSCase "non_cflow_dfa matches". clear Hd2 Hd3.
          use_lemma process_buffer_aux_subset by eassumption.
          unfold Int32Set.Subset in *.
          apply H2. apply Int32SetFacts.add_1. apply int_eq_refl.
        SSCase "dir_cflow_dfa matches". clear Hd1 Hd3.
          destruct_head in H; try discriminate.
          use_lemma process_buffer_aux_subset by eassumption.
          unfold Int32Set.Subset in *.
          apply H2. apply Int32SetFacts.add_1. apply int_eq_refl.
  Qed.

  Lemma process_buffer_start_in : forall code startAddrs jmpTargets,
      process_buffer code =  Some (startAddrs, jmpTargets)
        -> (length (code) > 0)%nat
        -> Int32Set.In int32_zero startAddrs.
  Proof. unfold process_buffer, FastVerifier.process_buffer; intros.
    eapply process_buffer_aux_start_in. eassumption.
      rewrite list_length_map. assumption.
  Qed.


  Definition goodDefaultPC_aux (default_pc start:int32) 
    (startAddrs: Int32Set.t) (codeSize:nat) :=
    Int32Set.In default_pc startAddrs \/ default_pc = start +32_n codeSize.


  (* Capture the notion that all indirect-jmp targets are in jmpTargets *)
  Definition includeAllJmpTargets (start:int32) (len:nat) 
    (tokens:list token_id) (jmpTargets:Int32Set.t) := 
    match (parseloop Decode.X86_PARSER.initial_parser_state 
            (List.map token2byte (firstn len tokens))) with
      | Some ((_, JMP true false (Imm_op disp) None), _) => 
        Int32Set.In (start +32_n len +32 disp) jmpTargets
      | Some ((_, Jcc ct disp), _) => 
        Int32Set.In (start +32_n len +32 disp) jmpTargets
      | Some ((_, CALL true false (Imm_op disp) None), _) => 
        Int32Set.In (start +32_n len +32 disp) jmpTargets
      | _ => True
    end.

  Lemma extract_disp_include : forall start len tokens disp S,
    extract_disp (List.map token2byte (firstn len tokens)) = Some disp
      -> Int32Set.In (start +32_n len +32 disp) S
      -> includeAllJmpTargets start len tokens S.
  Proof. unfold extract_disp, includeAllJmpTargets; intros.
    destruct_head. destruct p as [[pre ins] _].
    destruct ins; try trivial.
      Case "JMP".
        destruct near; try congruence.
        destruct absolute; try congruence.
        destruct op1; try congruence.
        destruct sel; congruence.
      Case "Jcc". congruence.
      Case "Call".
        destruct near; try congruence.
        destruct absolute; try congruence.
        destruct op1; try congruence.
        destruct sel; congruence.
      trivial.
  Qed.  


  Lemma Int32Set_in_subset : forall x s s',
    Int32Set.In x s -> Int32Set.Subset s s' -> Int32Set.In x s'.
  Proof. unfold Int32Set.Subset. intros. auto. Qed.

  Lemma process_buffer_aux_inversion :
   forall n start tokens currStartAddrs currJmpTargets allStartAddrs allJmpTargets,
    process_buffer_aux start n tokens (currStartAddrs, currJmpTargets) =
      Some(allStartAddrs, allJmpTargets)
      -> noOverflow (start :: int32_of_nat (length tokens - 1) :: nil)
      -> Z_of_nat (length tokens) <= w32modulus
      -> forall pc:int32, Int32Set.In pc (Int32Set.diff allStartAddrs currStartAddrs)
           -> exists tokens', exists len, exists remaining,
                tokens' = (List.skipn (Zabs_nat (unsigned pc - unsigned start)) 
                             tokens) /\
                goodDefaultPC_aux (pc +32_n len) start allStartAddrs 
                  (length tokens) /\
                (dfa_recognize 256 non_cflow_dfa tokens' = Some (len, remaining) \/
                 (dfa_recognize 256 dir_cflow_dfa tokens' = Some (len, remaining) /\
                  includeAllJmpTargets pc len tokens' allJmpTargets) \/
                 dfa_recognize 256 nacljmp_dfa tokens' = Some (len, remaining)).
(*  Admitted. *)
  Proof. induction n. intros.
    Case "n=0". intros. destruct tokens; pbprover.
    Case "S n". intros.
      process_buffer_aux_tac.
      SCase "tokens = nil". pbprover.
      SCase "tokens<>nil; nacljmp_dfa matches". clear Hd1 Hd2.
        use_lemma dfa_recognize_inv by eassumption. genSimpl.
        destruct (@Int32Set_in_dichotomy pc start _ _ H2). 
        SSCase "pc=start". subst pc. 
          assert (goodDefaultPC_aux (start +32_n len3) start allStartAddrs
                    (length (t1::tokens1))).
            destruct remaining3.
            SSSCase "remaining3=nil".
              assert (len3 = length (t1 ::tokens1)) by prover.
              right. prover.
            SSSCase "remaining3<>nil".
              left. eapply process_buffer_aux_start_in. 
              eassumption. simpl. omega.
          exists (t1::tokens1), len3, remaining3. pbprover.
        SSCase "pc in (allStartAddrs - ({start} \/ currStartAddrs)".
          assert (length (t1::tokens1) >= 1)%nat by (simpl; omega).
          assert (length remaining3 > 0)%nat by (destruct remaining3; pbprover).
          use_lemma (process_buffer_arith_facts start len3 (t1::tokens1) remaining3)
            by assumption.
          simplHyp.
          use_lemma process_buffer_aux_addrRange by eassumption.
          use_lemma IHn by eassumption.
          destruct H12 as [tokens'' [len [remaining [H20 [H21 H22]]]]].
          subst tokens''. rewrite H3 in H22. rewrite skipn_twice_eq in H22.
          int32_simplify.
          assert (Zabs_nat (unsigned pc - (unsigned start + Z_of_nat len3)) + len3 = 
                  Zabs_nat (unsigned pc - unsigned start))%nat as H30.
            apply inj_eq_rev; int32_simplify_in_goal; ring.
          rewrite H30 in H22.
          assert (goodDefaultPC_aux (pc +32_n len) start allStartAddrs
                    (length (t1 :: tokens1))).
            destruct H21. left. assumption.
              right. rewrite H4. rewrite <- add_repr. 
                unfold w32add at 2. rewrite <- add_assoc. 
              assumption.
          exists (skipn (Zabs_nat (unsigned pc -unsigned start)) (t1::tokens1)).
            exists len, remaining.
              split. trivial.
              split. assumption. assumption.
      SCase "tokens<>nil; non_cflow_dfa matches". clear Hd2 Hd3.
        use_lemma dfa_recognize_inv by eassumption. genSimpl.
        destruct (@Int32Set_in_dichotomy pc start _ _ H2). 
        SSCase "pc=start". subst pc. 
          assert (goodDefaultPC_aux (start +32_n len1) start allStartAddrs
                    (length (t1::tokens1))).
            destruct remaining1.
            SSSCase "remaining1=nil".
              assert (len1 = length (t1 ::tokens1)) by prover.
              right. prover.
            SSSCase "remaining3<>nil".
              left. eapply process_buffer_aux_start_in. 
              eassumption. simpl. omega.
          exists (t1::tokens1), len1, remaining1. pbprover.
        SSCase "pc in (allStartAddrs - ({start} \/ currStartAddrs)".
          assert (length (t1::tokens1) >= 1)%nat by (simpl; omega).
          assert (length remaining1 > 0)%nat by (destruct remaining1; pbprover).
          use_lemma (process_buffer_arith_facts start len1 (t1::tokens1) remaining1)
            by assumption.
          simplHyp.
          use_lemma process_buffer_aux_addrRange by eassumption.
          use_lemma IHn by eassumption.
          destruct H12 as [tokens'' [len [remaining [H20 [H21 H22]]]]].
          subst tokens''. rewrite H3 in H22. rewrite skipn_twice_eq in H22.
          int32_simplify.
          assert (Zabs_nat (unsigned pc - (unsigned start + Z_of_nat len1)) + len1 = 
                  Zabs_nat (unsigned pc - unsigned start))%nat as H30.
            apply inj_eq_rev; int32_simplify_in_goal; ring.
          rewrite H30 in H22. simplHyp.
          assert (goodDefaultPC_aux (pc +32_n len) start allStartAddrs
                    (length (t1 :: tokens1))).
            destruct H21. left. assumption.
              right. rewrite H4. rewrite <- add_repr. 
                unfold w32add at 2. rewrite <- add_assoc. 
              assumption.
          exists (skipn (Zabs_nat (unsigned pc -unsigned start)) (t1::tokens1)).
            exists len, remaining.
              split. trivial. split; assumption.
      SCase "tokens<>nil; dir_cflow_dfa matches". clear Hd1 Hd3.
        remember_destruct_head in H as ed; try discriminate.
        use_lemma dfa_recognize_inv by eassumption. genSimpl.
        destruct (@Int32Set_in_dichotomy pc start _ _ H2). 
        SSCase "pc=start". subst pc. 
          assert (goodDefaultPC_aux (start +32_n len2) start allStartAddrs
                    (length (t1::tokens1))).
            destruct remaining2.
            SSSCase "remaining2=nil".
              assert (len2 = length (t1 ::tokens1)) by prover.
              right. prover.
            SSSCase "remaining2<>nil".
              left. eapply process_buffer_aux_start_in. 
              eassumption. simpl. omega.
          use_lemma process_buffer_aux_subset by eassumption.
          assert (Int32Set.In (start +32_n len2 +32 i) allJmpTargets).
            apply Int32Set_in_subset 
              with (s:=(Int32Set.add (start +32_n len2 +32 i) currJmpTargets)).
            eapply Int32Set.add_spec. left. apply int_eq_refl.
            prover.
          exists (t1::tokens1), len2, remaining2.
            split. pbprover.
            split. assumption.
              right; left. split. assumption.
              eapply extract_disp_include; eassumption.
        SSCase "pc in (allStartAddrs - ({start} \/ currStartAddrs)".
          assert (length (t1::tokens1) >= 1)%nat by (simpl; omega).
          assert (length remaining2 > 0)%nat by (destruct remaining2; pbprover).
          use_lemma (process_buffer_arith_facts start len2 (t1::tokens1) remaining2)
            by assumption.
          simplHyp.
          use_lemma process_buffer_aux_addrRange by eassumption.
          use_lemma IHn by eassumption.
          destruct H12 as [tokens'' [len [remaining [H20 [H21 H22]]]]].
          subst tokens''. rewrite H3 in H22. rewrite skipn_twice_eq in H22.
          int32_simplify.
          assert (Zabs_nat (unsigned pc - (unsigned start + Z_of_nat len2)) + len2 = 
                  Zabs_nat (unsigned pc - unsigned start))%nat as H30.
            apply inj_eq_rev; int32_simplify_in_goal; ring.
          rewrite H30 in H22.
          assert (goodDefaultPC_aux (pc +32_n len) start allStartAddrs
                    (length (t1 :: tokens1))).
            destruct H21. left. assumption.
              right. rewrite H4. rewrite <- add_repr. 
                unfold w32add at 2. rewrite <- add_assoc. 
              assumption.
          exists (skipn (Zabs_nat (unsigned pc -unsigned start)) (t1::tokens1)).
            exists len, remaining.
              split. trivial. split; assumption.
  Qed.

  Hint Rewrite Zminus_0_r : pbDB.

  Lemma process_buffer_inversion :
   forall buffer startAddrs jmpTargets,
    process_buffer buffer = Some(startAddrs, jmpTargets)
      -> Z_of_nat (length buffer) <= w32modulus
      -> forall pc:int32, Int32Set.In pc startAddrs
           -> exists tokens', exists len, exists remaining,
                tokens' = (List.skipn (Zabs_nat (unsigned pc)) 
                             (List.map byte2token buffer)) /\
                goodDefaultPC (pc +32_n len) startAddrs (length buffer) /\
                (dfa_recognize 256 non_cflow_dfa tokens' = Some (len, remaining) \/
                 (dfa_recognize 256 dir_cflow_dfa tokens' = Some (len, remaining) /\
                  includeAllJmpTargets pc len tokens' jmpTargets) \/
                 dfa_recognize 256 nacljmp_dfa tokens' = Some (len, remaining)).
  Proof. unfold process_buffer; intros.
    assert (length (List.map byte2token buffer) = length buffer) as H10
      by (apply list_length_map).
    assert (noOverflow (repr 0 ::
      int32_of_nat (length (List.map byte2token buffer) - 1) :: nil)).
      rewrite H10. 
      destruct buffer as [| b buffer'].
        simpl. int32_simplify. rewrite int32_modulus_constant. simpl. lia.
        assert (length (b::buffer') >= 1)%nat by (simpl; omega).
        int32_prover.
    apply process_buffer_aux_inversion with (pc:=pc) in H;
      [idtac | assumption | (rewrite list_length_map; omega) | pbprover].
    destruct H as [tokens' [len [remaining H]]].
    simplHyp.
    assert (goodDefaultPC (pc +32_n len) startAddrs (length buffer)).
      unfold goodDefaultPC, goodDefaultPC_aux in *.
      destruct H3. left. trivial.
        right. unfold w32add in H3. rewrite zero_add in H3.
          rewrite <- H10. assumption.
    exists tokens', len, remaining. int32_simplify. pbprover.
  Qed.

  (** ** Properties of simple_parse *)
  Lemma simple_parse'_len_pos : forall bytes ps pre ins bytes1,
    simple_parse' ps bytes = Some ((pre,ins), bytes1)
      -> (length bytes > length bytes1)%nat.
  Proof. induction bytes. prover.
    intros. compute [simple_parse'] in H. fold simple_parse' in H.
      remember_destruct_head in H as pb.
      destruct l. 
        use_lemma IHbytes by eassumption. prover.
        prover.
  Qed.

  Lemma simple_parse'_ext : forall bytes bytes1 ps pre ins rem len,
    simple_parse' ps bytes = Some ((pre,ins), rem)
      -> len = (length bytes - length rem)%nat
      -> firstn len bytes = firstn len bytes1
      -> exists rem1, simple_parse' ps bytes1 = Some ((pre,ins), rem1).
  Proof. induction bytes as [ | b bytes']. prover.
    Case "bytes = b :: bytes'".
      intros. dupHyp H.
      compute [simple_parse'] in H. fold simple_parse' in H.
      use_lemma simple_parse'_len_pos by eassumption.
      assert (len >= 1)%nat by omega.
      destruct len. contradict H4. omega.
      rewrite firstn_S_cons in H1.
      destruct bytes1. simpl in H1. congruence.
      rewrite firstn_S_cons in H1.
      inversion H1. subst i.
      compute [simple_parse']. fold simple_parse'.
      destruct (parse_byte ps b).
      destruct l.
      SCase "parse_byte returns nil".
        assert (len = length bytes' - length rem)%nat.
          rewrite length_cons in H0. omega.
        eapply IHbytes'; eassumption.
      SCase "parse_byte returns some val".
        exists bytes1. prover.
  Qed.

  (** ** A theorem about immutable code region *)

  Section FETCH_INSTR_CODE_INV.

  Opaque parse_instr.

  Remark fetchSize_lt_modulus : 15 <= w32modulus.
  Proof. rewrite int32_modulus_constant. lia. Qed.

  Theorem fetch_instr_code_inv : forall s1 s2 s1' pc pre i len,
    eqCodeRegion s1 s2
      -> fetch_instruction pc s1 = (Okay_ans (pre, i, len), s1')
      -> fetch_instruction pc s2 = (Okay_ans (pre, i, len), s2).
  Proof. unfold fetch_instruction. intros.
    repeat rtl_okay_elim.
    destruct v as [pi' len'].
    rtl_okay_elim.
    remember_destruct_head in H0 as bchk; try discriminate H0.
    inversion H0. subst pi' len' s1'.
    assert (s1 = s).
      eapply parse_instr_same_state. eapply H1.
    subst s.
    bool_elim_tac.
    dupHyp H; unfold eqCodeRegion in H. destruct H as [H10 [H11 [H12 H13]]].
    assert (H14:1 <= Zpos len < 16).
      eapply parse_instr_len. eapply H1.
    assert (Zpos len - 1 < w32modulus). 
      apply Zlt_le_trans with (m:=15). omega.
      apply fetchSize_lt_modulus.
    assert (noOverflow (pc :: repr (Zpos len - 1) :: nil)).
      apply checkNoOverflow_equiv_noOverflow. trivial.
    assert (noOverflow (CStart s1 +32 pc :: repr (Zpos len - 1) :: nil)) by
      int32_prover.
    assert (H20: Ensembles.Included int32
              (addrRegion (CStart s1 +32 pc) (repr (Zpos len - 1)))
              (segAddrs CS s1)).
      apply subsetRegion_sound. assumption. assumption.
        subsetRegion_intro_tac. int32_prover. int32_prover.
    assert (parse_instr pc s2 = (Okay_ans (pre, i, len), s2)).
      eapply parse_instr_code_inv. eassumption. eapply H1.
      eassumption. eassumption. eassumption.
    assert (H22: AddrMap.get (CStart s1 +32 pc) (rtl_memory s1)
                = AddrMap.get (CStart s1 +32 pc) (rtl_memory s2)).
      apply H13. apply H20. apply addrRegion_start_in.
   (* all useful hypotheses from fetch_instruction pc s1 = ... 
      are now in the context *)
    eapply rtl_bind_okay_intro. eassumption.
    remember_destruct_head as pl. 
    inversion Hpl. subst p p0. 
    rtl_okay_intro.
    rewrite <- H11. 
    rewrite H2. rewrite H3. simpl.
    reflexivity.
  Qed.

  Lemma fetch_instr_after_flush_env : forall s v' s' pre ins len,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> flush_env s = (Okay_ans v', s')
      -> checkSegments s = true
      -> fetch_instruction (PC s') s' = (Okay_ans (pre, ins, len), s').
  Proof. intros.
    assert (H10: PC s = PC s').
      unfold flush_env in *. prover.
    assert (H12: eqCodeRegion s s').
      eapply eqCodeRegion_intro2; try eassumption.
      same_seg_regs_tac.
      left; agree_outside_seg_tac.
    apply fetch_instr_code_inv with (s1:=s) (s1':=s).
      assumption.
    rewrite <- H10. assumption.
  Qed. 

  Transparent parse_instr.
  End FETCH_INSTR_CODE_INV.

  Lemma codeLoaded_inv : forall s1 s2 code,
    eqCodeRegion s1 s2 -> codeLoaded code s1 -> codeLoaded code s2.
  Proof. unfold eqCodeRegion, codeLoaded.
    intros. split; [idtac | prover].
    unfold eqMemBuffer in *. split. prover.
    intros. repeat genSimpl.
    generalize (H3 i); intros.
    rewrite H7 by assumption. 
    rewrite <- H. apply H6.
    unfold Ensembles.In. unfold segAddrs, addrRegion.
    exists (int32_of_nat i). split; [trivial | int32_prover].
  Qed.

  Lemma list_eq_exten :
    forall (A:Type) (l1 l2:list A),
      length l1 = length l2 
        -> (forall n:nat, 
             (0<=n<length l1)%nat -> nth_error l1 n = nth_error l2 n)
        -> l1 = l2.
  Proof. induction l1; destruct l2; intros.
    trivial. 
    simpl in H. discriminate. 
    simpl in H. discriminate.
    simpl in H0.
      use_lemma (H0 O) by omega.
      simpl in H1. inversion H1.
      assert (l1 = l2).
        apply IHl1. prover.
        intros. generalize (H0 (S n)).
        intros. use_lemma H4 by omega.
        simpl in H5. trivial.
      congruence.
  Qed.

  Lemma fetch_n_sub_list : forall n1 n2 loc s,
    (n2 <= n1)%nat
      -> fetch_n n2 loc s = firstn n2 (fetch_n n1 loc s).
  Proof. induction n1; intros.
    Case "n1=0". assert (n2=0)%nat by omega. subst n2. prover.
    Case "S n1".
      destruct n2. prover.
      SCase "S n2". simpl. f_equal. prover.
  Qed.

  Lemma codeLoaded_fetch_n : forall code s k pc code' gSize guardZone,
    codeLoaded code s
      -> (pc < length code)%nat
      -> code' = skipn pc code
      -> fetch_n gSize (CStart s +32_n (length code)) s = guardZone
      -> (k < gSize)%nat
      -> fetch_n k (CStart s +32_n pc) s = firstn k (code' ++ guardZone).
  Proof. induction k.
    Case "k=0". prover.
    Case "S k". intros.
      destruct code' as [| byte code''].
      SCase "code'=nil".
        assert (length (skipn pc code) + pc = length code)%nat as H10.
          apply skipn_length.  trivial.
        rewrite <- H1 in H10. simpl in H10. subst pc. 
        contradict H0. omega.
      SCase "code'<>nil".
        rewrite <- app_comm_cons. simpl.
        f_equal.
        SSCase "byte = AddrMap.get (CStart s +32_n pc) (rtl_memory s))".
          erewrite <- codeLoaded_lookup by eassumption.
          rewrite <- (plus_0_l pc).
          rewrite <- skipn_nth. rewrite <- H1. prover.
        SSCase "fetch_n k ... = firstn k ...".
          rewrite add_assoc. rewrite add_repr.
          assert (H10:Z_of_nat pc + 1 = Z_of_nat (pc + 1)).
            rewrite inj_plus. ring.
          rewrite H10.
          assert (H12: (pc+1 <= length code)%nat) by omega.
          apply le_lt_or_eq in H12.
          destruct H12.
          SSSCase "pc+1<length code".
            eapply IHk; try eassumption.
              rewrite plus_comm.
                rewrite <- skipn_twice_eq. rewrite <- H1. trivial.
              omega.
          SSSCase "pc+1=length code".
            assert (length (skipn pc code) + pc = length code)%nat.
              apply skipn_length. trivial.
            assert (H20:(length (skipn pc code) = length code - pc)%nat).
              omega.
            assert (H22:length (byte :: code'') = 1%nat).
              rewrite H1. rewrite H20. rewrite <- H4. omega.
            destruct code''. 
              simpl. rewrite H4. subst guardZone.
              apply fetch_n_sub_list. omega.
              prover.
  Qed.

  (* todo: move *)
  Notation nat_of_int32 i := (Zabs_nat (unsigned i)).

  Lemma int32_of_nat_of_int32 : forall x,
    int32_of_nat (nat_of_int32 x) = x.
  Proof. intros. rewrite inj_Zabs_nat.
    generalize (unsigned_range x); intros.
    rewrite Zabs_eq by omega.
    apply repr_unsigned.
  Qed.

  Lemma codeLoaded_fetch_n_2 : forall code s k pc code' gSize guardZone,
    codeLoaded code s
      -> unsigned pc < Z_of_nat (length code)
      -> code' = skipn (nat_of_int32 pc) code
      -> fetch_n gSize (CStart s +32_n (length code)) s = guardZone
      -> (k < gSize)%nat
      -> fetch_n k (CStart s +32 pc) s = firstn k (code' ++ guardZone).
  Proof. intros. 
    rewrite <- (int32_of_nat_of_int32 pc).
    assert (nat_of_int32 pc < Datatypes.length code)%nat.
      apply inj_lt_rev. rewrite inj_Zabs_nat.
      rewrite Zabs_eq by int32_prover.
      assumption.
    eapply codeLoaded_fetch_n; eassumption.
  Qed.

  Lemma Zdiv_eucl_mult : forall a b c,
    b > 0 -> a = b * c -> Zdiv_eucl a b = (c, 0).
  Proof. intros. 
    assert (a mod b = 0).
      rewrite H0. rewrite (Zmult_comm b c).
      apply Z_mod_mult.
    unfold Zmod in H1.
    case_eq (Zdiv_eucl a b). intros q r. intro.
    use_lemma (Z_div_mod a b) by omega.
    rewrite H2 in *. subst r.
    genSimpl.
    ring_simplify in H1.
    assert (c = q). 
      apply Zmult_reg_l with (p:=b). omega. 
      congruence.
    prover.
  Qed.

  Lemma codeLoaded_pc_inbound: forall code s (tokens remaining: list token_id) len,
    codeLoaded code s 
      -> (length tokens + nat_of_int32 (PC s) = length code)%nat
      -> length tokens = (len + length remaining)%nat
      -> (len > 0)%nat
      -> in_seg_bounds_rng CS (PC s) (repr (Z_of_nat len - 1)) s 
           = (Okay_ans true, s).
  Proof. intros. unfold in_seg_bounds_rng. simpl.
     generalize (le_0_n (length remaining)); intros.
     f_equal. f_equal.
     use_lemma codeLoaded_length by eassumption.
     bool_intro_tac. int32_prover.
       unfold codeLoaded in H. genSimpl.
       unfold look. int32_prover.
  Qed.

  Lemma skipn_byte2token_len : forall tokens n code,
    tokens = skipn n (List.map FastVerifier.byte2token code)
      -> (n < length code)%nat
      -> (length tokens + n = length code)%nat.
  Proof. intros. rewrite H.
    rewrite skipn_length. apply list_length_map.
    rewrite list_length_map. omega.
  Qed.

  (** ** Properties of run_dep *)
  Lemma run_rep_same_seg_regs : forall pre ins dpc,
    same_seg_regs (RTL_step_list (instr_to_rtl pre ins))
      -> same_seg_regs (run_rep pre ins dpc).
  Proof. intros.
    unfold run_rep, check_rep_instr.
    destruct ins; try discriminate; simpl in H.
    Case "CMPS". same_seg_regs_tac.
    Case "MOVS". same_seg_regs_tac.
    Case "STOS". same_seg_regs_tac.
  Qed.

  Hint Resolve run_rep_same_seg_regs : same_seg_regs_db.

  (* todo: change the following lemmas to the above way of organizing thing*)
  Lemma run_rep_aoes_nci : forall pre ins dpc,
    non_cflow_instr pre ins = true
      -> agree_outside_seg ES (run_rep pre ins dpc).
  Proof. unfold run_rep, check_rep_instr. intros.
    destruct ins; try discriminate; simpl in H.
    Case "CMPS".
      agree_outside_seg_tac. 
      unfold instr_to_rtl, check_prefix. prove_instr.
    Case "MOVS".
      agree_outside_seg_tac. 
      unfold instr_to_rtl, check_prefix. prove_instr.
    Case "STOS".
      agree_outside_seg_tac. 
      unfold instr_to_rtl, check_prefix. prove_instr.
  Qed.

  Hint Resolve run_rep_aoes_nci : agree_outside_seg_db.

  Lemma run_rep_same_mem_dci : forall pre ins dpc,
    dir_cflow_instr pre ins = true
      -> same_mem (run_rep pre ins dpc).
  Proof. unfold run_rep, check_rep_instr. intros.
    destruct ins; discriminate.
  Qed.
  
  Hint Resolve run_rep_same_mem_dci : same_mem_db.

  Lemma run_rep_same_mem_nacljmp_snd : forall pre1 ins1 pre2 ins2 dpc,
    nacljmp_mask_instr pre1 ins1 pre2 ins2 = true
      -> same_mem (run_rep pre2 ins2 dpc).
  Proof. unfold nacljmp_mask_instr. intros.
    destruct ins1; bool_elim_tac; try discriminate.
    destruct_head in H0; try discriminate.
    destruct op1; try discriminate.
    destruct op2; try discriminate.
    bool_elim_tac.
    destruct ins2; try discriminate.
  Qed.

  Hint Resolve run_rep_same_mem_nacljmp_snd : same_mem_db.

  Lemma run_rep_PC : forall s v' s' pre ins default_pc,
    run_rep pre ins default_pc s = (Okay_ans v', s')
      -> PC s' = default_pc \/ PC s' = PC s.
  Proof. unfold run_rep; intros.
    repeat rtl_okay_break.
    destruct (eq v0 zero). unfold set_loc in *. prover.
    repeat rtl_okay_break.
    destruct ins; try discriminate.
    (* CMPS *)
    assert (H10:same_pc (RTL_step_list (instr_to_rtl pre (CMPS w)))).
      unfold instr_to_rtl, check_prefix, conv_CMPS. prove_instr.
    assert (H12: PC s2 = PC s3). 
      eapply H10. eassumption.
    repeat rtl_okay_break.
    destruct (eq v3 zero); destruct (eq v5 zero).
      unfold set_loc in *. prover.
      unfold set_loc in *. 
        inversion H; inversion H6; inversion H5; subst. prover.
      unfold set_loc in *. prover.
      unfold set_loc in *. right. 
        inversion H; inversion H6; inversion H5; inversion H4;
          inversion H2; inversion H1; inversion H0; subst.
        prover.
    (* MOVS *)
    assert (H10:same_pc (RTL_step_list (instr_to_rtl pre (MOVS w)))).
      unfold instr_to_rtl, check_prefix, conv_MOVS. prove_instr.
    assert (H12: PC s2 = PC s3). 
      eapply H10. eassumption.
    repeat rtl_okay_break.
    destruct (eq v3 zero).
      unfold set_loc in *. prover.
      unfold set_loc in *. right. 
        prover. inversion H4. inversion H1. subst. congruence.
    (* STOS *)
    assert (H10:same_pc (RTL_step_list (instr_to_rtl pre (STOS w)))).
      unfold instr_to_rtl, check_prefix, conv_STOS. prove_instr.
    assert (H12: PC s2 = PC s3). 
      eapply H10. eassumption.
    repeat rtl_okay_break.
    destruct (eq v3 zero).
      unfold set_loc in *. prover.
      unfold set_loc in *. right. 
        prover. inversion H4. inversion H1. subst. congruence.
  Qed.        

  (** ** Proving that any non-cflow-instr reaches a safe state in one step *)
  Ltac step_tac := 
   match goal with 
    | [H1: step_immed ?s ?s' |- _] =>
       unfold step_immed, step in H1;
       rtl_okay_break;
       do 2 rtl_okay_elim;
       match goal with
         | [H2: context[if ?X then _ else _], 
            H3: flush_env ?s = (Okay_ans ?v0, ?s0) |- _] => 
           destruct X; [idtac | discriminate H1];
           rtl_okay_break
       end
   end.

  Lemma nci_eqCodeRegion: forall pre ins s v' s',
    non_cflow_instr pre ins = true
      -> checkSegments s = true
      -> RTL_step_list (instr_to_rtl pre ins) s = (Okay_ans v', s')
      -> eqCodeRegion s s'.
  Proof. intros.
    eapply eqCodeRegion_intro2; try eassumption.
    eapply nci_same_seg_regs; try eassumption.
    eapply nci_aos; try eassumption.
  Qed.

  Ltac safestate_unfold_tac := 
    match goal with
      | [H:safeState ?s ?inv |- _] => 
        unfold safeState, appropState in H; 
        destruct inv as [[sregs_st sregs_lm] code];
        simplHyp
    end.

  Ltac same_seg_regs_rel_tac := 
      match goal with
        | [H: ?C ?s = (Okay_ans _, ?s') |- Same_Seg_Regs_Rel.brel ?s ?s']
          => let H:= fresh "H" in
              assert (same_seg_regs C) as H by same_seg_regs_tac;
              eauto using H
      end.

  Lemma nci_step_same_seg_regs : forall s s' inv pre ins len,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> non_cflow_instr pre ins = true
      -> safeState s inv
      -> s ==> s'
      -> Same_Seg_Regs_Rel.brel s s'.
  Proof. intros.
    safestate_unfold_tac.
    step_tac.
    use_lemma fetch_instr_after_flush_env by eassumption.
    assert (v0 = (pre, ins , len)) by congruence.
    assert (s0 = s1) by congruence.
    subst v0 s1.
    assert (same_seg_regs (RTL_step_list (instr_to_rtl pre ins))).
      auto using nci_same_seg_regs.
    apply Same_Seg_Regs_Rel.brel_trans with (s2:=s0).
      same_seg_regs_rel_tac.
      same_seg_regs_rel_tac.
  Qed.

  Ltac aoar_tac := 
      match goal with
        | [H: ?C ?s = (Okay_ans _, ?s') |- 
            agree_outside_addr_region (segAddrs ?Seg ?s) ?s ?s']
          => let H:= fresh "H" in
              assert (agree_outside_seg Seg C) as H 
                by agree_outside_seg_tac;
              eapply H; eassumption
      end.

  Lemma nci_step_aos : forall s s' inv pre ins len,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> non_cflow_instr pre ins = true
      -> safeState s inv
      -> s ==> s'
      -> (agree_outside_addr_region (segAddrs DS s) s s' \/
          agree_outside_addr_region (segAddrs SS s) s s' \/
          agree_outside_addr_region (segAddrs GS s) s s' \/
          agree_outside_addr_region (segAddrs ES s) s s').
  Proof. intros. safestate_unfold_tac.
    step_tac.
    use_lemma fetch_instr_after_flush_env by eassumption.
    assert (v0 = (pre, ins, len)) by congruence.
    assert (s0 = s1) by congruence.
    subst v0 s1.
    remember (RTL_step_list (instr_to_rtl pre ins)) as comp.
    assert (H20: agree_outside_seg DS comp \/ agree_outside_seg SS comp \/
                 agree_outside_seg GS comp \/ agree_outside_seg ES comp).
      subst comp.
      eauto using nci_aos.
    assert (H30: segAddrs DS s = segAddrs DS s0 /\ 
              segAddrs SS s = segAddrs SS s0 /\
              segAddrs GS s = segAddrs GS s0 /\
              segAddrs ES s = segAddrs ES s0).
      unfold segAddrs. unfold flush_env in *. prover.
    destruct H30 as [H30 [H32 [H34 H36]]].
    destruct (lock_rep pre). destruct l. 
    Case "lock".
      destruct H20 as [H20 | [H20 | [H20 | H20]]].
      SCase "DS".
        left. apply agree_outside_addr_region_trans with (s2:=s0). aoar_tac.
        rewrite H30. aoar_tac.
      SCase "SS".
        right. left. apply agree_outside_addr_region_trans with (s2:=s0). aoar_tac.
        rewrite H32. aoar_tac.
      SCase "GS".
        right. right. left. 
        apply agree_outside_addr_region_trans with (s2:=s0). aoar_tac.
        rewrite H34. aoar_tac.
      SCase "ES".
        right. right. right. 
        apply agree_outside_addr_region_trans with (s2:=s0). aoar_tac.
        rewrite H36. aoar_tac.
    Case "rep".
      right; right; right.
      apply agree_outside_addr_region_trans with (s2:=s0). aoar_tac.
      rewrite H36. aoar_tac.
    Case "repn".
      destruct H20 as [H20 | [H20 | [H20 | H20]]].
      SCase "DS".
        left. apply agree_outside_addr_region_trans with (s2:=s0). aoar_tac.
        rewrite H30. aoar_tac.
      SCase "SS".
        right. left. apply agree_outside_addr_region_trans with (s2:=s0). aoar_tac.
        rewrite H32. aoar_tac.
      SCase "GS".
        right. right. left. 
        apply agree_outside_addr_region_trans with (s2:=s0). aoar_tac.
        rewrite H34. aoar_tac.
      SCase "ES".
        right. right. right. 
        apply agree_outside_addr_region_trans with (s2:=s0). aoar_tac.
        rewrite H36. aoar_tac.
    Case "None".
      destruct H20 as [H20 | [H20 | [H20 | H20]]].
      SCase "DS".
        left. apply agree_outside_addr_region_trans with (s2:=s0). aoar_tac.
        rewrite H30. aoar_tac.
      SCase "SS".
        right. left. apply agree_outside_addr_region_trans with (s2:=s0). aoar_tac.
        rewrite H32. aoar_tac.
      SCase "GS".
        right. right. left. 
        apply agree_outside_addr_region_trans with (s2:=s0). aoar_tac.
        rewrite H34. aoar_tac.
      SCase "ES".
        right. right. right. 
        apply agree_outside_addr_region_trans with (s2:=s0). aoar_tac.
        rewrite H36. aoar_tac.
  Qed.

  Lemma nci_checkSegments_inv : forall s s' inv pre ins len,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> non_cflow_instr pre ins = true
      -> safeState s inv
      -> s ==> s'
      -> checkSegments s' = true.
  Proof.  intros. dupHyp H1. safestate_unfold_tac.
    eapply checkSegments_inv.
    eapply nci_step_same_seg_regs; eassumption.
    assumption.
  Qed.

  Lemma nci_step_eqCodeRegion : forall s s' inv pre ins len,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> non_cflow_instr pre ins = true
      -> safeState s inv
      -> s ==> s'
      -> eqCodeRegion s s'.
  Proof. intros. dupHyp H1.
    safestate_unfold_tac.
    eapply eqCodeRegion_intro.
      eapply nci_step_same_seg_regs; eassumption.
      assumption.
      eapply nci_step_aos; eassumption.
  Qed.

  Lemma nci_code_inv : forall s s' inv pre ins len,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> non_cflow_instr pre ins = true
      -> safeState s inv
      -> s ==> s'
      -> codeLoaded (snd inv) s'.
  Proof. intros. dupHyp H1.
    safestate_unfold_tac.
    eapply codeLoaded_inv; try eassumption.
      eapply nci_step_eqCodeRegion; eassumption.
  Qed.

  Lemma nci_appropState : forall s s' inv pre ins len,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> non_cflow_instr pre ins = true
      -> safeState s inv
      -> s ==> s'
      -> appropState s' inv.
  Proof. intros. dupHyp H1.
    safestate_unfold_tac.
    unfold appropState.
    use_lemma nci_step_same_seg_regs by eassumption.
    use_lemma nci_code_inv by eassumption.
    use_lemma nci_checkSegments_inv by eassumption.
    unfold Same_Seg_Regs_Rel.brel in *.
    prover.
  Qed.

  Lemma only_gs_seg_override_lock_rep : forall pre,
    only_gs_seg_override pre = true -> lock_rep pre = None.
  Proof. unfold only_gs_seg_override; intros.
    destruct (lock_rep pre); congruence.
  Qed.

  Lemma only_op_override_lock_rep : forall pre,
    only_op_override pre = true -> lock_rep pre = None.
  Proof. unfold only_op_override; intros.
    destruct (lock_rep pre); congruence.
  Qed.

  Lemma either_prefix_lock_rep : forall pre,
    either_prefix pre = true -> lock_rep pre = None.
  Proof. unfold either_prefix; intros.
    bool_elim_tac. apply only_op_override_lock_rep; assumption.
      apply only_gs_seg_override_lock_rep; assumption.
  Qed.

  Lemma only_lock_or_rep_lock_rep : forall pre,
    only_lock_or_rep pre = true -> lock_rep pre = Some rep \/ lock_rep pre = None.
  Proof. unfold only_lock_or_rep. intros.
    destruct (lock_rep pre).
    destruct l; try congruence.
    do 3 (destruct_head in H; try congruence). prover.
    do 3 (destruct_head in H; try congruence). prover.
  Qed.

  Lemma nci_lock_rep_prefix : forall pre ins,
    non_cflow_instr pre ins = true -> 
      lock_rep pre = Some rep \/ lock_rep pre = None.
  Proof. intros.
    destruct ins; simpl in H; bool_elim_tac;
    match goal with
      | [H: only_gs_seg_override pre = true |- _]
        => right; apply only_gs_seg_override_lock_rep; assumption
      | [H: either_prefix pre = true |- _]
        => right; apply either_prefix_lock_rep; assumption
      | [H: only_lock_or_rep pre = true |- _]
        =>  apply only_lock_or_rep_lock_rep in H; assumption
      | [H: false = true |- _] => congruence
      | _ => idtac
    end.
    destruct op2; try congruence.
    bool_elim_tac. 
    right; apply only_gs_seg_override_lock_rep; assumption.
  Qed.

   Lemma same_pc_same_mem_fetch_equal : forall n loc len ps s s' s0,
       rtl_memory s = rtl_memory s0
    -> seg_regs_starts (rtl_mach_state s) = seg_regs_starts (rtl_mach_state s0)
    -> seg_regs_limits (rtl_mach_state s) = seg_regs_limits (rtl_mach_state s0)
    -> parse_instr_aux n loc len ps s = Fail _ s' 
    -> (exists s0', parse_instr_aux n loc len ps s0 = Fail _ s0').
   Proof.
     induction n; intros.
     simpl. auto. exists s0. auto. unfold parse_instr_aux in *.
     Opaque parse_byte. simpl in *.
     rewrite <-H. destruct (parse_byte ps (AddrMap.get loc0 (rtl_memory s))).
     destruct l. eapply IHn; eauto.
    discriminate H2.
   Qed.

  Lemma parse_instr_aux_flush_same : forall n loc len ps s s' s1 v v2,
   flush_env s = (Okay_ans v, s1)
   -> parse_instr_aux n loc len ps s = (Okay_ans v2, s')
   -> (exists s1', parse_instr_aux n loc len ps s1 = (Okay_ans v2, s1')).
  Proof. induction n; intros. simpl in *. discriminate H0.
    simpl in *. inversion H. subst. simpl.
    destruct (parse_byte ps (AddrMap.get loc0 (rtl_memory s))).
    destruct l. eapply IHn. apply H. eauto.
    eexists. inv H0. auto.
  Qed.

  Lemma fetch_instr_flush_nofail : forall s s' s1 s1' v pre ins len,
     fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s')
    -> flush_env s = (Okay_ans v, s1)
    -> fetch_instruction (PC s1) s1 <> (Fail_ans (prefix * instr * positive), s1').
  Proof. 
    intros. intro Hc.
    unfold fetch_instruction in *.
    rtl_fail_break. unfold parse_instr in *.
    rtl_fail_break. discriminate Hc.
    rtl_okay_break. 
    rtl_okay_break. 
    assert (exists s0', parse_instr_aux 15 (add v2 (PC s)) 1 initial_parser_state s3 = Fail _ s0').
    eapply same_pc_same_mem_fetch_equal with (s := s0) (s' := s1').
         inv H0. inv H1. inv H3. auto.
         inv H0. inv H1. inv H3. auto.
         inv H0. inv H1. inv H3. auto.
    assert (v0 = v2). 
         inv H0. inv H1. inv H3. auto. rewrite <-H4.
    assert (PC s = PC s1).
         inv H0. inv H1. inv H3. auto. rewrite H5. auto.
    destruct H4. rewrite H4 in H2. discriminate H2.
    destruct v0. rtl_fail_break. unfold in_seg_bounds_rng in *.
   rtl_fail_break. discriminate Hc. discriminate Hc. destruct v0; discriminate. 
  Qed.

  Lemma nci_nextStepNoFail : forall s pre ins len,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> checkSegments s = true
      -> non_cflow_instr pre ins = true
      -> nextStepNoFail s.
  Proof. unfold nextStepNoFail, step, in_seg_bounds_rng.
    intros. intro Hc.
    rtl_fail_break. discriminate Hc.
    do 2 rtl_comp_elim.
    destruct_head in Hc; [idtac | discriminate].
    rtl_fail_break. 
    eapply fetch_instr_flush_nofail. apply H. apply H2. apply Hc.
      use_lemma fetch_instr_after_flush_env by eassumption.
      assert (v0 = (pre, ins, len)) by prover.
      assert (s0 = s1) by prover.
      subst v0 s1.
      assert (no_fail (RTL_step_list (instr_to_rtl pre ins)))
        by (eauto using nci_no_fail).
      use_lemma nci_lock_rep_prefix by eassumption.
      destruct H6.
      Case "Some rep".
        rewrite H6 in Hc.
        destruct ins; simpl in H1; bool_elim_tac;
        match goal with
          | [H: only_gs_seg_override pre = true |- _]
            => apply only_gs_seg_override_lock_rep in H; congruence
          | [H: either_prefix pre = true |- _]
            => apply either_prefix_lock_rep in H; congruence
          | [H: false = true |- _] => congruence
          | _ => (* CMPS/STOS/MOVS*)
            unfold run_rep, check_rep_instr in *;
            contradict Hc;
            (match goal with
               | [|-?c _ <> (Fail_ans _, _)] => 
                 let H:= fresh "H" in
                   cut (no_fail c); [intro H; apply H | idtac]
             end);
            unfold instr_to_rtl; no_fail_tac; fail
          | _ => idtac
        end.
        SCase "LEA".
          destruct op2; try congruence.
          bool_elim_tac.
          apply only_gs_seg_override_lock_rep in H1; congruence.
      Case "none".
        rewrite H6 in Hc.
        destruct ins; simpl in H1; bool_elim_tac;
        match goal with
          | _ =>
            contradict Hc;
            (match goal with
               | [|-?c _ <> (Fail_ans _, _)] => 
                 let H:= fresh "H" in
                   cut (no_fail c); [intro H; apply H | idtac]
             end);
            no_fail_tac
        end.
  Qed.

  Lemma nci_step_defaultPC : forall s s' pre ins len inv,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> non_cflow_instr pre ins = true
      -> safeState s inv
      -> s ==> s'
         (* the case of "PC s' = PC s" is for the case of MOVS/STOS/CMPS with a
            repeat prefix *)
      -> PC s' = PC s +32_p len \/ PC s' = PC s.
  Proof. intros.
    safestate_unfold_tac.
    step_tac.
    use_lemma fetch_instr_after_flush_env by eassumption.
    assert (v0 = (pre, ins, len)) by congruence.
    assert (s0 = s1) by congruence.
    subst v0 s1.
    assert (H20:same_pc (RTL_step_list (instr_to_rtl pre ins))).
      eapply nci_same_pc; eassumption.
    destruct (lock_rep pre). destruct l.
    Case "lock". discriminate.
    Case "rep".
      assert (H22: PC s = PC s0). unfold flush_env in *. prover.
      rewrite H22. 
      eapply run_rep_PC. eassumption.
    Case "repn". discriminate.
    Case "none". left.
      rtl_okay_break.
      assert (PC s1 = PC s'). eapply H20; eassumption.
      rewrite <- H12. unfold flush_env, set_loc in *. prover.
  Qed.

  Lemma pc_at_end_is_safe : forall s code pc startAddrs,
    codeLoaded code s
      -> checkProgram code = (true, startAddrs)
      -> pc = int32_of_nat (length code)
      -> Int32Set.In pc startAddrs \/ ~inBoundCodeAddr pc s.
  Proof. unfold codeLoaded; intros.
    simplHyp.
    generalize (unsigned_range (CLimit s)); intro.
    assert (H20:unsigned (CLimit s) + 1 <= w32modulus) by omega.
    apply Zle_lt_or_eq in H20.
    destruct H20.
    Case "unsigned (CLimit s) + 1 < w32modulus". right.
      unfold inBoundCodeAddr.  
      rewrite H1. rewrite H2. int32_simplify. omega.
    Case "unsigned (CLimit s') + 1 = w32modulus". left.
      assert (pc = int32_zero).
        rewrite H1. rewrite H2. rewrite H4.
        apply mkint_eq. apply Z_mod_same_full.
      generalize (unsigned_range (CLimit s)); intro.
      assert ((length code) > 0)%nat. omega.
      unfold checkProgram, FastVerifier.checkProgram in H0.
      remember_destruct_head in H0 as pb; try discriminate H0.
      destruct p. inversion H0; subst.
      apply process_buffer_start_in in Hpb. prover. assumption.
  Qed.

  Lemma nci_safeInSomeK : forall s pre ins len inv startAddrs,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> non_cflow_instr pre ins = true
      -> safeState s inv
      -> checkProgram (snd inv) = (true, startAddrs)
      -> goodDefaultPC ((PC s) +32_p len) startAddrs (length (snd inv))
      -> safeInSomeK s inv.
  Proof. unfold safeInSomeK. intros. 
    dupHyp H1. safestate_unfold_tac.
    exists 1%nat.
    apply safeInK_intro_one. 
      unfold safeState in H1. prover.
      eapply nci_nextStepNoFail; try eassumption.
      intros. unfold safeState. 
        assert (Int32Set.In (PC s) (snd (checkProgram code))).
          destruct H6. trivial.
          use_lemma step_immed_pc_inBound by eassumption.
            contradiction.
        assert (Same_Seg_Regs_Rel.brel s s').
          eapply nci_step_same_seg_regs; eassumption.
        assert (CLimit s = CLimit s'). 
          unfold Same_Seg_Regs_Rel.brel in *. prover.
        assert (unsigned (CLimit s') + 1 = Z_of_nat (length code)).
          unfold codeLoaded in H8. prover.
        assert (Int32Set.In (PC s') (snd (checkProgram code)) \/
                ~ inBoundCodeAddr (PC s') s').
          use_lemma nci_step_defaultPC by eassumption.
          destruct H15.
          Case "PC s' = PC s +32_p len".
            unfold goodDefaultPC in *.
            destruct H3.
              SCase "Int32Set.In (PC s +32_p len) startAddrs".
                left. prover.
              SCase "PC s +32_p len = length code".
                unfold inBoundCodeAddr. rewrite <- H13.
                use_lemma pc_at_end_is_safe by eassumption.
                rewrite H15. simpl in H2. rewrite H2. simpl.
                assumption.
          Case "PC s' = PC s".
            left. prover.
        split. eapply nci_appropState; eassumption.
        split. trivial. trivial.
  Qed.

  (** ** Proving that dir_cflow_instr can reach safe state in one step *)
  Lemma dci_eqCodeRegion: forall pre ins s v' s',
    dir_cflow_instr pre ins = true
      -> checkSegments s = true
      -> RTL_step_list (instr_to_rtl pre ins) s = (Okay_ans v', s')
      -> eqCodeRegion s s'.
  Proof. intros.
    eapply eqCodeRegion_intro2; try eassumption.
    eapply dci_same_seg_regs; try eassumption.
    right. left. eauto using dci_aoss.
  Qed.

  Lemma dci_step_same_seg_regs : forall s s' inv pre ins len,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> dir_cflow_instr pre ins = true
      -> safeState s inv
      -> s ==> s'
      -> Same_Seg_Regs_Rel.brel s s'.
  Proof. intros.
    safestate_unfold_tac.
    step_tac.
    use_lemma fetch_instr_after_flush_env by eassumption.
    assert (v0 = (pre, ins , len)) by congruence.
    assert (s0 = s1) by congruence.
    subst v0 s1.
    assert (same_seg_regs (RTL_step_list (instr_to_rtl pre ins))).
      auto using dci_same_seg_regs.
    apply Same_Seg_Regs_Rel.brel_trans with (s2:=s0).
      same_seg_regs_rel_tac.
      same_seg_regs_rel_tac.
  Qed.

  Lemma dci_step_aoss : forall s s' inv pre ins len,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> dir_cflow_instr pre ins = true
      -> safeState s inv
      -> s ==> s'
      -> agree_outside_addr_region (segAddrs SS s) s s'.
  Proof. intros. safestate_unfold_tac.
    step_tac.
    use_lemma fetch_instr_after_flush_env by eassumption.
    assert (v0 = (pre, ins, len)) by congruence.
    assert (s0 = s1) by congruence.
    subst v0 s1.
    remember (RTL_step_list (instr_to_rtl pre ins)) as comp.
    assert (H20: agree_outside_seg SS comp).
      subst comp.
      eauto using dci_aoss.
    assert (H30: segAddrs SS s = segAddrs SS s0).
      unfold segAddrs. unfold flush_env in *. prover.
    destruct (lock_rep pre).
      destruct l.
        discriminate. 
        (apply agree_outside_addr_region_trans with (s2:=s0); 
          [aoar_tac | rewrite H30; aoar_tac]).
        discriminate.
      apply agree_outside_addr_region_trans with (s2:=s0); 
        [aoar_tac | rewrite H30; aoar_tac].
  Qed.

  Lemma dci_checkSegments_inv : forall s s' inv pre ins len,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> dir_cflow_instr pre ins = true
      -> safeState s inv
      -> s ==> s'
      -> checkSegments s' = true.
  Proof.  intros. dupHyp H1.
    safestate_unfold_tac.
    eapply checkSegments_inv.
    eapply dci_step_same_seg_regs; eassumption.
    assumption.
  Qed.

  Lemma dci_code_inv : forall s s' inv pre ins len,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> dir_cflow_instr pre ins = true
      -> safeState s inv
      -> s ==> s'
      -> codeLoaded (snd inv) s'.
  Proof. intros. dupHyp H1.
    safestate_unfold_tac.
    eapply codeLoaded_inv; try eassumption.
    eapply eqCodeRegion_intro.
      eapply dci_step_same_seg_regs; eassumption.
      assumption.
      right. left. eapply dci_step_aoss; eassumption.
  Qed.

  Lemma dci_appropState : forall s s' inv pre ins len,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> dir_cflow_instr pre ins = true
      -> safeState s inv
      -> s ==> s'
      -> appropState s' inv.
  Proof. intros. dupHyp H1.
    safestate_unfold_tac.
    unfold appropState.
    use_lemma dci_step_same_seg_regs by eassumption.
    use_lemma dci_code_inv by eassumption.
    use_lemma dci_checkSegments_inv by eassumption.
    unfold Same_Seg_Regs_Rel.brel in *.
    prover.
  Qed. (* ??? why is this slow *)

  (* todo: put all these kinds of lemmas together *)
  Lemma no_prefix_no_lock_rep : forall pre,
    no_prefix pre = true -> lock_rep pre = None.
  Proof. unfold no_prefix. intros.
    repeat (destruct_head in H; try congruence).
  Qed.

  Lemma dci_lock_rep_prefix : forall pre ins,
    dir_cflow_instr pre ins = true -> lock_rep pre = None.
  Proof. intros.
    destruct ins; simpl in H; bool_elim_tac; try congruence.
    Case "CALL".
      do 2 (destruct_head in H; try congruence).
      destruct op1; try congruence.
      destruct_head in H; try congruence.
      apply no_prefix_no_lock_rep in H. assumption.
    Case "Jcc".
      apply no_prefix_no_lock_rep in H. assumption.
    Case "Jmp".
      do 2 (destruct_head in H; try congruence).
      destruct op1; try congruence.
      destruct_head in H; try congruence.
      apply no_prefix_no_lock_rep in H. assumption.
  Qed.

  Lemma dci_nextStepNoFail : forall s pre ins len,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> checkSegments s = true
      -> dir_cflow_instr pre ins = true
      -> nextStepNoFail s.
  Proof. unfold nextStepNoFail, step, in_seg_bounds_rng.
    intros. intro Hc.
    rtl_fail_break. discriminate Hc.
    do 2 rtl_comp_elim.
    destruct_head in Hc; [idtac | discriminate].
    rtl_fail_break.
    eapply fetch_instr_flush_nofail. apply H. apply H2. apply Hc.
      use_lemma fetch_instr_after_flush_env by eassumption.
      assert (v0 = (pre, ins, len)) by prover.
      assert (s0 = s1) by prover.
      subst v0 s1.
      assert (no_fail (RTL_step_list (instr_to_rtl pre ins)))
        by (eauto using dci_no_fail).
      contradict Hc.
      (match goal with
         | [|-?c _ <> (Fail_ans _, _)] => 
           cut (no_fail c)
         end).
      intro H10. apply H10.
      use_lemma dci_lock_rep_prefix by eassumption.
      rewrite H6. no_fail_tac.
  Qed.

  Lemma conv_JMP_relative_imm_PC : forall pre disp cs r cs' s v' s',
    conv_JMP pre true false (Imm_op disp) None cs = (r, cs') 
      -> same_pc (RTL_step_list (List.rev (c_rev_i cs)))
      -> RTL_step_list (List.rev (c_rev_i cs')) s = (Okay_ans v', s')
      -> (PC s') = (PC s) +32 disp.
  Proof. intros.
    unfold conv_JMP in H. 
    simpl in H. simpl_rtl.
    inv H. simpl in H1.
    autorewrite with step_list_db in H1.
    repeat rtl_okay_elim. removeUnit.
    assert (H10:PC s = PC s2). eapply H0; eassumption.
    rewrite H10.
    compute [interp_rtl] in *.
    repeat rtl_okay_break. 
    unfold get_ps, set_ps, get_loc, set_loc in *.
    repeat (rtl_invert; simpl in *; autorewrite with rtl_rewrite_db in *).
    trivial.
  Qed.

  Lemma conv_JMP_relative_imm_step_PC : forall s s' pre disp len,
    fetch_instruction (PC s) s = 
      (Okay_ans (pre, (JMP true false (Imm_op disp) None), len), s)
      -> no_prefix pre = true
      -> s ==> s'
      -> checkSegments s = true
      -> (PC s') = (PC s) +32_p len +32 disp.
  Proof. intros.
    step_tac.
    use_lemma fetch_instr_after_flush_env by eassumption.
    assert (v0 = (pre, (JMP true false (Imm_op disp) None), len)) by congruence.
    assert (s0 = s1) by congruence.
    subst v0 s1.
    unfold no_prefix in H0.
    destruct (lock_rep pre); try discriminate H0.
    rtl_okay_break.
    unfold instr_to_rtl, runConv in H1.
    remember_rev 
       (Bind unit (check_prefix pre)
              (fun _ : unit => conv_JMP pre true false (Imm_op disp) None)
              {| c_rev_i := nil; c_next := 0 |}) as cv.
    destruct cv.
    unfold check_prefix in Hcv.
    destruct (seg_override pre); try discriminate H0.
    destruct (op_override pre); try discriminate H0.
    destruct (addr_override pre); try discriminate H0.
    conv_break.
    assert (H10:PC s' = PC s1 +32 disp).
      eapply conv_JMP_relative_imm_PC; try eassumption.
      compute in H7. inv H7. simpl. 
      unfold same_pc. prover.
    rewrite H10.
    assert (H12: PC s1 = PC s +32_p len).
      unfold flush_env, set_loc in *. prover.
    rewrite H12. trivial.
  Qed.

  Opaque set_mem_n. (* without this, the QED would take forever *)
  Lemma conv_CALL_relative_imm_step_PC : forall s s' pre disp len,
    fetch_instruction (PC s) s = 
      (Okay_ans (pre, (CALL true false (Imm_op disp) None), len), s)
      -> no_prefix pre = true
      -> s ==> s'
      -> checkSegments s = true
      -> (PC s') = (PC s) +32_p len +32 disp.
  Proof. intros.
    step_tac.
    use_lemma fetch_instr_after_flush_env by eassumption.
    assert (v0 = (pre, (CALL true false (Imm_op disp) None), len)) by congruence.
    assert (s0 = s1) by congruence.
    subst v0 s1.
    unfold no_prefix in H0.
    destruct (lock_rep pre); try discriminate H0.
    rtl_okay_break.
    unfold instr_to_rtl, runConv in H1.
    remember_rev 
       (Bind unit (check_prefix pre)
              (fun _ : unit => conv_CALL pre true false (Imm_op disp) None)
              {| c_rev_i := nil; c_next := 0 |}) as cv.
    destruct cv.
    unfold conv_CALL, check_prefix in Hcv.
    destruct (seg_override pre); try discriminate H0.
    destruct (op_override pre); try discriminate H0.
    destruct (addr_override pre); try discriminate H0.
    repeat conv_break.
    assert (H20:PC s' = PC s1 +32 disp).
      eapply conv_JMP_relative_imm_PC; try eassumption.
      unfold set_mem32 in *.
      repeat conv_backward_same_pc.
      simpl. unfold same_pc. 
        intros. unfold Same_PC_Rel.brel. inv H14. trivial.
    assert (H22:PC s1 = PC s +32_p len).
      inv H6. inv H3. simpl. trivial.
    rewrite H20. rewrite H22. trivial.
  Qed.
  Transparent set_mem_n.

  Lemma conv_Jcc_PC : forall pre ct disp cs r cs' s v' s',
    conv_Jcc pre ct disp cs = (r, cs') 
      -> same_pc (RTL_step_list (List.rev (c_rev_i cs)))
      -> RTL_step_list (List.rev (c_rev_i cs')) s = (Okay_ans v', s')
      -> (PC s' = (PC s) \/ (PC s') = (PC s) +32 disp).
  Proof. intros.
    unfold conv_Jcc in H. 
    repeat conv_break.
    inv H. simpl in H1.
    autorewrite with step_list_db in H1.
    repeat rtl_okay_break.
    inv H1.
    assert (H10: PC s' = PC s0 \/ PC s' = (rtl_env s0 v2)).
      simpl in H6.
      destruct_head in H6. right. unfold set_loc in H6. prover.
        left. prover.
    assert (H12: same_pc (RTL_step_list (rev (c_rev_i cs3)))).
      unfold compute_cc, not in *.
      repeat conv_backward_same_pc. assumption.
    assert (H14: PC s = PC s0). eapply H12; eassumption.
    clear H12 H6.
    destruct H10. 
      Case "fall through case". left. prover.
      Case "the branch is taken". right.
        inv H5. simpl in *.
        autorewrite with step_list_db in H.
        repeat rtl_okay_break.
        inv H.
        inv H4. simpl in *.
        autorewrite with step_list_db in H5.
        repeat rtl_okay_break. inv H5.
        simpl in *.
        inv H3. simpl in *. removeUnit.
        autorewrite with step_list_db in H.
        repeat rtl_okay_break. inv H.
        assert (H20: same_pc (RTL_step_list (rev (c_rev_i cs0)))).
          unfold compute_cc, not in *.
          repeat conv_backward_same_pc. assumption.
        assert (H22: PC s = PC s3). eapply H20; eassumption.
        rewrite H1. rewrite H22.
        simpl in H5.
        unfold set_ps  in *. inv H4. simpl in *.
        inv H5. simpl in *. inv H6. simpl in *.
        autorewrite with rtl_rewrite_db. trivial.
  Qed.
        
  Lemma conv_Jcc_step_PC : forall s s' pre ct disp len,
    fetch_instruction (PC s) s = (Okay_ans (pre, (Jcc ct disp), len), s)
      -> no_prefix pre = true
      -> s ==> s'
      -> checkSegments s = true
      -> (PC s' = (PC s) +32_p len \/ (PC s') = (PC s) +32_p len +32 disp).
  Proof. intros.
    step_tac.
    use_lemma fetch_instr_after_flush_env by eassumption.
    assert (v0 = (pre, (Jcc ct disp), len)) by congruence.
    assert (s0 = s1) by congruence.
    subst v0 s1.
    unfold no_prefix in H0.
    destruct (lock_rep pre); try discriminate H0.
    rtl_okay_break.
    unfold instr_to_rtl, runConv in H1.
    remember_rev 
       (Bind unit (check_prefix pre)
              (fun _ : unit => conv_Jcc pre ct disp)
              {| c_rev_i := nil; c_next := 0 |}) as cv.
    destruct cv.
    unfold check_prefix in Hcv.
    destruct (seg_override pre); try discriminate H0.
    destruct (op_override pre); try discriminate H0.
    destruct (addr_override pre); try discriminate H0.
    repeat conv_break.
    assert (H20:PC s' = PC s1 \/ PC s' = PC s1 +32 disp).
      eapply conv_Jcc_PC; try eassumption.
      repeat conv_backward_same_pc.
      simpl. unfold same_pc. 
        intros. unfold Same_PC_Rel.brel. inv H8. trivial.
    assert (H22:PC s1 = PC s +32_p len).
      inv H6. inv H3. simpl. trivial.
    prover.
  Qed.

  (* any aligned address is a safe program counter *)
  Lemma aligned_addr_safePC : forall s inv pc,
    safeState s inv -> aligned pc
      -> Int32Set.In pc (snd (checkProgram (snd inv))) \/ ~ inBoundCodeAddr pc s.
  Proof. intros. safestate_unfold_tac.
    unfold checkProgram in *. simpl.
    remember_rev (FastVerifier.checkProgram non_cflow_dfa dir_cflow_dfa nacljmp_dfa
                  code) as cp.
    destruct cp as [b startAddrs].
    unfold FastVerifier.checkProgram in Hcp.
    destruct_head in Hcp; [idtac | prover].
    destruct p. inversion Hcp. subst. 
    simpl in H1. bool_elim_tac.
    remember_rev (int32_lequ_bool pc (CLimit s)) as cmp.
    destruct cmp.
    Case "pc <= (CLimit s)". left. simpl.
      unfold codeLoaded in *.
      simplHyp.
      assert (0 <= unsigned pc < Z_of_nat (length code)) by int32_prover.
      rewrite <- (repr_unsigned _ pc).
      eapply checkAligned_corr; try eassumption.
        unfold aligned, aligned_bool in H0.
        rewrite ZOrderedType.Z_as_DT.eqb_eq in H0.
        assumption.
    Case "pc > (CLimit s)". right. prover.
  Qed.

  Lemma dci_step_safePC : forall s s' pre ins len inv,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> dir_cflow_instr pre ins = true
      -> safeState s inv
      -> goodDefaultPC ((PC s) +32_p len) (snd (checkProgram (snd inv))) (length (snd inv))
      -> goodJmp ins ((PC s) +32_p len) (snd (checkProgram (snd inv))) = true
      -> s ==> s'
      -> Int32Set.In (PC s') (snd (checkProgram (snd inv))) \/ 
         ~ inBoundCodeAddr (PC s') s'.
  Proof. unfold inBoundCodeAddr. intros.
    use_lemma dci_step_same_seg_regs by eassumption.
    assert (CLimit s = CLimit s').
       unfold Same_Seg_Regs_Rel.brel in *. prover.
    rewrite <- H6.
    dupHyp H1. safestate_unfold_tac.
    destruct ins; try discriminate H0.
    Case "CALL".
      destruct near; try discriminate H0.
      destruct absolute; try discriminate H0.
      destruct op1; try discriminate H0.
      destruct sel; try discriminate H0.
      use_lemma conv_CALL_relative_imm_step_PC by eassumption.
      unfold goodJmp, goodJmpTarget in H3.
      bool_elim_tac.
        left. prover.
        eapply aligned_addr_safePC. assumption. prover.
   Case "Jcc".
      use_lemma conv_Jcc_step_PC by eassumption.
      unfold goodJmp, goodJmpTarget in H3.
      unfold goodDefaultPC in H2.
      destruct H13.
      SCase "PC s' = PC s +32_p len".
        destruct H2. left. prover.
          remember_rev (checkProgram code) as cp.
          destruct cp as [t startAddrs].
          simpl in H8. subst t.
          use_lemma pc_at_end_is_safe by eassumption.
          simpl. prover.
      SCase "PC s' = PC s +32_p len +32 disp".
      bool_elim_tac.
        left. rewrite H13. apply Int32Set.mem_spec. assumption.
        eapply aligned_addr_safePC. assumption. prover.
    Case "JMP".
      destruct near; try discriminate H0.
      destruct absolute; try discriminate H0.
      destruct op1; try discriminate H0.
      destruct sel; try discriminate H0.
      use_lemma conv_JMP_relative_imm_step_PC by eassumption.
      unfold goodJmp, goodJmpTarget in H3.
      bool_elim_tac.
        left. prover.
        eapply aligned_addr_safePC. assumption. prover.
  Qed.        

  Lemma dci_safeInSomeK : forall s pre ins len inv startAddrs,
    fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
      -> dir_cflow_instr pre ins = true
      -> safeState s inv
      -> checkProgram (snd inv) = (true, startAddrs)
      -> goodDefaultPC ((PC s) +32_p len) startAddrs (length (snd inv))
      -> goodJmp ins ((PC s) +32_p len) (snd (checkProgram (snd inv))) = true
      -> safeInSomeK s inv.
  Proof. unfold safeInSomeK. intros. 
    dupHyp H1. safestate_unfold_tac.
    exists 1%nat.
    apply safeInK_intro_one. 
      unfold safeState in H1. prover.
      eapply dci_nextStepNoFail; try eassumption.
      intros. unfold safeState. 
        split. eapply dci_appropState; eassumption.
        split. trivial. 
          change code with (snd ((sregs_st, sregs_lm, code))).
          eapply dci_step_safePC; try eassumption. prover.
  Qed. 


  (** ** the proof that nacljmp is safe in two steps *)
  Lemma nacljmp_first_non_cflow_instr : forall pre1 ins1 pre2 ins2,
    nacljmp_mask_instr pre1 ins1 pre2 ins2 = true 
      -> non_cflow_instr pre1 ins1 = true.
  Proof. intros.
    unfold nacljmp_mask_instr in H.
    destruct ins1; bool_elim_tac; try discriminate.
    assert (either_prefix pre1 = true).
      clear H0. destruct pre1.
        destruct lock_rep; try discriminate.
        destruct seg_override; try discriminate.
        destruct op_override; try discriminate.
        destruct addr_override; try discriminate.
        unfold either_prefix.
        apply orb_true_intro. left.
        trivial.
    destruct op1; try (destruct w; discriminate).
    simpl. prover.
  Qed.

  Lemma nacljmp_no_prefix : forall pre1 ins1 pre2 ins2,
    nacljmp_mask_instr pre1 ins1 pre2 ins2 = true 
      -> no_prefix pre1 = true /\ no_prefix pre2 = true.
  Proof. unfold nacljmp_mask_instr; intros. bool_elim_tac.
    prover.
  Qed.

  Lemma nacljmp_mask_PC : forall s s' pre1 ins1 len1 pre2 ins2 inv,
    fetch_instruction (PC s) s = (Okay_ans (pre1, ins1, len1), s)
      -> nacljmp_mask_instr pre1 ins1 pre2 ins2 = true
      -> safeState s inv
      -> s ==> s'
      -> PC s' = PC s +32_p len1.
  Proof. intros. safestate_unfold_tac.
    step_tac.
    use_lemma fetch_instr_after_flush_env by eassumption.
    assert (v0 = (pre1, ins1, len1)) by congruence.
    assert (s0 = s1) by congruence.
    subst v0 s1.
    assert (non_cflow_instr pre1 ins1 = true).
      eapply nacljmp_first_non_cflow_instr; eassumption.
    assert (H20:same_pc (RTL_step_list (instr_to_rtl pre1 ins1))).
      eapply nci_same_pc; eassumption.
    use_lemma nacljmp_no_prefix by eassumption.
    simplHyp. unfold no_prefix in H12.
    do 4 (destruct_head in H12; try congruence).
      rtl_okay_break.
      assert (H22:PC s1 = PC s'). eapply H20; eassumption.
      rewrite <- H22. unfold flush_env, set_loc in *. prover.
  Qed.

  Lemma nacljmp_snd_no_fail : forall pre1 ins1 pre2 ins2,
    nacljmp_mask_instr pre1 ins1 pre2 ins2 = true 
      -> no_fail (RTL_step_list (instr_to_rtl pre2 ins2)).
  Proof. unfold nacljmp_mask_instr; intros. 
    destruct ins1; bool_elim_tac; try discriminate.
    (destruct_head in H0; try discriminate H0).
    destruct op1; try discriminate H0.
    destruct op2; try discriminate H0.
    bool_elim_tac.
    destruct ins2; try discriminate.
    Case "Call".
      unfold instr_to_rtl in *.
      do 2 (destruct_head in H2; try discriminate).
      destruct op1; try discriminate.
      prove_instr.
    Case "Jmp".
      unfold instr_to_rtl in *.
      do 2 (destruct_head in H2; try discriminate).
      destruct op1; try discriminate.
      prove_instr.
  Qed.

  
  Lemma nacljmp_snd_nextStepNoFail : forall s pre1 ins1 pre2 ins2 len2,
    fetch_instruction (PC s) s = (Okay_ans (pre2, ins2, len2), s)
      -> checkSegments s = true
      -> nacljmp_mask_instr pre1 ins1 pre2 ins2 = true 
      -> nextStepNoFail s.
  Proof. unfold nextStepNoFail, step, in_seg_bounds_rng.
    intros. intro Hc.
    rtl_fail_break. discriminate Hc.
    do 2 rtl_comp_elim.
    destruct_head in Hc; [idtac | discriminate].
    rtl_fail_break.
    eapply fetch_instr_flush_nofail. apply H. apply H2. apply Hc.
      use_lemma fetch_instr_after_flush_env by eassumption.
      assert (v0 = (pre2, ins2, len2)) by prover.
      assert (s0 = s1) by prover.
      subst v0 s1.
      assert (no_fail (RTL_step_list (instr_to_rtl pre2 ins2))) 
        by (eauto using nacljmp_snd_no_fail).
      contradict Hc.
      (match goal with
         | [|-?c _ <> (Fail_ans _, _)] => 
           cut (no_fail c)
         end).
      intro H10. apply H10.
      remember_rev (lock_rep pre2) as lr.
      destruct lr. destruct l.
        Case "lock". 
          apply nacljmp_no_prefix in H1. simplHyp. 
          apply no_prefix_no_lock_rep in H6. congruence.
        Case "rep". 
          apply nacljmp_no_prefix in H1. simplHyp. 
          apply no_prefix_no_lock_rep in H6. congruence.
        Case "repn". 
          apply nacljmp_no_prefix in H1. simplHyp. 
          apply no_prefix_no_lock_rep in H6. congruence.
        Case "none". no_fail_tac.
  Qed.

  Lemma no_prefix_no_op_override : forall pre,
    no_prefix pre = true -> op_override pre = false.
  Proof. unfold no_prefix. intros.
    repeat (destruct_head in H; try congruence).
  Qed.

  Lemma compute_parity_aux_break : forall n sz (op1:pseudo_reg sz) op2 cs v' cs', 
    compute_parity_aux op1 op2 n cs = (v', cs')
      -> exists ilist,
          c_rev_i cs' = (ilist ++ c_rev_i cs)%list /\
          forall s s' szx x, 
            RTL_step_list (rev ilist) s = (Okay_ans tt, s')
              -> x < c_next cs 
              -> rtl_env s (ps_reg szx x) = rtl_env s' (ps_reg szx x).
  Proof. induction n; intros.
    Case "n=0". simpl in H. inv H. simpl.
      eexists. split.
      rewrite CheckDeterministic.cons_app. trivial.
      intros. simpl in H. inv H. simpl. autorewrite with rtl_rewrite_db. trivial.
    Case "S n".  simpl in H.
      remember_destruct_head in H as cp. rename c into cs1.
      use_lemma IHn by eassumption.
      destruct H0 as [ilist [H20 H22]].
      unfold arith, fresh in H.
      simpl in H. simpl_rtl.
      eexists. split.
        inv H. simpl. rewrite H20.
        repeat (rewrite app_comm_cons). trivial.
        simpl. intros.
        autorewrite with step_list_db in H0.
        repeat rtl_okay_elim. removeUnit.
        erewrite H22; [idtac | eassumption | omega].
        assert (c_next cs < c_next cs1).
          eapply compute_parity_aux_index_increase; eassumption.
        simpl in *.
        unfold set_ps in *. prover.
        simpl in *.
        autorewrite with rtl_rewrite_db.
        trivial.
  Qed.        

  Lemma nacljmp_mask_reg_aligned : forall pre r1 wd cs r cs' s v' s',
    conv_AND pre true (Reg_op r1) (Imm_op wd) cs = (r, cs')
      -> no_prefix pre = true
      -> signed wd = signed safeMask
      -> RTL_step_list (List.rev (c_rev_i cs')) s = (Okay_ans v', s')
      -> aligned (get_location (reg_loc r1) (rtl_mach_state s')).
  Proof. unfold conv_AND, conv_logical_op. intros.
    assert (op_override pre = false).
      eauto using no_prefix_no_op_override.
    unfold  load_op, set_op, compute_parity in H.
    rewrite H3 in H.
    compute [opsize] in H.
    repeat conv_break. removeUnit.
    conv_backward.
    inv H21. rtl_okay_elim. inv H2. simpl.
    unfold look, upd.
    destruct_head; [idtac | contradict n; trivial].
    conv_backward.
    inv H17. inv H. inv H22. inv H2. simpl.
    autorewrite with rtl_rewrite_db.
    repeat (conv_backward;
      match goal with 
        | [H: interp_rtl (set_loc_rtl _ _) _ = _,
          H1 : Return _ _ = _ |- _]
          => inv H; inv H1; simpl
      end).
    conv_backward.
    inv H11. inv H. simpl.
    autorewrite with rtl_rewrite_db.
    conv_backward.
    inv H10. inv H2. simpl.
    autorewrite with rtl_rewrite_db.
    eapply compute_parity_aux_break in H20.
    destruct H20 as [ilists [H30 H32]].
    rewrite H30 in H.
    rewrite rev_app_distr in H.
    autorewrite with step_list_db in H.
    rtl_okay_elim. removeUnit.
    destruct v1 as [andResIdx].
    assert (andResIdx < c_next cs15).
      do 5 (match goal with
        | [H: ?cv ?cs = (_, ?cs') |- _ < c_next ?cs']
          => apply Zlt_trans with (m:= c_next cs);
             [idtac | 
              cut (conv_index_increase cv); [eauto | conv_index_increase_tac]]
      end).
      unfold arith in H6.
      eapply fresh_conv_index_monotone; eassumption.
    use_lemma H32 by eassumption.    
    rewrite <- H11. clear H30 H32 H10 H11 H.
    conv_backward. 
    inv H10. inv H2. simpl.
    autorewrite with rtl_rewrite_db.
    conv_backward.
    inv H10. inv H. simpl.
    autorewrite with rtl_rewrite_db.
    conv_backward.
    inv H9. inv H2. simpl.
    autorewrite with rtl_rewrite_db.
    conv_backward.
    inv H8. inv H. simpl.
    autorewrite with rtl_rewrite_db.
    conv_backward.
    inv H7. inv H2. simpl.
    assert (andResIdx < c_next cs2).
      unfold arith, fresh in H6. prover.
    autorewrite with rtl_rewrite_db.
    conv_backward.
    inv H2. inv H7. inv H. simpl.
    autorewrite with rtl_rewrite_db.
    clear H9.
    conv_backward.
    inv H2. inv H6. simpl.
    autorewrite with rtl_rewrite_db.
    conv_backward.
    inv H4. inv H. simpl.
    autorewrite with rtl_rewrite_db.
    eapply and_safeMask_aligned. assumption.
  Qed.

  Lemma nacljmp_snd_same_seg_regs : forall pre1 ins1 pre2 ins2,
    nacljmp_mask_instr pre1 ins1 pre2 ins2 = true
      -> same_seg_regs (RTL_step_list (instr_to_rtl pre2 ins2)).
  Proof. unfold nacljmp_mask_instr. intros.
      destruct ins1; bool_elim_tac; try discriminate H0.
      destruct_head in H0; try discriminate.
      destruct op1; try discriminate.
      destruct op2; try discriminate.
      bool_elim_tac.
      destruct ins2; try discriminate H2.
      unfold instr_to_rtl, check_prefix. prove_instr.
      unfold instr_to_rtl, check_prefix. prove_instr.
  Qed.

  Lemma nacljmp_snd_step_same_seg_regs : 
   forall s s' code pre1 ins1 pre2 ins2 len2,
    fetch_instruction (PC s) s = (Okay_ans (pre2, ins2, len2), s)
      -> nacljmp_mask_instr pre1 ins1 pre2 ins2 = true 
      -> codeLoaded code s
      -> checkSegments s = true
      -> s ==> s'
      -> Same_Seg_Regs_Rel.brel s s'.
  Proof. unfold safeState. intros.
    step_tac.
    use_lemma fetch_instr_after_flush_env by eassumption.
    assert (v0 = (pre2, ins2 , len2)) by congruence.
    assert (s0 = s1) by congruence.
    subst v0 s1.
    unfold nacljmp_mask_instr in H0.
    assert (same_seg_regs (RTL_step_list (instr_to_rtl pre2 ins2))).
      eauto using nacljmp_snd_same_seg_regs.
    apply Same_Seg_Regs_Rel.brel_trans with (s2:=s0).
      same_seg_regs_rel_tac.
      same_seg_regs_rel_tac.
  Qed.

  (* todo: a tactic for unfolding nacljmp_mask_instr *)
  Lemma nacljmp_snd_aoss : forall pre1 ins1 pre2 ins2,
    nacljmp_mask_instr pre1 ins1 pre2 ins2 = true
      -> agree_outside_seg SS (RTL_step_list (instr_to_rtl pre2 ins2)).
  Proof. unfold nacljmp_mask_instr; intros.
      destruct ins1; bool_elim_tac; try discriminate H0.
      destruct_head in H0; try discriminate.
      destruct op1; try discriminate.
      destruct op2; try discriminate.
      bool_elim_tac.
      destruct ins2; try discriminate.
      unfold instr_to_rtl, check_prefix. prove_instr.
      unfold instr_to_rtl, check_prefix. prove_instr.
  Qed.

  (* todo : maybe use a step lemma to parametrize over the property of ins2 *)
  Lemma nacljmp_snd_step_aoss : forall s s' code pre1 ins1 pre2 ins2 len2,
    fetch_instruction (PC s) s = (Okay_ans (pre2, ins2, len2), s)
      -> nacljmp_mask_instr pre1 ins1 pre2 ins2 = true
      -> codeLoaded code s
      -> checkSegments s = true
      -> s ==> s'
      -> agree_outside_addr_region (segAddrs SS s) s s'.
  Proof. intros.
    step_tac.
    use_lemma fetch_instr_after_flush_env by eassumption.
    assert (v0 = (pre2, ins2, len2)) by congruence.
    assert (s0 = s1) by congruence.
    subst v0 s1.
    assert (H20: agree_outside_seg SS (RTL_step_list (instr_to_rtl pre2 ins2))).
      eauto using nacljmp_snd_aoss.
    assert (H30: segAddrs SS s = segAddrs SS s0).
      unfold segAddrs. unfold flush_env in *. prover.
    destruct (lock_rep pre2).
      destruct l.
        (apply agree_outside_addr_region_trans with (s2:=s0); 
          [aoar_tac | rewrite H30; aoar_tac]).
        (apply agree_outside_addr_region_trans with (s2:=s0); 
          [aoar_tac | rewrite H30; idtac]).
          assert (H32: agree_outside_seg SS 
                   (run_rep pre2 ins2 (add (PC s0) (repr (Zpos len2))))).
            apply same_mem_agree_outside_seg.
            eapply run_rep_same_mem_nacljmp_snd; eassumption.
            eapply run_rep_same_seg_regs.
            eauto using nacljmp_snd_same_seg_regs.
          eapply H32; eassumption.
        (apply agree_outside_addr_region_trans with (s2:=s0); 
          [aoar_tac | rewrite H30; aoar_tac]).
      apply agree_outside_addr_region_trans with (s2:=s0); 
        [aoar_tac | rewrite H30; aoar_tac].
  Qed.

  Lemma conv_JMP_absolute_reg_PC : forall pre reg cs r cs' s v' s',
    conv_JMP pre true true (Reg_op reg) None cs = (r, cs') 
      -> (forall s1 s2, 
           RTL_step_list (List.rev (c_rev_i cs)) s1 = (Okay_ans tt, s2)
             -> get_location (reg_loc reg) (rtl_mach_state s1)
                = get_location (reg_loc reg) (rtl_mach_state s2))
      -> RTL_step_list (List.rev (c_rev_i cs')) s = (Okay_ans v', s')
      -> (PC s') = (get_location (reg_loc reg) (rtl_mach_state s)).
  Proof. intros.
    unfold conv_JMP in H. 
    simpl in H. simpl_rtl.
    inv H. simpl in H1.
    autorewrite with step_list_db in H1.
    repeat rtl_okay_elim. removeUnit.
    compute [interp_rtl] in *.
    repeat rtl_okay_break. 
    unfold get_ps, set_ps, get_loc, set_loc in *.
    repeat (rtl_invert; simpl in *; autorewrite with rtl_rewrite_db in *).
    rewrite zero_add.
    apply eq_sym. eauto.
  Qed.

  Lemma conv_JMP_absolute_reg_step_PC : forall s s' pre r len,
    fetch_instruction (PC s) s = 
      (Okay_ans (pre, (JMP true true (Reg_op r) None), len), s)
      -> no_prefix pre = true
      -> s ==> s'
      -> checkSegments s = true
      -> (PC s') = (get_location (reg_loc r) (rtl_mach_state s)).
  Proof. intros.
    step_tac.
    use_lemma fetch_instr_after_flush_env by eassumption.
    assert (v0 = (pre, (JMP true true (Reg_op r) None), len)) by congruence.
    assert (s0 = s1) by congruence.
    subst v0 s1.
    unfold no_prefix in H0.
    destruct (lock_rep pre); try discriminate H0.
    rtl_okay_break.
    unfold instr_to_rtl, runConv in H1.
    remember_rev 
       (Bind unit (check_prefix pre)
              (fun _ : unit => conv_JMP pre true true (Reg_op r) None)
              {| c_rev_i := nil; c_next := 0 |}) as cv.
    destruct cv.
    unfold check_prefix in Hcv.
    destruct (seg_override pre); try discriminate H0.
    destruct (op_override pre); try discriminate H0.
    destruct (addr_override pre); try discriminate H0.
    conv_break.
    assert (gp_regs (rtl_mach_state s) = gp_regs (rtl_mach_state s1)).
      unfold flush_env, set_loc in *. prover.
    unfold get_location.
    rewrite H8.
    eapply conv_JMP_absolute_reg_PC; try eassumption.
      intros. inv H7. prover.
  Qed.

  Opaque set_mem_n. (* without this, the QED would take forever *)
  Lemma conv_CALL_absolute_reg_step_PC : forall s s' pre r len,
    fetch_instruction (PC s) s = 
      (Okay_ans (pre, (CALL true true (Reg_op r) None), len), s)
      -> ESP <> r
      -> no_prefix pre = true
      -> s ==> s'
      -> checkSegments s = true
      -> (PC s') = (get_location (reg_loc r) (rtl_mach_state s)).
  Proof. intros.
    step_tac.
    use_lemma fetch_instr_after_flush_env by eassumption.
    assert (v0 = (pre, (CALL true true (Reg_op r) None), len)) by congruence.
    assert (s0 = s1) by congruence.
    subst v0 s1.
    unfold no_prefix in H1.
    destruct (lock_rep pre); try discriminate H1.
    rtl_okay_break.
    unfold instr_to_rtl, runConv in H2.
    remember_rev 
       (Bind unit (check_prefix pre)
              (fun _ : unit => conv_CALL pre true true (Reg_op r) None)
              {| c_rev_i := nil; c_next := 0 |}) as cv.
    destruct cv.
    unfold conv_CALL, check_prefix in Hcv.
    destruct (seg_override pre); try discriminate H1.
    destruct (op_override pre); try discriminate H1.
    destruct (addr_override pre); try discriminate H1.
    repeat conv_break.
    removeUnit.
    assert (H20:gp_regs (rtl_mach_state s) = gp_regs (rtl_mach_state s1)).
      unfold flush_env, set_loc in *. prover.
    unfold get_location.
    rewrite H20.
    eapply conv_JMP_absolute_reg_PC; try eassumption.
      intros. 
      inv H14. simpl in *. autorewrite with step_list_db in *.
      repeat rtl_okay_break.
      inv H15. inv H16. simpl in *.
      unfold look, upd.
      destruct (register_eq_dec ESP r).
        contradict e; assumption.
        simpl_rtl.
        clear Hcv.
        unfold set_mem32 in *.
        assert (same_mach_state (RTL_step_list (rev (c_rev_i cs4)))).
          do 5 conv_backward_sms. 
          inv H8. prover.
        assert (rtl_mach_state s2 = rtl_mach_state s4). eapply H15; eassumption.
        prover.
  Qed.
  Transparent set_mem_n.

  Lemma nacljmp_step_safePC : forall s s' s'' pre1 ins1 len1 pre2 ins2 len2 inv,
    fetch_instruction (PC s) s = (Okay_ans (pre1, ins1, len1), s)
      -> fetch_instruction (PC s +32_p len1) s' = (Okay_ans (pre2, ins2, len2), s')
      -> nacljmp_mask_instr pre1 ins1 pre2 ins2 = true 
      -> safeState s inv
      -> s ==> s'
      -> s'==> s''
      -> aligned (PC s'').
  Proof. intros.
    dupHyp H1; unfold nacljmp_mask_instr in H1.
    dupHyp H2; safestate_unfold_tac.  simplHyp.
    destruct ins1; bool_elim_tac; try congruence.
    destruct w; try congruence.
    destruct op1; try congruence.
    destruct op2; try congruence.
    bool_elim_tac.
    assert (aligned (get_location (reg_loc r) (rtl_mach_state s'))).
      clear H14 H0 H4.
      step_tac.
      use_lemma fetch_instr_after_flush_env by eassumption.
      assert (v0 = (pre1, (AND true (Reg_op r) (Imm_op i)), len1)) by congruence.
      assert (s0 = s1) by congruence.
      subst v0 s1.
      rewrite no_prefix_no_lock_rep in H3 by assumption.
      unfold instr_to_rtl, check_prefix in H3.
      dupHyp H1; unfold no_prefix in H1.
      repeat (destruct_head in H1; try congruence).
      unfold runConv in H3. simpl in H3.
      remember_destruct_head in H3 as ca.
      eapply nacljmp_mask_reg_aligned; try eassumption.
        destruct (zeq (signed i) (signed safeMask)). congruence.
          discriminate H12.
    assert (H20: PC s' = PC s +32_p len1).
      eapply nacljmp_mask_PC. 
        eapply H. eassumption. eassumption. eassumption.
    rewrite <- H20 in *.
    assert (non_cflow_instr pre1 (AND true (Reg_op r) (Imm_op i)) = true).
      eapply nacljmp_first_non_cflow_instr; eassumption.
    assert (H22: checkSegments s' = true).
      eapply nci_checkSegments_inv. eapply H. assumption.
        eassumption. assumption.
    destruct ins2; bool_elim_tac; try congruence.
    Case "CALL".
      destruct (register_eq_dec r ESP); try congruence.
      destruct near; try congruence.
      destruct absolute; try congruence.
      destruct op1; try congruence.
      destruct sel; try congruence.
      clear H.
      assert (r = r0).
        destruct_head in H14; congruence.
      subst r0.
      assert (H30: PC s'' = get_location (reg_loc r) (rtl_mach_state s')).
        eapply conv_CALL_absolute_reg_step_PC.
          eassumption. congruence. assumption. assumption. 
          assumption.
      rewrite H30. assumption.
    Case "JMP".
      destruct near; try congruence.
      destruct absolute; try congruence.
      destruct op1; try congruence.
      destruct sel; try congruence.
      clear H.
      assert (r = r0).
        destruct_head in H14; congruence.
      subst r0.
      assert (H30: PC s'' = get_location (reg_loc r) (rtl_mach_state s')).
        eapply conv_JMP_absolute_reg_step_PC.
          eassumption. congruence. assumption. assumption. 
      rewrite H30. assumption.
  Qed.

  Lemma nacljmp_safeInSomeK : forall s code pre1 ins1 len1 pre2 ins2 len2,
    fetch_instruction (PC s) s = (Okay_ans (pre1, ins1, len1), s)
      -> fetch_instruction (PC s +32_p len1) s = (Okay_ans (pre2, ins2, len2), s)
      -> nacljmp_mask_instr pre1 ins1 pre2 ins2 = true 
      -> safeState s code
      -> safeInSomeK s code.
  Proof. unfold safeInSomeK. intros. 
    dupHyp H2. safestate_unfold_tac.
    exists 2%nat.
    assert (non_cflow_instr pre1 ins1 = true).
      eapply nacljmp_first_non_cflow_instr; eassumption.
    unfold safeInK.
      split. unfold safeState in H2. prover.
      split. eapply nci_nextStepNoFail. eapply H. assumption. assumption.
      intros. right.
        assert (Same_Seg_Regs_Rel.brel s s').
          eapply nci_step_same_seg_regs. eapply H. assumption.
          eassumption. assumption.
        assert (eqCodeRegion s s').
          eapply nci_step_eqCodeRegion. 
            eapply H. assumption. eassumption. assumption.
        assert (PC s' = PC s +32_p len1).
          eapply nacljmp_mask_PC. 
            eapply H. eassumption. eassumption. assumption.
        assert (fetch_instruction (PC s') s' = (Okay_ans (pre2, ins2, len2), s')).
          rewrite H13.
          eapply fetch_instr_code_inv. eassumption. eassumption.
        assert (codeLoaded code s').
          eapply codeLoaded_inv; eassumption.
        assert (checkSegments s' = true).
          eapply nci_checkSegments_inv. eapply H. assumption.
            eassumption. assumption.
        split. 
          eapply nci_appropState. eapply H. assumption. assumption. assumption.
        split.
          eapply nacljmp_snd_nextStepNoFail; eassumption.
          intro s''. intros. left.
            use_lemma nacljmp_snd_step_same_seg_regs by eassumption.
            assert (H20: CLimit s = CLimit s'').
              unfold Same_Seg_Regs_Rel.brel in *.
              simplHyp. prover.
            assert (eqCodeRegion s' s'').
              eapply eqCodeRegion_intro; try eassumption.
              right; left. 
                eapply nacljmp_snd_step_aoss; eassumption.
            use_lemma codeLoaded_inv by eassumption.
            use_lemma checkSegments_inv by eassumption.
            assert (appropState s'' ((sregs_st, sregs_lm), code)).
              unfold appropState. unfold Same_Seg_Regs_Rel.brel in *.
              prover.
            split. assumption.
            split. trivial.
              assert (aligned (PC s'')).
                eapply nacljmp_step_safePC. eapply H. 
                  rewrite <- H13. eapply H14.
                  assumption. eassumption. assumption. assumption.
              unfold inBoundCodeAddr.
              rewrite <- H20.
              change code with (snd ((sregs_st, sregs_lm), code)).
              eapply aligned_addr_safePC. assumption. assumption.
  Qed.                  


  (** ** The interface theorem between the verifier correctness proof and the
     proofs about the parser *)

  (* todo: move *)
  Lemma int32_add_add_sub :
    forall i1 i2 i3:int32, (i1 +32 i3) +32 (i2 -32 i3) = i1 +32 i2.
  Proof. intros; unfold w32add. rewrite add_assoc. 
    rewrite (@add_commut 31 i3 (i2 -32 i3)).
    rewrite <- sub_add_l. 
    rewrite add_sub_assoc. rewrite sub_idem.
    rewrite add_zero. trivial.
  Qed.

  Lemma eqMemBuffer_succ : forall b buffer s lc,
    eqMemBuffer (b::buffer) s lc -> eqMemBuffer buffer s (lc +32_z 1).
  Proof. unfold eqMemBuffer. intros.
    simplHyp.
    rewrite length_cons in H.
    split. int32_prover.
    intros.
      assert (S i < length (b::buffer))%nat.
        rewrite length_cons. omega.
      use_lemma (H0 (S i)) by eassumption.
      rewrite cons_nth in H3 by omega.
      assert (S i - 1 = i)%nat by omega.
      assert (lc +32_n S i = lc +32_p 1 +32_n i).
        unfold w32add. rewrite add_assoc. rewrite add_repr.
        cut (Z_of_nat (S i) = 1 + Z_of_nat i).  prover.
        nat_to_Z_tac. omega.
      prover.
  Qed.

  Lemma simple_parse_aux_corr_parse_instr_aux : 
   forall bytes ps pre ins len bytes1 s lc k consumed_len,
    simple_parse' ps bytes = Some ((pre,ins), bytes1)
      -> len = (length bytes - length bytes1)%nat
      -> eqMemBuffer (firstn len bytes) s lc
      -> (k >= len)%nat
      -> exists pos,
           parse_instr_aux k lc consumed_len ps s = (Okay_ans (pre, ins, pos), s) /\
           Zpos pos + 1 = Zpos consumed_len + Z_of_nat len.
  Proof. induction bytes as [ | b bytes']; intros.
    Case "nil". prover.
    Case "bytes = b::bytes'".
      use_lemma simple_parse'_len_pos by eassumption.
      assert (len <= length (b::bytes'))%nat by omega.
      assert (len > 0)%nat as H8 by omega.
      destruct len as [ | len]; [contradict H8; omega | idtac].
      compute [simple_parse'] in H. fold simple_parse' in H.
      remember_destruct_head in H as pb.
      destruct k; [contradict H2; omega | idtac].
      dupHyp H1; unfold eqMemBuffer in H1.
      destruct H1 as [H10 H12].
      rewrite firstn_S_cons in H12.
      assert (H20:b = AddrMap.get lc (rtl_memory s)).
        apply eq_trans with (y:= nth 0 (b::bytes') Word.zero).
          trivial.
          generalize (H12 O). simpl. intro H14.
            unfold w32add in H14.
            rewrite add_zero in H14.
          apply H14. omega.
      destruct l.
      SCase "parse_byte returns nil".
        assert (len = length bytes' - length bytes1)%nat.
          rewrite length_cons in H0. omega.
        assert (len <= length bytes')%nat by omega.
        assert (eqMemBuffer (firstn len bytes') s (lc +32_p 1)).
          eapply eqMemBuffer_succ; eassumption.
        assert (k >= len)%nat by omega.
        use_lemma IHbytes' by eassumption.
        destruct H11 as [pos [H30 H32]].
        exists pos.
        split.
          compute [parse_instr_aux]. fold parse_instr_aux.
          rtl_okay_intro.
          rewrite <- H20. rewrite Hpb.
          eassumption.
        rewrite Zpos_plus_distr in H32.
        rewrite inj_S. omega.
      SCase "parse_byte returns some v".
        exists consumed_len.
        split.
          SSCase "subgoal 1".
          compute [parse_instr_aux]. fold parse_instr_aux.
          rtl_okay_intro.
          rewrite <- H20. rewrite Hpb. prover.
          SSCase "subgoal 2".
          inv H.
          assert (len = 0)%nat.
            rewrite length_cons in H0.  omega.
          rewrite H. nat_to_Z_tac. omega.
  Qed.

  Lemma simple_parse_corr_parse_instr : 
   forall bytes pre ins len bytes1 s pc,
    simple_parse bytes = Some ((pre,ins), bytes1)
      -> len = (length bytes - length bytes1)%nat
      -> eqMemBuffer (firstn len bytes) s (CStart s +32 pc)
      -> (15 >= len)%nat
      -> exists pos,
           parse_instr pc s = (Okay_ans (pre, ins, pos), s) /\
           Zpos pos = Z_of_nat len.
  Proof. unfold simple_parse. intros.
    use_lemma simple_parse_aux_corr_parse_instr_aux by eassumption.
    destruct H3 as [pos [H10 H12]].
    exists pos. split.
      unfold parse_instr. rtl_okay_intro. eassumption. omega.
  Qed.

  Import ABSTRACT_MAKE_DFA.

  Lemma eqMemBuffer_skipn : forall n ls s lc,
    eqMemBuffer ls s lc -> eqMemBuffer (skipn n ls) s (lc +32_n n).
  Proof. unfold eqMemBuffer. intros. simplHyp.
    split.
      eapply Zle_trans. eapply inj_le. eapply skipn_length_leq. assumption.
      intros.
        destruct (le_or_lt (length ls) n).
        Case "length ls <= n".
          assert (n >= length ls)%nat by omega.
          apply skipn_nil in H3. 
          rewrite H3 in H1. simpl in H1. contradict H1. omega.
        Case "n < lenth ls".
          assert (length (skipn n ls) + n = length ls)%nat.
             eapply skipn_length. omega.
          assert (i + n < length ls)%nat by omega.
          eapply H0 in H4.
          rewrite skipn_nth. 
          assert (lc +32_n (i+n) = lc +32_n n +32_n i).
            unfold w32add. rewrite add_assoc. rewrite add_repr.
            rewrite inj_plus. rewrite Zplus_comm. trivial.
          prover.
  Qed.

  Lemma eqMemBuffer_firstn : forall n ls s lc,
    eqMemBuffer ls s lc -> eqMemBuffer (firstn n ls) s lc.
  Proof. unfold eqMemBuffer. intros. simplHyp.
    assert (length (firstn n ls) <= length ls)%nat.
      rewrite firstn_length. apply Min.le_min_r.
    split. omega.
      intros.
        assert (i<n)%nat. rewrite firstn_length in H2.
          eapply lt_le_trans. eassumption. 
          eapply Min.le_min_l.
        rewrite nth_firstn by assumption.
        eapply H0.  omega.
  Qed.

  Lemma simple_parse_parseloop_same : forall bytes ps,
    simple_parse' ps bytes = parseloop ps bytes.
  Proof. induction bytes; prover. Qed.

  Lemma token2byte_inv_byte2token : forall b,
    FastVerifier.token2byte (FastVerifier.byte2token b) = b.
  Proof. unfold FastVerifier.token2byte, FastVerifier.byte2token. intros.
    rewrite inj_Zabs_nat. rewrite Zabs_eq. rewrite repr_unsigned. trivial.
    generalize (unsigned_range b). prover.
  Qed.

  Lemma list_map_token_byte : forall bytes,
    List.map (fun x  => FastVerifier.token2byte (FastVerifier.byte2token x)) bytes
      = bytes.
  Proof. induction bytes. prover.
    simpl. rewrite token2byte_inv_byte2token. prover.
  Qed.

  (* todo: two defs of byte2token in FastVerifier.v and DFACorrectness.v;
     should remove one of them *)
  Lemma byte2token_same : forall l,
    List.map byte2token l = List.map FastVerifier.byte2token l.
  Proof. unfold byte2token, FastVerifier.byte2token. 
    induction l; prover.
  Qed.
 
  Remark aligned_bool_proper: 
    Morphisms.Proper ((fun x y : Int32_OT.t => eq x y = true) ==> Logic.eq)
      aligned_bool.
  Proof. unfold Morphisms.Proper, Morphisms.respectful.
    intros. apply int_eq_true_iff2 in H. prover.
  Qed.

  Lemma goodJmp_lemma : forall pc len bytes jmpTargets startAddrs pre ins rem,
    dir_cflow_instr pre ins = true 
      -> simple_parse bytes = Some (pre, ins, rem)
      -> len = (length bytes - length rem)%nat
      -> includeAllJmpTargets pc len (List.map byte2token bytes) jmpTargets
      -> checkJmpTargets jmpTargets startAddrs = true
      -> goodJmp ins (pc +32_n len) startAddrs = true.
  Proof. intros.
    assert (firstn len bytes = firstn len (firstn len bytes)).
      rewrite firstn_twice_eq by omega. trivial.
    use_lemma simple_parse'_ext by eassumption.
    destruct H5 as [rem1 H10].
    rewrite simple_parse_parseloop_same in H10.
    rewrite <- (list_map_token_byte bytes) in H10.
    rewrite <- list_map_compose in H10.
    rewrite firstn_map in H10.
    rewrite <- byte2token_same in H10.
    unfold goodJmp, checkJmpTargets in *.
    destruct ins; simpl in H; try congruence.
    Case "CALL".
      destruct near; try congruence.
      destruct absolute; try congruence.
      destruct op1; try congruence.
      destruct sel; try congruence.
      unfold includeAllJmpTargets in H2.
      rewrite H10 in H2.
      unfold goodJmpTarget.
      remember_rev (Int32Set.mem (pc +32_n len +32 i) startAddrs) as ab.
      destruct ab. prover.
        apply orb_true_intro. right.
        assert (Int32Set.In (pc +32_n len +32 i) 
                  (Int32Set.diff jmpTargets startAddrs)).
          apply Int32Set.diff_spec. split. assumption.
          apply Int32SetFacts.not_mem_iff. assumption.
        apply Int32Set.for_all_spec in H3. auto. apply aligned_bool_proper.
    Case "Jcc".
      unfold includeAllJmpTargets in H2.
      rewrite H10 in H2.
      unfold goodJmpTarget.
      remember_rev (Int32Set.mem (pc +32_n len +32 disp) startAddrs) as ab.
      destruct ab. prover.
        apply orb_true_intro. right.
        assert (Int32Set.In (pc +32_n len +32 disp) 
                  (Int32Set.diff jmpTargets startAddrs)).
          apply Int32Set.diff_spec. split. assumption.
          apply Int32SetFacts.not_mem_iff. assumption.
        apply Int32Set.for_all_spec in H3. auto. apply aligned_bool_proper.
    Case "Jmp".
      destruct near; try congruence.
      destruct absolute; try congruence.
      destruct op1; try congruence.
      destruct sel; try congruence.
      unfold includeAllJmpTargets in H2.
      rewrite H10 in H2.
      unfold goodJmpTarget.
      remember_rev (Int32Set.mem (pc +32_n len +32 i) startAddrs) as ab.
      destruct ab. prover.
        apply orb_true_intro. right.
        assert (Int32Set.In (pc +32_n len +32 i) 
                  (Int32Set.diff jmpTargets startAddrs)).
          apply Int32Set.diff_spec. split. assumption.
          apply Int32SetFacts.not_mem_iff. assumption.
        apply Int32Set.for_all_spec in H3. auto. apply aligned_bool_proper.
  Qed.


  Lemma parse_instr_imp_fetch_instr : 
    forall pc pre ins pos s,
      parse_instr pc s = (Okay_ans (pre, ins, pos), s)
        -> unsigned pc + Zpos pos <= unsigned (CLimit s) + 1
        -> fetch_instruction pc s = (Okay_ans (pre, ins, pos), s).
  Proof. intros.
    int32_simplify.
    assert (0 <= Zpos pos - 1 < w32modulus). 
      generalize (Zgt_pos_0 pos).  omega.
    assert (noOverflow (pc :: (repr (Zpos pos - 1)) :: nil)).
      int32_simplify. omega.
    assert (pc <=32 (pc +32_z (Zpos pos - 1))).
      apply checkNoOverflow_equiv_noOverflow. assumption.
    assert (pc +32_z (Zpos pos - 1) <=32 (CLimit s)).
      int32_simplify. omega.
    unfold fetch_instruction. 
    eapply rtl_bind_okay_intro; [eassumption | idtac].
    remember_destruct_head as pl. inversion Hpl. subst p0 p.
    rtl_okay_intro. 
    rewrite H6. rewrite H5. simpl. reflexivity.
  Qed.

  (* Including the following hypotheses in the context will make
     some tactics such as discriminate extremely slow since they will
     try to evaluate terms such as opt_dir_cflow_dfa, which are
     huge terms.*)
  Hypothesis non_cflow_dfa_built: 
    abstract_build_dfa 256 nat2bools 400 (par2rec non_cflow_parser)
      = Some non_cflow_dfa.

  Hypothesis dir_cflow_dfa_built: 
    abstract_build_dfa 256 nat2bools 400 (par2rec (alts dir_cflow))
      = Some dir_cflow_dfa.

  Hypothesis nacljmp_dfa_built: 
    abstract_build_dfa 256 nat2bools 400 (par2rec (alts nacljmp_mask))
      = Some nacljmp_dfa.

  Ltac clean := 
    clear non_cflow_dfa_built; clear dir_cflow_dfa_built; clear nacljmp_dfa_built.

  (* The three cases when the current state is a safe state *)
  (* The proof theorem needs the interface lemmas from the parser;
     will prove this theorem when the lemmmas become stable *)
  Theorem safeState_next_instr : forall s code startAddrs,
    codeLoaded code s
      -> checkProgram code = (true, startAddrs)
      -> Int32Set.In (PC s) startAddrs
      -> (exists pre, exists ins, exists len, 
           fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
           /\ non_cflow_instr pre ins = true
           /\ goodDefaultPC ((PC s) +32_p len) startAddrs (length code))
         \/
         (exists pre, exists ins, exists len, 
           fetch_instruction (PC s) s = (Okay_ans (pre, ins, len), s)
           /\ dir_cflow_instr pre ins = true
           /\ goodDefaultPC ((PC s) +32_p len) startAddrs (length code)
           /\ goodJmp ins ((PC s) +32_p len) startAddrs = true)
         \/ 
         (exists pre1, exists ins1, exists len1, 
          exists pre2, exists ins2, exists len2,
          fetch_instruction (PC s) s = (Okay_ans (pre1, ins1, len1), s) /\
          fetch_instruction (PC s +32_p len1) s = (Okay_ans (pre2, ins2, len2), s) /\
          nacljmp_mask_instr pre1 ins1 pre2 ins2 = true).
  Proof. unfold checkProgram, FastVerifier.checkProgram; intros.
    remember_destruct_head in H0 as pb; try discriminate.
    destruct p as [startAddrs' checkAddrs].
    assert (startAddrs = startAddrs') by congruence.
    subst startAddrs'. 
    use_lemma codeLoaded_length by eassumption.
    use_lemma process_buffer_inversion by eassumption.
    destruct H3 as [tokens [len [remaining [H20 [H22 H24]]]]].
    rewrite <- skipn_map in H20.
    remember (skipn (nat_of_int32 (PC s)) code) as code'.
    assert (PC s = repr (Z_of_nat (Zabs_nat (unsigned (PC s))))).
      rewrite inj_Zabs_nat. 
      generalize (unsigned_range (PC s)). intros.
      rewrite Zabs_eq by omega.
      rewrite repr_unsigned. trivial.
    assert (eqMemBuffer (firstn len code') s (CStart s +32 (PC s))).
      eapply eqMemBuffer_firstn. 
      subst code'. rewrite H3 at 2.
      apply eqMemBuffer_skipn. unfold codeLoaded in *. 
      simplHyp. assumption.
    use_lemma process_buffer_addrRange by eassumption.
    assert ((nat_of_int32 (PC s)) + length tokens = length code)%nat.
      rewrite H20. rewrite list_length_map. rewrite plus_comm.
      apply skipn_length. apply inj_lt_rev. int32_prover.
    destruct H24 as [H24 | [H24 | H24]].
    Case "non_cflow_dfa matches". left. 
      use_lemma non_cflow_dfa_corr by (subst tokens; eassumption).
      destruct H7 as [insBytes [pre [ins [H30 [H32 [H34 H36]]]]]].
      assert (len = length code' - length (List.map nat_to_byte remaining))%nat.
        apply plus_minus.  subst code'.
        rewrite H34. rewrite plus_comm.
        rewrite <- app_length. rewrite <- H36. trivial.
      assert (len <= 15)%nat. 
        eapply non_cflow_dfa_length. apply non_cflow_dfa_built.
          subst tokens. eassumption.
      subst code'.
      use_lemma simple_parse_corr_parse_instr by eassumption.
      destruct H9 as [pos [H40 H42]].
      assert (unsigned (PC s) + Zpos pos <= unsigned (CLimit s) + 1).
        use_lemma dfa_recognize_inv by eassumption. simplHyp.
        unfold codeLoaded in *. simplHyp.
        int32_simplify. omega.
      use_lemma parse_instr_imp_fetch_instr by eassumption.
      exists pre. exists ins. exists pos.
      split. assumption.
      split. assumption. 
        rewrite H42. assumption.
    Case "dir_cflow_dfa matches". right; left.
      simplHyp.
      use_lemma dir_cflow_dfa_corr by (subst tokens; eassumption).
      destruct H10 as [insBytes [pre [ins [H30 [H32 [H34 H36]]]]]].
      assert (len = length code' - length (List.map nat_to_byte remaining))%nat.
        apply plus_minus.  subst code'.
        rewrite H34. rewrite plus_comm.
        rewrite <- app_length. rewrite <- H36. trivial.
      assert (len <= 15)%nat. 
        eapply dir_cflow_dfa_length. apply dir_cflow_dfa_built.
          subst tokens. eassumption.
      subst code'.
      use_lemma simple_parse_corr_parse_instr by eassumption.
      destruct H12 as [pos [H40 H42]].
      assert (unsigned (PC s) + Zpos pos <= unsigned (CLimit s) + 1).
        use_lemma dfa_recognize_inv by eassumption. simplHyp.
        unfold codeLoaded in *. simplHyp.
        int32_simplify. omega.
      use_lemma parse_instr_imp_fetch_instr by eassumption.
      exists pre. exists ins. exists pos.
      split. assumption.
      split. assumption.  
      split. rewrite H42. assumption.
        injection H0. intros. bool_elim_tac.
        subst tokens.
        rewrite H42.
        eapply goodJmp_lemma; eassumption.
    Case "nacljmp_dfa matches". right; right.
      simplHyp.
      use_lemma NACLjmp.nacljmp_dfa_corr by (subst tokens; eassumption).
      destruct H8 as 
        [bytes1 [pre1 [ins1 [bytes [pre2 [ins2 [H30 [H32 [H34 [H36 H38]]]]]]]]]].
      rewrite app_length in H36.
      assert (len <= 15)%nat.
        eapply nacljmp_mask_dfa_length. eassumption.
          subst tokens. eassumption.
      assert (length bytes1 = 
                (length code' - length (bytes ++ List.map nat_to_byte remaining)))%nat.
        subst code'. apply plus_minus. rewrite plus_comm.
        rewrite <- app_length. rewrite <- H38. trivial.
      assert (eqMemBuffer (firstn (length bytes1) code') s (CStart s +32 (PC s))).
        rewrite <- firstn_twice_eq with (m:=len) by omega.
        apply eqMemBuffer_firstn. assumption.
      assert (15 >= length (bytes1))%nat by omega.
      generalize H32; clear H32. (* hide H32 for now *)
      use_lemma simple_parse_corr_parse_instr by (subst code'; eassumption).
      destruct H12 as [pos1 [H40 H42]].

      assert (unsigned (PC s) + Zpos pos1 <= unsigned (CLimit s) + 1).
        use_lemma dfa_recognize_inv by eassumption. simplHyp.
        unfold codeLoaded in *. simplHyp.
        int32_simplify. omega.
      use_lemma parse_instr_imp_fetch_instr by eassumption.

      intro H32. clear H30.
      assert (length bytes = 
                (length (bytes ++ List.map nat_to_byte remaining) - 
                 length (List.map nat_to_byte remaining)))%nat.
        apply plus_minus. rewrite plus_comm.
        rewrite <- app_length. trivial.
      assert (eqMemBuffer 
                (firstn (length bytes) (bytes ++ List.map nat_to_byte remaining))
                s (CStart s +32 (PC s) +32_n (length bytes1))).
        rewrite firstn_list_app by trivial.
        assert (bytes = skipn (length bytes1) (bytes1 ++ bytes)).
          rewrite skipn_list_app by trivial. trivial.
        rewrite H15 at 1.
        apply eqMemBuffer_skipn. 
        assert (firstn len code' = bytes1 ++ bytes)%list.
          subst code'.
          rewrite <- firstn_list_app with (n:=len) 
            (l2:= List.map nat_to_byte remaining).
          rewrite <- app_assoc. rewrite <- H38. trivial.
          rewrite app_length. omega.
        rewrite <- H16. assumption.
      unfold w32add in H15.
      rewrite add_assoc in H15.
      assert (15 >= length (bytes))%nat by omega.
      use_lemma simple_parse_corr_parse_instr by (subst code'; eassumption).
      destruct H17 as [pos2 [H50 H52]].

      use_lemma dfa_recognize_inv by eassumption. simplHyp.
      unfold codeLoaded in *. simplHyp.
      generalize (Zgt_pos_0 pos1) (Zgt_pos_0 pos2). intros.
      assert (Z_of_nat (length bytes1) < w32modulus). 
        int32_simplify. omega.
      assert (noOverflow (PC s :: int32_of_nat (length bytes1) :: nil)).
        int32_simplify.  omega.
      assert (unsigned (PC s +32 (int32_of_nat (length bytes1)))
                + Zpos pos2 <= unsigned (CLimit s) + 1).
        int32_simplify. omega.
      use_lemma parse_instr_imp_fetch_instr by eassumption.
      exists pre1. exists ins1. exists pos1. 
      exists pre2. exists ins2. exists pos2.
      split. assumption. 
      split. rewrite H42. assumption.
        assumption.
  Qed.

  (** ** the proof that any safeState is safe for in some k *)

  Lemma pc_out_bound_safeInSomeK : forall s inv,
    ~ inBoundCodeAddr (PC s) s -> safeState s inv -> safeInSomeK s inv.
  Proof. unfold safeInSomeK. intros.
    exists (S O). simpl.
    split. 
      unfold safeState in *. destruct inv. simplHyp. assumption.
    split.
      unfold nextStepNoFail. intros. contradict H.
        eapply step_fail_pc_inBound; eassumption.
      intros. left. contradict H.
        eapply step_immed_pc_inBound; eassumption.
  Qed.

  Lemma fetch_instruction_dichotomy : forall pc s pre ins len,
    parse_instr pc s = (Okay_ans (pre, ins, len), s)
      -> fetch_instruction pc s = (Okay_ans (pre, ins, len), s) \/
         fetch_instruction pc s = (SafeFail_ans _, s).
  Proof. intros.
    remember_rev (andb (int32_lequ_bool pc (pc +32 repr (Zpos len - 1)))
                    (int32_lequ_bool (pc +32 repr (Zpos len - 1)) (CLimit s)))
      as rb.
    destruct rb; unfold fetch_instruction.
    left. 
      eapply rtl_bind_okay_intro; [eassumption | idtac].
      remember_destruct_head as pl. inv Hpl.
      rtl_okay_intro. rewrite Hrb. reflexivity.
    right. 
      eapply rtl_bind_safefail_intro1. eassumption.
      remember_destruct_head as pl. inv Hpl.
      unfold Bind at 1; unfold RTL_monad at 1.
      rewrite in_seg_bounds_rng_equation.
      rewrite Hrb. trivial.
  Qed.   


  Ltac unroll_bind := unfold Bind at 1; unfold RTL_monad at 1.

(*
  Lemma step_fetch_instr_safefail : forall s,
    fetch_instruction (PC s) s = (SafeFail_ans _, s)
      -> inBoundCodeAddr (PC s) s
      -> exists s', step s = (SafeFail_ans _, s').
  Proof. intros. unfold step.
    unroll_bind.
    remember_destruct_head as fe.
    destruct r; try discriminate Hfe.
    rename r0 into s1.
    exists s1.
    unroll_bind. compute [get_loc].
    unroll_bind. rewrite in_seg_bounds_equation.
    compute [get_location].
    assert (int32_lequ_bool (PC s1) (CLimit s1) = true).
      unfold flush_env in Hfe. inv Hfe.
      simpl. unfold inBoundCodeAddr in H0. assumption.
    rewrite H1.
    unroll_bind.
*)    

  Lemma in_seg_bounds_rng_dichotomy : forall sreg a offset s,
    in_seg_bounds_rng sreg a offset s = (Okay_ans true, s) \/
    in_seg_bounds_rng sreg a offset s = (Okay_ans false, s).
  Proof. intros.
    rewrite in_seg_bounds_rng_equation.
    remember_rev (andb (int32_lequ_bool a (a +32 offset))
                    (int32_lequ_bool (a +32 offset) (SegLimit s sreg)))
      as rb.
    destruct rb. left. trivial.
      right. trivial.
  Qed.

  Lemma fetch_instruction_intro : forall pc s pre ins len,
    parse_instr pc s = (Okay_ans (pre, ins, len), s)
      -> in_seg_bounds_rng CS pc (repr (Zpos len - 1)) s = (Okay_ans true, s)
      -> fetch_instruction pc s = (Okay_ans (pre, ins, len), s).
  Proof. unfold fetch_instruction. intros.
    eapply rtl_bind_okay_intro; [eassumption | idtac].
    remember_destruct_head as pl. inv Hpl.
    unroll_bind. rewrite H0.
    reflexivity.
  Qed.



  Opaque Decode.X86_PARSER.parse_byte.
  Lemma parse_instr_aux_code_inv2 : forall n pc len ps s1 s1' pi len' s2,
    Same_Mem_Rel.brel s1 s2
      -> parse_instr_aux n pc len ps s1 = (Okay_ans (pi, len'), s1')
      -> parse_instr_aux n pc len ps s2 = (Okay_ans (pi, len'), s2).
  Proof. clean. induction n; intros.
    Case "n=0". discriminate.
    Case "S n". simpl in H0. simpl.
      rewrite <- H.
      remember_destruct_head as pr.
      destruct l. 
      SCase "l=nil". eauto.
      SCase "l<>nil". prover.
  Qed.

  Lemma parse_instr_code_inv2 : forall pc s1 s1' pi len' s2,
    Same_Mem_Rel.brel s1 s2
      -> Same_Mach_State_Rel.brel s1 s2
      -> parse_instr pc s1 = (Okay_ans (pi, len'), s1')
      -> parse_instr pc s2 = (Okay_ans (pi, len'), s2).
  Proof. clean. unfold parse_instr. intros.
    rtl_okay_elim.
    rtl_okay_intro.
    eapply parse_instr_aux_code_inv2. eassumption.
      rewrite <- H0. eassumption.
  Qed.
  Transparent Decode.X86_PARSER.parse_byte.

  (* The proof of this theorem needs to perform case analysis over
     the current pseudo instruction *)
  Theorem safeState_safeInK: 
    forall s inv, safeState s inv -> safeInSomeK s inv.
  Proof. intros. clean. dupHyp H.
    safestate_unfold_tac.
    remember (snd (checkProgram code)) as startAddrs.
    destruct H2.
    Case "pc in startAddrs".
      assert (checkProgram code = (true, startAddrs)).
        destruct (checkProgram code); prover.
      use_lemma safeState_next_instr by eassumption.
      destruct H7. 
      SCase "Next: non_cflow_instr".
        destruct H7 as [pre [ins [len [H20 [H22 H24]]]]].
        eapply nci_safeInSomeK; eassumption.
      destruct H7.
      SCase "Next: dir_cflow_instr".
        destruct H7 as [pre [ins [len [H20 [H22 [H24 H26]]]]]].
          eapply dci_safeInSomeK; try eassumption. prover.
      SCase "Next: nacljmp".
        destruct H7 as [pre1 [ins1 [len1 [pre2 [ins2 [len2 [H20 [H22 H24]]]]]]]].
            eapply nacljmp_safeInSomeK. eapply H20. eapply H22. eassumption.
              assumption.
    Case "pc is out of bound".
      apply pc_out_bound_safeInSomeK. assumption. assumption.
  Qed.

  Lemma safeInSomeK_preservation : forall s s' inv,
    s ==>* s' -> safeInSomeK s inv -> safeInSomeK s' inv.
  Proof. intros s s' inv Heval. induction Heval as [s s'| | s s1 s']; intros.
    Case "s ==> s'". unfold safeInSomeK in H0. destruct H0 as [k H0].
      use_lemma safeInK_step_dichotomy by eassumption.
      destruct H1. apply safeState_safeInK; assumption. assumption.
    Case "s' = s". assumption.
    Case "s ==>* s1 ==>* s'". tauto.
  Qed.

  Theorem safeState_no_fail : forall s s' inv,
    safeState s inv -> s ==>* s' -> nextStepNoFail s'.
  Proof. intros. eapply safeInSomeK_no_fail.
    eapply safeInSomeK_preservation. eassumption.
     apply safeState_safeInK in H; eassumption.
  Qed.


  Theorem safeState_appropState : forall s s' inv,
    safeState s inv -> s ==>* s' -> appropState s' inv.
  Proof. intros. clean.
    use_lemma safeState_safeInK by eassumption.
    use_lemma safeInSomeK_preservation by eassumption.
    unfold safeInSomeK in H2.
    destruct H2 as [k H10]. 
    destruct k. simpl in H10. contradict H10.
      simpl in H10. prover.
  Qed.

End VERIFIER_CORR.
