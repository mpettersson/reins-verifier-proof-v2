type __ = Obj.t

val xorb : bool -> bool -> bool

val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a compSpecT =
| CompEqT
| CompLtT
| CompGtT

val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type 'a exc = 'a option

val value : 'a1 -> 'a1 option

val error : 'a1 option

val plus : int -> int -> int

val minus : int -> int -> int

type positive =
| XI of positive
| XO of positive
| XH

val psucc : positive -> positive

val pplus : positive -> positive -> positive

val pplus_carry : positive -> positive -> positive

val pmult_nat : positive -> int -> int

val nat_of_P : positive -> int

val p_of_succ_nat : int -> positive

val pdouble_minus_one : positive -> positive

type positive_mask =
| IsNul
| IsPos of positive
| IsNeg

val pdouble_plus_one_mask : positive_mask -> positive_mask

val pdouble_mask : positive_mask -> positive_mask

val pdouble_minus_two : positive -> positive_mask

val pminus_mask : positive -> positive -> positive_mask

val pminus_mask_carry : positive -> positive -> positive_mask

val pminus : positive -> positive -> positive

val pmult : positive -> positive -> positive

val pcompare : positive -> positive -> comparison -> comparison

val positive_eq_dec : positive -> positive -> bool

val le_gt_dec : int -> int -> bool

type z =
| Z0
| Zpos of positive
| Zneg of positive

val zplus : z -> z -> z

val zopp : z -> z

val zminus : z -> z -> z

val zmult : z -> z -> z

val zcompare : z -> z -> comparison

val zabs_nat : z -> int

val z_of_nat : int -> z

val iter_nat : int -> ('a1 -> 'a1) -> 'a1 -> 'a1

val ztrichotomy_inf : z -> z -> bool option

module type OrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> comparison
  
  val eq_dec : t -> t -> bool
 end

module type OrderedType' = 
 sig 
  type t 
  
  val compare : t -> t -> comparison
  
  val eq_dec : t -> t -> bool
 end

module OT_to_Full : 
 functor (O:OrderedType') ->
 sig 
  type t = O.t
  
  val compare : t -> t -> comparison
  
  val eq_dec : t -> t -> bool
 end

val zcompare_rect :
  z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

val zcompare_rec : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

val z_eq_dec : z -> z -> bool

val z_lt_dec : z -> z -> bool

val z_le_dec : z -> z -> bool

val z_gt_dec : z -> z -> bool

val z_ge_dec : z -> z -> bool

val z_lt_ge_dec : z -> z -> bool

val z_le_gt_dec : z -> z -> bool

val z_gt_le_dec : z -> z -> bool

val z_ge_lt_dec : z -> z -> bool

val zge_bool : z -> z -> bool

val zgt_bool : z -> z -> bool

val zeq_bool : z -> z -> bool

module OT_to_OrderTac : 
 functor (OT:OrderedType) ->
 sig 
  module OTF : 
   sig 
    type t = OT.t
    
    val compare : t -> t -> comparison
    
    val eq_dec : t -> t -> bool
   end
  
  module TO : 
   sig 
    type t = OTF.t
    
    val compare : t -> t -> comparison
    
    val eq_dec : t -> t -> bool
   end
 end

module OrderedTypeFacts : 
 functor (O:OrderedType') ->
 sig 
  module OrderTac : 
   sig 
    module OTF : 
     sig 
      type t = O.t
      
      val compare : t -> t -> comparison
      
      val eq_dec : t -> t -> bool
     end
    
    module TO : 
     sig 
      type t = OTF.t
      
      val compare : t -> t -> comparison
      
      val eq_dec : t -> t -> bool
     end
   end
  
  val eq_dec : O.t -> O.t -> bool
  
  val lt_dec : O.t -> O.t -> bool
  
  val eqb : O.t -> O.t -> bool
 end

val zmax : z -> z -> z

val bool_dec : bool -> bool -> bool

val iter_pos : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1

val nth : int -> 'a1 list -> 'a1 -> 'a1

val nth_error : 'a1 list -> int -> 'a1 exc

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val firstn : int -> 'a1 list -> 'a1 list

val skipn : int -> 'a1 list -> 'a1 list

val shift_nat : int -> positive -> positive

val shift_pos : positive -> positive -> positive

val two_power_nat : int -> z

val two_power_pos : positive -> z

val two_p : z -> z

val zdiv_eucl_POS : positive -> z -> z * z

val zdiv_eucl : z -> z -> z * z

val zdiv : z -> z -> z

val zmod : z -> z -> z

val zeq : z -> z -> bool

val zlt : z -> z -> bool

val zle : z -> z -> bool

val proj_sumbool : bool -> bool

module type PARSER_ARG = 
 sig 
  type char_p 
  
  val char_eq : char_p -> char_p -> bool
  
  type tipe 
  
  val tipe_eq : tipe -> tipe -> bool
  
  type tipe_m 
 end

module Parser : 
 functor (PA:PARSER_ARG) ->
 sig 
  type result =
  | Coq_unit_t
  | Coq_char_t
  | Coq_pair_t of result * result
  | Coq_list_t of result
  | Coq_sum_t of result * result
  | Coq_tipe_t of PA.tipe
  
  val result_rect :
    'a1 -> 'a1 -> (result -> 'a1 -> result -> 'a1 -> 'a1) -> (result -> 'a1
    -> 'a1) -> (result -> 'a1 -> result -> 'a1 -> 'a1) -> (PA.tipe -> 'a1) ->
    result -> 'a1
  
  val result_rec :
    'a1 -> 'a1 -> (result -> 'a1 -> result -> 'a1 -> 'a1) -> (result -> 'a1
    -> 'a1) -> (result -> 'a1 -> result -> 'a1 -> 'a1) -> (PA.tipe -> 'a1) ->
    result -> 'a1
  
  val result_eq : result -> result -> bool
  
  type result_m = __
  
  type coq_parser =
  | Any_p
  | Char_p of PA.char_p
  | Eps_p
  | Cat_p of result * result * coq_parser * coq_parser
  | Zero_p of result
  | Alt_p of result * coq_parser * coq_parser
  | Star_p of result * coq_parser
  | Map_p of result * result * (result_m -> result_m) * coq_parser
  
  val parser_rect :
    'a1 -> (PA.char_p -> 'a1) -> 'a1 -> (result -> result -> coq_parser ->
    'a1 -> coq_parser -> 'a1 -> 'a1) -> (result -> 'a1) -> (result ->
    coq_parser -> 'a1 -> coq_parser -> 'a1 -> 'a1) -> (result -> coq_parser
    -> 'a1 -> 'a1) -> (result -> result -> (result_m -> result_m) ->
    coq_parser -> 'a1 -> 'a1) -> result -> coq_parser -> 'a1
  
  val parser_rec :
    'a1 -> (PA.char_p -> 'a1) -> 'a1 -> (result -> result -> coq_parser ->
    'a1 -> coq_parser -> 'a1 -> 'a1) -> (result -> 'a1) -> (result ->
    coq_parser -> 'a1 -> coq_parser -> 'a1 -> 'a1) -> (result -> coq_parser
    -> 'a1 -> 'a1) -> (result -> result -> (result_m -> result_m) ->
    coq_parser -> 'a1 -> 'a1) -> result -> coq_parser -> 'a1
  
  type fn_name = int
  
  val fn_name_eq : int -> int -> bool
  
  type fn =
  | Fn_name of fn_name * result * result
  | Fn_const_char of PA.char_p
  | Fn_empty_list of result
  | Fn_cons of result
  | Fn_unit_left of result
  | Fn_unit_right of result
  | Fn_unit of result
  
  val fn_rect :
    (fn_name -> result -> result -> 'a1) -> (PA.char_p -> 'a1) -> (result ->
    'a1) -> (result -> 'a1) -> (result -> 'a1) -> (result -> 'a1) -> (result
    -> 'a1) -> result -> result -> fn -> 'a1
  
  val fn_rec :
    (fn_name -> result -> result -> 'a1) -> (PA.char_p -> 'a1) -> (result ->
    'a1) -> (result -> 'a1) -> (result -> 'a1) -> (result -> 'a1) -> (result
    -> 'a1) -> result -> result -> fn -> 'a1
  
  type regexp =
  | Any
  | Char of PA.char_p
  | Eps
  | Cat of result * result * regexp * regexp
  | Alt of result * regexp * regexp
  | Zero of result
  | Star of result * regexp
  | Map of result * result * fn * regexp
  
  val regexp_rect :
    'a1 -> (PA.char_p -> 'a1) -> 'a1 -> (result -> result -> regexp -> 'a1 ->
    regexp -> 'a1 -> 'a1) -> (result -> regexp -> 'a1 -> regexp -> 'a1 ->
    'a1) -> (result -> 'a1) -> (result -> regexp -> 'a1 -> 'a1) -> (result ->
    result -> fn -> regexp -> 'a1 -> 'a1) -> result -> regexp -> 'a1
  
  val regexp_rec :
    'a1 -> (PA.char_p -> 'a1) -> 'a1 -> (result -> result -> regexp -> 'a1 ->
    regexp -> 'a1 -> 'a1) -> (result -> regexp -> 'a1 -> regexp -> 'a1 ->
    'a1) -> (result -> 'a1) -> (result -> regexp -> 'a1 -> 'a1) -> (result ->
    result -> fn -> regexp -> 'a1 -> 'a1) -> result -> regexp -> 'a1
  
  val s2b : bool -> bool
  
  val fn_eq : result -> result -> fn -> result -> result -> fn -> bool
  
  val regexp_eq' : result -> regexp -> result -> regexp -> bool
  
  val regexp_eq : result -> regexp -> regexp -> bool
  
  type fn_result_m = result_m -> result_m
  
  type ctxt_t = (result * result, fn_result_m) sigT list
  
  val fn_result' : ctxt_t -> fn_name -> (result * result) option
  
  type void = unit (* empty inductive *)
  
  val void_rect : void -> 'a1
  
  val void_rec : void -> 'a1
  
  type fn_result_m_opt = __
  
  val lookup_fn' : fn_name -> ctxt_t -> fn_result_m_opt
  
  val fn_result : ctxt_t -> fn_name -> (result * result) option
  
  val lookup_fn : ctxt_t -> fn_name -> fn_result_m_opt
  
  val apply_fn : ctxt_t -> result -> result -> fn -> result_m -> result_m
  
  val coq_OptCat_r : result -> result -> regexp -> regexp -> regexp
  
  val coq_OptCat : result -> result -> regexp -> regexp -> regexp
  
  val coq_OptAlt_r : result -> regexp -> regexp -> regexp
  
  val coq_OptAlt : result -> regexp -> regexp -> regexp
  
  val coq_MapUnit : result -> regexp -> regexp
  
  val coq_OptMap' : result -> result -> fn -> regexp -> regexp
  
  val coq_OptMap : result -> result -> fn -> regexp -> regexp
  
  val coerce_reg : result -> result -> regexp -> regexp
  
  val coerce_val : result -> result -> result_m -> result_m
  
  val eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2
  
  val null : result -> regexp -> regexp
  
  val coq_OptCatDelayed :
    result -> result -> regexp -> (PA.char_p -> regexp) -> PA.char_p ->
    regexp
  
  val deriv : result -> regexp -> PA.char_p -> regexp
  
  val accepts_null : result -> regexp -> bool
  
  val unit_deriv : result -> regexp -> PA.char_p -> regexp
  
  val unit_derivs : regexp -> PA.char_p list -> regexp
  
  val apply_null : ctxt_t -> result -> regexp -> result_m list
  
  val deriv_parse' : result -> regexp -> PA.char_p list -> regexp
  
  val deriv_parse :
    ctxt_t -> result -> regexp -> PA.char_p list -> result_m list
  
  type coq_DFA = { dfa_num_states : int; dfa_states : regexp list;
                   dfa_transition : int list list; dfa_accepts : bool list;
                   dfa_rejects : bool list }
  
  val coq_DFA_rect :
    (int -> regexp list -> int list list -> bool list -> bool list -> 'a1) ->
    coq_DFA -> 'a1
  
  val coq_DFA_rec :
    (int -> regexp list -> int list list -> bool list -> bool list -> 'a1) ->
    coq_DFA -> 'a1
  
  val dfa_num_states : coq_DFA -> int
  
  val dfa_states : coq_DFA -> regexp list
  
  val dfa_transition : coq_DFA -> int list list
  
  val dfa_accepts : coq_DFA -> bool list
  
  val dfa_rejects : coq_DFA -> bool list
  
  type token_id = int
  
  type states = regexp list
  
  val find_index' : regexp -> int -> states -> int option
  
  val find_index : regexp -> states -> int option
  
  val find_or_add : regexp -> states -> states * int
  
  val gen_row' :
    (token_id -> PA.char_p list) -> int -> regexp -> states -> token_id ->
    states * int list
  
  val gen_row :
    int -> (token_id -> PA.char_p list) -> regexp -> states -> states * int
    list
  
  val build_table' :
    int -> (token_id -> PA.char_p list) -> int -> states -> int list list ->
    int -> (states * int list list) option
  
  val build_transition_table :
    int -> (token_id -> PA.char_p list) -> int -> regexp -> (states * int
    list list) option
  
  val build_accept_table : states -> bool list
  
  val always_rejects : result -> regexp -> bool
  
  val build_rejects : states -> bool list
  
  val build_dfa :
    int -> (token_id -> PA.char_p list) -> int -> regexp -> coq_DFA option
  
  val dfa_loop :
    int -> coq_DFA -> int -> int -> token_id list -> (int * token_id list)
    option
  
  val dfa_recognize :
    int -> coq_DFA -> token_id list -> (int * token_id list) option
  
  val par2rec : result -> coq_parser -> regexp
  
  val recognize : ctxt_t -> result -> coq_parser -> PA.char_p list -> bool
  
  val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list
  
  val run_dfa : int -> coq_DFA -> int -> token_id list -> bool
  
  val accepts_at_most_one_null : ctxt_t -> result -> regexp -> bool
  
  val enum_tokens : (token_id -> bool) -> int -> bool
  
  val forall_tokens : int -> (token_id -> bool) -> bool
  
  val extend_state :
    ctxt_t -> result -> result -> fn_result_m -> fn_name * ctxt_t
  
  val par2reg : result -> coq_parser -> ctxt_t -> regexp * ctxt_t
  
  val initial_ctxt : ctxt_t
  
  val parser2regexp : result -> coq_parser -> regexp * ctxt_t
  
  val parse : result -> coq_parser -> PA.char_p list -> result_m list
 end

type 'x compare0 =
| LT
| EQ
| GT

module type Coq_OrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> t compare0
  
  val eq_dec : t -> t -> bool
 end

module Word : 
 sig 
  val wordsize : int -> int
  
  val modulus : int -> z
  
  val half_modulus : int -> z
  
  type comparison =
  | Ceq
  | Cne
  | Clt
  | Cle
  | Cgt
  | Cge
  
  val comparison_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> comparison -> 'a1
  
  val comparison_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> comparison -> 'a1
  
  val negate_comparison : comparison -> comparison
  
  val swap_comparison : comparison -> comparison
  
  type wint =
    z
    (* singleton inductive, whose constructor was mkint *)
  
  val wint_rect : int -> (z -> __ -> 'a1) -> wint -> 'a1
  
  val wint_rec : int -> (z -> __ -> 'a1) -> wint -> 'a1
  
  val intval : int -> wint -> z
  
  val max_unsigned : int -> z
  
  val max_signed : int -> z
  
  val min_signed : int -> z
  
  val unsigned : int -> wint -> z
  
  val signed : int -> wint -> z
  
  val repr : int -> z -> wint
  
  val zero : int -> wint
  
  val one : int -> wint
  
  val mone : int -> wint
  
  val eq_dec : int -> wint -> wint -> bool
  
  val eq : int -> wint -> wint -> bool
  
  val lt : int -> wint -> wint -> bool
  
  val ltu : int -> wint -> wint -> bool
  
  val lequ : int -> wint -> wint -> bool
  
  val neg : int -> wint -> wint
  
  val zero_ext : int -> z -> wint -> wint
  
  val sign_ext : int -> z -> wint -> wint
  
  val add : int -> wint -> wint -> wint
  
  val sub : int -> wint -> wint -> wint
  
  val mul : int -> wint -> wint -> wint
  
  val coq_Zdiv_round : z -> z -> z
  
  val coq_Zmod_round : z -> z -> z
  
  val divs : int -> wint -> wint -> wint
  
  val mods : int -> wint -> wint -> wint
  
  val divu : int -> wint -> wint -> wint
  
  val modu : int -> wint -> wint -> wint
  
  val bool_to_int : int -> bool -> wint
  
  val unsigned_overflow : int -> z -> z -> bool
  
  val unsigned_overflow_with_carry : int -> z -> z -> bool -> bool
  
  val signed_overflow : int -> z -> z -> bool
  
  val signed_overflow_with_carry : int -> z -> z -> bool -> bool
  
  val signed_overflow_with_borrow : int -> z -> z -> bool -> bool
  
  val is_zero : int -> wint -> bool
  
  val is_signed : int -> wint -> bool
  
  val coq_Z_shift_add : bool -> z -> z
  
  val coq_Z_bin_decomp : z -> bool * z
  
  val bits_of_Z : int -> z -> z -> bool
  
  val coq_Z_of_bits : int -> (z -> bool) -> z
  
  val bitwise_binop : int -> (bool -> bool -> bool) -> wint -> wint -> wint
  
  val coq_and : int -> wint -> wint -> wint
  
  val coq_or : int -> wint -> wint -> wint
  
  val xor : int -> wint -> wint -> wint
  
  val not : int -> wint -> wint
  
  val shl : int -> wint -> wint -> wint
  
  val shru : int -> wint -> wint -> wint
  
  val shr : int -> wint -> wint -> wint
  
  val shrx : int -> wint -> wint -> wint
  
  val shr_carry : int -> wint -> wint -> wint
  
  val rol : int -> wint -> wint -> wint
  
  val ror : int -> wint -> wint -> wint
  
  val rolm : int -> wint -> wint -> wint -> wint
  
  val coq_Z_one_bits : int -> z -> z -> z list
  
  val one_bits : int -> wint -> wint list
  
  val is_power2 : int -> wint -> wint option
  
  type rlw_state =
  | RLW_S0
  | RLW_S1
  | RLW_S2
  | RLW_S3
  | RLW_S4
  | RLW_S5
  | RLW_S6
  | RLW_Sbad
  
  val rlw_state_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> rlw_state -> 'a1
  
  val rlw_state_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> rlw_state -> 'a1
  
  val rlw_transition : rlw_state -> bool -> rlw_state
  
  val rlw_accepting : rlw_state -> bool
  
  val is_rlw_mask_rec : int -> rlw_state -> z -> bool
  
  val is_rlw_mask : int -> wint -> bool
  
  val cmp : int -> comparison -> wint -> wint -> bool
  
  val cmpu : int -> comparison -> wint -> wint -> bool
  
  val notbool : int -> wint -> wint
  
  val check_equal_on_range :
    int -> (wint -> wint) -> (wint -> wint) -> int -> bool
  
  val powerserie : z list -> z
  
  val int_of_one_bits : int -> wint list -> wint
 end

type int8 = Word.wint

type int16 = Word.wint

type int32 = Word.wint

module Int32_OT : 
 sig 
  type t = Word.wint
  
  val compare : t -> t -> t compare0
  
  val eq_dec : t -> t -> bool
 end

val length0 : char list -> int

val zero_extend8_32 : int8 -> int32

val sign_extend8_32 : int8 -> int32

val sign_extend16_32 : int16 -> int32

type port_number = int8

type interrupt_type = int8

type selector = int16

type register =
| EAX
| ECX
| EDX
| EBX
| ESP
| EBP
| ESI
| EDI

val z_to_register : z -> register

type scale =
| Scale1
| Scale2
| Scale4
| Scale8

val z_to_scale : z -> scale

type segment_register =
| ES
| CS
| SS
| DS
| FS
| GS

type control_register =
| CR0
| CR2
| CR3
| CR4

type debug_register =
| DR0
| DR1
| DR2
| DR3
| DR6
| DR7

type address = { addrDisp : int32; addrBase : register option;
                 addrIndex : (scale * register) option }

val addrDisp : address -> int32

val addrBase : address -> register option

val addrIndex : address -> (scale * register) option

type operand =
| Imm_op of int32
| Reg_op of register
| Address_op of address
| Offset_op of int32

type reg_or_immed =
| Reg_ri of register
| Imm_ri of int8

type condition_type =
| O_ct
| NO_ct
| B_ct
| NB_ct
| E_ct
| NE_ct
| BE_ct
| NBE_ct
| S_ct
| NS_ct
| P_ct
| NP_ct
| L_ct
| NL_ct
| LE_ct
| NLE_ct

val z_to_condition_type : z -> condition_type

type instr =
| AAA
| AAD
| AAM
| AAS
| ADC of bool * operand * operand
| ADD of bool * operand * operand
| AND of bool * operand * operand
| ARPL of operand * operand
| BOUND of operand * operand
| BSF of operand * operand
| BSR of operand * operand
| BSWAP of register
| BT of operand * operand
| BTC of operand * operand
| BTR of operand * operand
| BTS of operand * operand
| CALL of bool * bool * operand * selector option
| CDQ
| CLC
| CLD
| CLI
| CLTS
| CMC
| CMOVcc of condition_type * operand * operand
| CMP of bool * operand * operand
| CMPS of bool
| CMPXCHG of bool * operand * operand
| CPUID
| CWDE
| DAA
| DAS
| DEC of bool * operand
| DIV of bool * operand
| HLT
| IDIV of bool * operand
| IMUL of bool * operand * operand option * int32 option
| IN of bool * port_number option
| INC of bool * operand
| INS of bool
| INTn of interrupt_type
| INT
| INTO
| INVD
| INVLPG of operand
| IRET
| Jcc of condition_type * int32
| JCXZ of int8
| JMP of bool * bool * operand * selector option
| LAHF
| LAR of operand * operand
| LDS of operand * operand
| LEA of operand * operand
| LEAVE
| LES of operand * operand
| LFS of operand * operand
| LGDT of operand
| LGS of operand * operand
| LIDT of operand
| LLDT of operand
| LMSW of operand
| LODS of bool
| LOOP of int8
| LOOPZ of int8
| LOOPNZ of int8
| LSL of operand * operand
| LSS of operand * operand
| LTR of operand
| MOV of bool * operand * operand
| MOVCR of bool * control_register * register
| MOVDR of bool * debug_register * register
| MOVSR of bool * segment_register * operand
| MOVBE of operand * operand
| MOVS of bool
| MOVSX of bool * operand * operand
| MOVZX of bool * operand * operand
| MUL of bool * operand
| NEG of bool * operand
| NOP of operand option
| NOT of bool * operand
| OR of bool * operand * operand
| OUT of bool * port_number option
| OUTS of bool
| POP of operand
| POPSR of segment_register
| POPA
| POPF
| PUSH of bool * operand
| PUSHSR of segment_register
| PUSHA
| PUSHF
| RCL of bool * operand * reg_or_immed
| RCR of bool * operand * reg_or_immed
| RDMSR
| RDPMC
| RDTSC
| RDTSCP
| RET of bool * int16 option
| ROL of bool * operand * reg_or_immed
| ROR of bool * operand * reg_or_immed
| RSM
| SAHF
| SAR of bool * operand * reg_or_immed
| SBB of bool * operand * operand
| SCAS of bool
| SETcc of condition_type * operand
| SGDT of operand
| SHL of bool * operand * reg_or_immed
| SHLD of operand * register * reg_or_immed
| SHR of bool * operand * reg_or_immed
| SHRD of operand * register * reg_or_immed
| SIDT of operand
| SLDT of operand
| SMSW of operand
| STC
| STD
| STI
| STOS of bool
| STR of operand
| SUB of bool * operand * operand
| TEST of bool * operand * operand
| UD2
| VERR of operand
| VERW of operand
| WAIT
| WBINVD
| WRMSR
| XADD of bool * operand * operand
| XCHG of bool * operand * operand
| XLAT
| XOR of bool * operand * operand

type lock_or_rep =
| Lock
| Rep
| Repn

type prefix = { lock_rep : lock_or_rep option;
                seg_override : segment_register option; op_override : 
                bool; addr_override : bool }

val lock_rep : prefix -> lock_or_rep option

val seg_override : prefix -> segment_register option

val op_override : prefix -> bool

val addr_override : prefix -> bool

module X86_PARSER_ARG : 
 sig 
  type char_p = bool
  
  val char_eq : char_p -> char_p -> bool
  
  type coq_type =
  | Int_t
  | Register_t
  | Byte_t
  | Half_t
  | Word_t
  | Scale_t
  | Condition_t
  | Operand_t
  | Instruction_t
  | Control_Register_t
  | Debug_Register_t
  | Segment_Register_t
  | Lock_or_Rep_t
  | Bool_t
  | Prefix_t
  | Option_t of coq_type
  | Pair_t of coq_type * coq_type
  
  val type_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (coq_type -> 'a1 -> 'a1) -> (coq_type ->
    'a1 -> coq_type -> 'a1 -> 'a1) -> coq_type -> 'a1
  
  val type_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (coq_type -> 'a1 -> 'a1) -> (coq_type ->
    'a1 -> coq_type -> 'a1 -> 'a1) -> coq_type -> 'a1
  
  type tipe = coq_type
  
  val tipe_eq : tipe -> tipe -> bool
  
  type tipe_m = __
 end

module X86_PARSER : 
 sig 
  module X86_BASE_PARSER : 
   sig 
    type result =
    | Coq_unit_t
    | Coq_char_t
    | Coq_pair_t of result * result
    | Coq_list_t of result
    | Coq_sum_t of result * result
    | Coq_tipe_t of X86_PARSER_ARG.tipe
    
    val result_rect :
      'a1 -> 'a1 -> (result -> 'a1 -> result -> 'a1 -> 'a1) -> (result -> 'a1
      -> 'a1) -> (result -> 'a1 -> result -> 'a1 -> 'a1) ->
      (X86_PARSER_ARG.tipe -> 'a1) -> result -> 'a1
    
    val result_rec :
      'a1 -> 'a1 -> (result -> 'a1 -> result -> 'a1 -> 'a1) -> (result -> 'a1
      -> 'a1) -> (result -> 'a1 -> result -> 'a1 -> 'a1) ->
      (X86_PARSER_ARG.tipe -> 'a1) -> result -> 'a1
    
    val result_eq : result -> result -> bool
    
    type result_m = __
    
    type coq_parser =
    | Any_p
    | Char_p of X86_PARSER_ARG.char_p
    | Eps_p
    | Cat_p of result * result * coq_parser * coq_parser
    | Zero_p of result
    | Alt_p of result * coq_parser * coq_parser
    | Star_p of result * coq_parser
    | Map_p of result * result * (result_m -> result_m) * coq_parser
    
    val parser_rect :
      'a1 -> (X86_PARSER_ARG.char_p -> 'a1) -> 'a1 -> (result -> result ->
      coq_parser -> 'a1 -> coq_parser -> 'a1 -> 'a1) -> (result -> 'a1) ->
      (result -> coq_parser -> 'a1 -> coq_parser -> 'a1 -> 'a1) -> (result ->
      coq_parser -> 'a1 -> 'a1) -> (result -> result -> (result_m ->
      result_m) -> coq_parser -> 'a1 -> 'a1) -> result -> coq_parser -> 'a1
    
    val parser_rec :
      'a1 -> (X86_PARSER_ARG.char_p -> 'a1) -> 'a1 -> (result -> result ->
      coq_parser -> 'a1 -> coq_parser -> 'a1 -> 'a1) -> (result -> 'a1) ->
      (result -> coq_parser -> 'a1 -> coq_parser -> 'a1 -> 'a1) -> (result ->
      coq_parser -> 'a1 -> 'a1) -> (result -> result -> (result_m ->
      result_m) -> coq_parser -> 'a1 -> 'a1) -> result -> coq_parser -> 'a1
    
    type fn_name = int
    
    val fn_name_eq : int -> int -> bool
    
    type fn =
    | Fn_name of fn_name * result * result
    | Fn_const_char of X86_PARSER_ARG.char_p
    | Fn_empty_list of result
    | Fn_cons of result
    | Fn_unit_left of result
    | Fn_unit_right of result
    | Fn_unit of result
    
    val fn_rect :
      (fn_name -> result -> result -> 'a1) -> (X86_PARSER_ARG.char_p -> 'a1)
      -> (result -> 'a1) -> (result -> 'a1) -> (result -> 'a1) -> (result ->
      'a1) -> (result -> 'a1) -> result -> result -> fn -> 'a1
    
    val fn_rec :
      (fn_name -> result -> result -> 'a1) -> (X86_PARSER_ARG.char_p -> 'a1)
      -> (result -> 'a1) -> (result -> 'a1) -> (result -> 'a1) -> (result ->
      'a1) -> (result -> 'a1) -> result -> result -> fn -> 'a1
    
    type regexp =
    | Any
    | Char of X86_PARSER_ARG.char_p
    | Eps
    | Cat of result * result * regexp * regexp
    | Alt of result * regexp * regexp
    | Zero of result
    | Star of result * regexp
    | Map of result * result * fn * regexp
    
    val regexp_rect :
      'a1 -> (X86_PARSER_ARG.char_p -> 'a1) -> 'a1 -> (result -> result ->
      regexp -> 'a1 -> regexp -> 'a1 -> 'a1) -> (result -> regexp -> 'a1 ->
      regexp -> 'a1 -> 'a1) -> (result -> 'a1) -> (result -> regexp -> 'a1 ->
      'a1) -> (result -> result -> fn -> regexp -> 'a1 -> 'a1) -> result ->
      regexp -> 'a1
    
    val regexp_rec :
      'a1 -> (X86_PARSER_ARG.char_p -> 'a1) -> 'a1 -> (result -> result ->
      regexp -> 'a1 -> regexp -> 'a1 -> 'a1) -> (result -> regexp -> 'a1 ->
      regexp -> 'a1 -> 'a1) -> (result -> 'a1) -> (result -> regexp -> 'a1 ->
      'a1) -> (result -> result -> fn -> regexp -> 'a1 -> 'a1) -> result ->
      regexp -> 'a1
    
    val s2b : bool -> bool
    
    val fn_eq : result -> result -> fn -> result -> result -> fn -> bool
    
    val regexp_eq' : result -> regexp -> result -> regexp -> bool
    
    val regexp_eq : result -> regexp -> regexp -> bool
    
    type fn_result_m = result_m -> result_m
    
    type ctxt_t = (result * result, fn_result_m) sigT list
    
    val fn_result' : ctxt_t -> fn_name -> (result * result) option
    
    type void = unit (* empty inductive *)
    
    val void_rect : void -> 'a1
    
    val void_rec : void -> 'a1
    
    type fn_result_m_opt = __
    
    val lookup_fn' : fn_name -> ctxt_t -> fn_result_m_opt
    
    val fn_result : ctxt_t -> fn_name -> (result * result) option
    
    val lookup_fn : ctxt_t -> fn_name -> fn_result_m_opt
    
    val apply_fn : ctxt_t -> result -> result -> fn -> result_m -> result_m
    
    val coq_OptCat_r : result -> result -> regexp -> regexp -> regexp
    
    val coq_OptCat : result -> result -> regexp -> regexp -> regexp
    
    val coq_OptAlt_r : result -> regexp -> regexp -> regexp
    
    val coq_OptAlt : result -> regexp -> regexp -> regexp
    
    val coq_MapUnit : result -> regexp -> regexp
    
    val coq_OptMap' : result -> result -> fn -> regexp -> regexp
    
    val coq_OptMap : result -> result -> fn -> regexp -> regexp
    
    val coerce_reg : result -> result -> regexp -> regexp
    
    val coerce_val : result -> result -> result_m -> result_m
    
    val eq_rew_r_dep :
      'a1
      ->
      'a1
      ->
      'a2
      ->
      'a2
    
    val null :
      result
      ->
      regexp
      ->
      regexp
    
    val coq_OptCatDelayed :
      result
      ->
      result
      ->
      regexp
      ->
      (X86_PARSER_ARG.char_p
      ->
      regexp)
      ->
      X86_PARSER_ARG.char_p
      ->
      regexp
    
    val deriv :
      result
      ->
      regexp
      ->
      X86_PARSER_ARG.char_p
      ->
      regexp
    
    val accepts_null :
      result
      ->
      regexp
      ->
      bool
    
    val unit_deriv :
      result
      ->
      regexp
      ->
      X86_PARSER_ARG.char_p
      ->
      regexp
    
    val unit_derivs :
      regexp
      ->
      X86_PARSER_ARG.char_p
      list
      ->
      regexp
    
    val apply_null :
      ctxt_t
      ->
      result
      ->
      regexp
      ->
      result_m
      list
    
    val deriv_parse' :
      result
      ->
      regexp
      ->
      X86_PARSER_ARG.char_p
      list
      ->
      regexp
    
    val deriv_parse :
      ctxt_t
      ->
      result
      ->
      regexp
      ->
      X86_PARSER_ARG.char_p
      list
      ->
      result_m
      list
    
    type coq_DFA = { dfa_num_states : int;
                     dfa_states : regexp
                                  list;
                     dfa_transition : int
                                      list
                                      list;
                     dfa_accepts : bool
                                   list;
                     dfa_rejects : bool
                                   list }
    
    val coq_DFA_rect :
      (int
      ->
      regexp
      list
      ->
      int
      list
      list
      ->
      bool
      list
      ->
      bool
      list
      ->
      'a1)
      ->
      coq_DFA
      ->
      'a1
    
    val coq_DFA_rec :
      (int
      ->
      regexp
      list
      ->
      int
      list
      list
      ->
      bool
      list
      ->
      bool
      list
      ->
      'a1)
      ->
      coq_DFA
      ->
      'a1
    
    val dfa_num_states :
      coq_DFA
      ->
      int
    
    val dfa_states :
      coq_DFA
      ->
      regexp
      list
    
    val dfa_transition :
      coq_DFA
      ->
      int
      list
      list
    
    val dfa_accepts :
      coq_DFA
      ->
      bool
      list
    
    val dfa_rejects :
      coq_DFA
      ->
      bool
      list
    
    type token_id
      =
      int
    
    type states
      =
      regexp
      list
    
    val find_index' :
      regexp
      ->
      int
      ->
      states
      ->
      int
      option
    
    val find_index :
      regexp
      ->
      states
      ->
      int
      option
    
    val find_or_add :
      regexp
      ->
      states
      ->
      states * int
    
    val gen_row' :
      (token_id
      ->
      X86_PARSER_ARG.char_p
      list)
      ->
      int
      ->
      regexp
      ->
      states
      ->
      token_id
      ->
      states * int
      list
    
    val gen_row :
      int
      ->
      (token_id
      ->
      X86_PARSER_ARG.char_p
      list)
      ->
      regexp
      ->
      states
      ->
      states * int
      list
    
    val build_table' :
      int
      ->
      (token_id
      ->
      X86_PARSER_ARG.char_p
      list)
      ->
      int
      ->
      states
      ->
      int
      list
      list
      ->
      int
      ->
      (states * int
      list
      list)
      option
    
    val build_transition_table :
      int
      ->
      (token_id
      ->
      X86_PARSER_ARG.char_p
      list)
      ->
      int
      ->
      regexp
      ->
      (states * int
      list
      list)
      option
    
    val build_accept_table :
      states
      ->
      bool
      list
    
    val always_rejects :
      result
      ->
      regexp
      ->
      bool
    
    val build_rejects :
      states
      ->
      bool
      list
    
    val build_dfa :
      int
      ->
      (token_id
      ->
      X86_PARSER_ARG.char_p
      list)
      ->
      int
      ->
      regexp
      ->
      coq_DFA
      option
    
    val dfa_loop :
      int
      ->
      coq_DFA
      ->
      int
      ->
      int
      ->
      token_id
      list
      ->
      (int * token_id
      list)
      option
    
    val dfa_recognize :
      int
      ->
      coq_DFA
      ->
      token_id
      list
      ->
      (int * token_id
      list)
      option
    
    val par2rec :
      result
      ->
      coq_parser
      ->
      regexp
    
    val recognize :
      ctxt_t
      ->
      result
      ->
      coq_parser
      ->
      X86_PARSER_ARG.char_p
      list
      ->
      bool
    
    val flat_map :
      ('a1
      ->
      'a2
      list)
      ->
      'a1
      list
      ->
      'a2
      list
    
    val run_dfa :
      int
      ->
      coq_DFA
      ->
      int
      ->
      token_id
      list
      ->
      bool
    
    val accepts_at_most_one_null :
      ctxt_t
      ->
      result
      ->
      regexp
      ->
      bool
    
    val enum_tokens :
      (token_id
      ->
      bool)
      ->
      int
      ->
      bool
    
    val forall_tokens :
      int
      ->
      (token_id
      ->
      bool)
      ->
      bool
    
    val extend_state :
      ctxt_t
      ->
      result
      ->
      result
      ->
      fn_result_m
      ->
      fn_name * ctxt_t
    
    val par2reg :
      result
      ->
      coq_parser
      ->
      ctxt_t
      ->
      regexp * ctxt_t
    
    val initial_ctxt :
      ctxt_t
    
    val parser2regexp :
      result
      ->
      coq_parser
      ->
      regexp * ctxt_t
    
    val parse :
      result
      ->
      coq_parser
      ->
      X86_PARSER_ARG.char_p
      list
      ->
      result_m
      list
   end
  
  val option_t :
    X86_PARSER_ARG.coq_type
    ->
    X86_BASE_PARSER.result
  
  val int_t :
    X86_BASE_PARSER.result
  
  val register_t :
    X86_BASE_PARSER.result
  
  val byte_t :
    X86_BASE_PARSER.result
  
  val half_t :
    X86_BASE_PARSER.result
  
  val word_t :
    X86_BASE_PARSER.result
  
  val scale_t :
    X86_BASE_PARSER.result
  
  val condition_t :
    X86_BASE_PARSER.result
  
  val operand_t :
    X86_BASE_PARSER.result
  
  val instruction_t :
    X86_BASE_PARSER.result
  
  val control_register_t :
    X86_BASE_PARSER.result
  
  val debug_register_t :
    X86_BASE_PARSER.result
  
  val segment_register_t :
    X86_BASE_PARSER.result
  
  val lock_or_rep_t :
    X86_BASE_PARSER.result
  
  val bool_t :
    X86_BASE_PARSER.result
  
  val prefix_t :
    X86_BASE_PARSER.result
  
  val bit :
    bool
    ->
    X86_BASE_PARSER.coq_parser
  
  val never :
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.coq_parser
  
  val always :
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.result_m
    ->
    X86_BASE_PARSER.coq_parser
  
  val alt :
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
  
  val alts :
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.coq_parser
    list
    ->
    X86_BASE_PARSER.coq_parser
  
  val map :
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.coq_parser
    ->
    (X86_BASE_PARSER.result_m
    ->
    X86_BASE_PARSER.result_m)
    ->
    X86_BASE_PARSER.coq_parser
  
  val seq :
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
  
  val cons :
    X86_BASE_PARSER.result
    ->
    (__ * __
    list)
    ->
    __
    list
  
  val seqs :
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.coq_parser
    list
    ->
    X86_BASE_PARSER.coq_parser
  
  val string_to_bool_list :
    char list
    ->
    bool
    list
  
  val bits_n :
    int
    ->
    X86_BASE_PARSER.result
  
  val field' :
    int
    ->
    X86_BASE_PARSER.coq_parser
  
  val bits2Z :
    int
    ->
    z
    ->
    X86_BASE_PARSER.result_m
    ->
    X86_BASE_PARSER.result_m
  
  val bits2int :
    int
    ->
    X86_BASE_PARSER.result_m
    ->
    X86_BASE_PARSER.result_m
  
  val bits :
    char list
    ->
    X86_BASE_PARSER.coq_parser
  
  val bitsleft :
    X86_BASE_PARSER.result
    ->
    char list
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
  
  val anybit :
    X86_BASE_PARSER.coq_parser
  
  val field :
    int
    ->
    X86_BASE_PARSER.coq_parser
  
  val reg :
    X86_BASE_PARSER.coq_parser
  
  val byte :
    X86_BASE_PARSER.coq_parser
  
  val halfword :
    X86_BASE_PARSER.coq_parser
  
  val word :
    X86_BASE_PARSER.coq_parser
  
  val scale_p :
    X86_BASE_PARSER.coq_parser
  
  val tttn :
    X86_BASE_PARSER.coq_parser
  
  val reg_no_esp :
    X86_BASE_PARSER.coq_parser
  
  val reg_no_ebp :
    X86_BASE_PARSER.coq_parser
  
  val si :
    X86_BASE_PARSER.coq_parser
  
  val sib :
    X86_BASE_PARSER.coq_parser
  
  val rm00 :
    X86_BASE_PARSER.coq_parser
  
  val rm01 :
    X86_BASE_PARSER.coq_parser
  
  val rm10 :
    X86_BASE_PARSER.coq_parser
  
  val rm11 :
    X86_BASE_PARSER.coq_parser
  
  val modrm :
    X86_BASE_PARSER.coq_parser
  
  val modrm_noreg :
    X86_BASE_PARSER.coq_parser
  
  val ext_op_modrm :
    char list
    ->
    X86_BASE_PARSER.coq_parser
  
  val ext_op_modrm2 :
    char list
    ->
    X86_BASE_PARSER.coq_parser
  
  val coq_AAA_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_AAD_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_AAM_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_AAS_p :
    X86_BASE_PARSER.coq_parser
  
  val imm_op :
    bool
    ->
    X86_BASE_PARSER.coq_parser
  
  val logic_or_arith_p :
    bool
    ->
    char list
    ->
    char list
    ->
    (bool
    ->
    operand
    ->
    operand
    ->
    instr)
    ->
    X86_BASE_PARSER.coq_parser
  
  val coq_ADC_p :
    bool
    ->
    X86_BASE_PARSER.coq_parser
  
  val coq_ADD_p :
    bool
    ->
    X86_BASE_PARSER.coq_parser
  
  val coq_AND_p :
    bool
    ->
    X86_BASE_PARSER.coq_parser
  
  val coq_CMP_p :
    bool
    ->
    X86_BASE_PARSER.coq_parser
  
  val coq_OR_p :
    bool
    ->
    X86_BASE_PARSER.coq_parser
  
  val coq_SBB_p :
    bool
    ->
    X86_BASE_PARSER.coq_parser
  
  val coq_SUB_p :
    bool
    ->
    X86_BASE_PARSER.coq_parser
  
  val coq_XOR_p :
    bool
    ->
    X86_BASE_PARSER.coq_parser
  
  val coq_ARPL_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_BOUND_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_BSF_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_BSR_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_BSWAP_p :
    X86_BASE_PARSER.coq_parser
  
  val bit_test_p :
    char list
    ->
    char list
    ->
    (operand
    ->
    operand
    ->
    instr)
    ->
    X86_BASE_PARSER.coq_parser
  
  val coq_BT_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_BTC_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_BTR_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_BTS_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_CALL_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_CDQ_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_CLC_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_CLD_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_CLI_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_CLTS_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_CMC_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_CMPS_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_CMPXCHG_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_CPUID_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_CWDE_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_DAA_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_DAS_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_DEC_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_DIV_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_HLT_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_IDIV_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_IMUL_p :
    bool
    ->
    X86_BASE_PARSER.coq_parser
  
  val coq_IN_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_INC_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_INS_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_INTn_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_INT_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_INTO_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_INVD_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_INVLPG_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_IRET_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_Jcc_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_JCXZ_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_JMP_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LAHF_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LAR_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LDS_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LEA_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LEAVE_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LES_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LFS_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LGDT_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LGS_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LIDT_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LLDT_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LMSW_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LODS_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LOOP_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LOOPZ_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LOOPNZ_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LSL_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LSS_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_LTR_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_CMOVcc_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_MOV_p :
    bool
    ->
    X86_BASE_PARSER.coq_parser
  
  val control_reg_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_MOVCR_p :
    X86_BASE_PARSER.coq_parser
  
  val debug_reg_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_MOVDR_p :
    X86_BASE_PARSER.coq_parser
  
  val segment_reg_p :
    X86_BASE_PARSER.coq_parser
  
  val seg_modrm :
    X86_BASE_PARSER.coq_parser
  
  val coq_MOVSR_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_MOVBE_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_MOVS_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_MOVSX_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_MOVZX_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_MUL_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_NEG_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_NOT_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_OUT_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_OUTS_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_POP_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_POPSR_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_POPA_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_POPF_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_PUSH_p :
    X86_BASE_PARSER.coq_parser
  
  val segment_reg2_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_PUSHSR_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_PUSHA_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_PUSHF_p :
    X86_BASE_PARSER.coq_parser
  
  val rotate_p :
    char list
    ->
    (bool
    ->
    operand
    ->
    reg_or_immed
    ->
    instr)
    ->
    X86_BASE_PARSER.coq_parser
  
  val coq_RCL_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_RCR_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_RDMSR_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_RDPMC_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_RDTSC_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_RDTSCP_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_RET_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_ROL_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_ROR_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_RSM_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_SAHF_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_SAR_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_SCAS_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_SETcc_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_SGDT_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_SHL_p :
    X86_BASE_PARSER.coq_parser
  
  val shiftdouble_p :
    char list
    ->
    (operand
    ->
    register
    ->
    reg_or_immed
    ->
    X86_BASE_PARSER.result_m)
    ->
    X86_BASE_PARSER.coq_parser
  
  val coq_SHLD_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_SHR_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_SHRD_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_SIDT_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_SLDT_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_SMSW_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_STC_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_STD_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_STI_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_STOS_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_STR_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_TEST_p :
    bool
    ->
    X86_BASE_PARSER.coq_parser
  
  val coq_UD2_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_VERR_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_VERW_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_WAIT_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_WBINVD_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_WRMSR_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_XADD_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_XCHG_p :
    X86_BASE_PARSER.coq_parser
  
  val coq_XLAT_p :
    X86_BASE_PARSER.coq_parser
  
  val instr_parsers_opsize_pre :
    X86_BASE_PARSER.coq_parser
    list
  
  val instr_parsers_nosize_pre :
    X86_BASE_PARSER.coq_parser
    list
  
  val list2pair_t :
    X86_BASE_PARSER.result
    list
    ->
    X86_BASE_PARSER.result
  
  val lock_or_rep_p :
    X86_BASE_PARSER.coq_parser
  
  val segment_override_p :
    X86_BASE_PARSER.coq_parser
  
  val op_override_p :
    X86_BASE_PARSER.coq_parser
  
  val addr_override_p :
    X86_BASE_PARSER.coq_parser
  
  val perm2 :
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
  
  val perm3 :
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
  
  val perm4 :
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.result
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
  
  val option_perm2 :
    X86_PARSER_ARG.tipe
    ->
    X86_PARSER_ARG.tipe
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
  
  val option_perm3 :
    X86_PARSER_ARG.tipe
    ->
    X86_PARSER_ARG.tipe
    ->
    X86_PARSER_ARG.tipe
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
  
  val option_perm4 :
    X86_PARSER_ARG.tipe
    ->
    X86_PARSER_ARG.tipe
    ->
    X86_PARSER_ARG.tipe
    ->
    X86_PARSER_ARG.tipe
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
    ->
    X86_BASE_PARSER.coq_parser
  
  val opt2b :
    bool
    option
    ->
    bool
    ->
    bool
  
  val prefix_parser_nooverride :
    X86_BASE_PARSER.coq_parser
  
  val prefix_parser_opsize :
    X86_BASE_PARSER.coq_parser
  
  val instruction_parser_list :
    X86_BASE_PARSER.coq_parser
    list
  
  val instruction_parser :
    X86_BASE_PARSER.coq_parser
  
  val instruction_regexp_pair :
    X86_BASE_PARSER.regexp * X86_BASE_PARSER.ctxt_t
  
  type instParserState = { inst_ctxt : X86_BASE_PARSER.ctxt_t;
                           inst_regexp : X86_BASE_PARSER.regexp }
  
  val instParserState_rect :
    (X86_BASE_PARSER.ctxt_t
    ->
    X86_BASE_PARSER.regexp
    ->
    __
    ->
    'a1)
    ->
    instParserState
    ->
    'a1
  
  val instParserState_rec :
    (X86_BASE_PARSER.ctxt_t
    ->
    X86_BASE_PARSER.regexp
    ->
    __
    ->
    'a1)
    ->
    instParserState
    ->
    'a1
  
  val inst_ctxt :
    instParserState
    ->
    X86_BASE_PARSER.ctxt_t
  
  val inst_regexp :
    instParserState
    ->
    X86_BASE_PARSER.regexp
  
  val initial_parser_state :
    instParserState
  
  val byte_explode :
    int8
    ->
    bool
    list
  
  val parse_byte :
    instParserState
    ->
    int8
    ->
    instParserState * (prefix * instr)
    list
 end

val w32add :
  Word.wint
  ->
  Word.wint
  ->
  Word.wint

val w32sub :
  Word.wint
  ->
  Word.wint
  ->
  Word.wint

val int32_lequ_bool :
  Word.wint
  ->
  Word.wint
  ->
  bool

val checkNoOverflow :
  int32
  ->
  int32
  ->
  bool

val logChunkSize :
  int

val chunkSize :
  z

val lowMemZeroBits :
  int

val lowMemCutoff :
  z

val safeMask :
  Word.wint

val int2bools_aux :
  (z
  ->
  bool)
  ->
  int
  ->
  bool
  list

val int_to_bools :
  int
  ->
  Word.wint
  ->
  bool
  list

val register_to_Z :
  register
  ->
  z

val register_to_bools :
  register
  ->
  bool
  list

val bitslist :
  bool
  list
  ->
  X86_PARSER.X86_BASE_PARSER.coq_parser

val int32_p :
  int32
  ->
  X86_PARSER.X86_BASE_PARSER.coq_parser

val reinsjmp_nonIAT_MASK_p :
  register
  ->
  X86_PARSER.X86_BASE_PARSER.coq_parser

val reinsjmp_nonIAT_MASK_EAX25_p :
  X86_PARSER.X86_BASE_PARSER.coq_parser

val reinsjmp_IAT_or_RET_MASK_p :
  X86_PARSER.X86_BASE_PARSER.coq_parser

val reinsjmp_nonIAT_JMP_p :
  register
  ->
  X86_PARSER.X86_BASE_PARSER.coq_parser

val reinsjmp_nonIAT_CALL_p :
  register
  ->
  X86_PARSER.X86_BASE_PARSER.coq_parser

val reinsjmp_IAT_JMP_p :
  X86_PARSER.X86_BASE_PARSER.coq_parser

val reinsjmp_IAT_CALL_p :
  X86_PARSER.X86_BASE_PARSER.coq_parser

val reinsjmp_nonIAT_p :
  register
  ->
  X86_PARSER.X86_BASE_PARSER.coq_parser

val reinsjmp_nonIAT_EAX25_p :
  X86_PARSER.X86_BASE_PARSER.coq_parser

val reinsjmp_IAT_JMP_or_RET_p :
  X86_PARSER.X86_BASE_PARSER.coq_parser

val reinsjmp_nonIAT_mask :
  X86_PARSER.X86_BASE_PARSER.coq_parser

val reinsjmp_IAT_JMP_or_RET_mask :
  X86_PARSER.X86_BASE_PARSER.coq_parser

type 'x vector =
| Vnil
| Vcons of int
   * 'x
   * 'x
     vector

val vtolist :
  int
  ->
  'a1
  vector
  ->
  'a1
  list

type bYTE
  =
  int8

type wORD
  =
  int16

type dWORD
  =
  int32

type 'x ptr =
  dWORD
  (* singleton inductive, whose constructor was ptr *)

type _IMAGE_DATA_DIRECTORY = { virtualAddress_IDD : dWORD;
                               size : dWORD }

val virtualAddress_IDD :
  _IMAGE_DATA_DIRECTORY
  ->
  dWORD

val size :
  _IMAGE_DATA_DIRECTORY
  ->
  dWORD

type _IMAGE_OPTIONAL_HEADER = { magic : wORD;
                                majorLinkerVersion : bYTE;
                                minorLinkerVersion : bYTE;
                                sizeOfCode : dWORD;
                                sizeOfInitializedData : dWORD;
                                sizeOfUninitializedData : dWORD;
                                addressOfEntryPoint : dWORD;
                                baseOfCode : dWORD;
                                baseOfData : dWORD;
                                imageBase : dWORD;
                                sectionAlignment : dWORD;
                                fileAlignment : dWORD;
                                majorOperatingSystemVersion : wORD;
                                minorOperatingSystemVersion : wORD;
                                majorImageVersion : wORD;
                                minorImageVersion : wORD;
                                majorSubsystemVersion : wORD;
                                minorSubsystemVersion : wORD;
                                win32VersionValue : dWORD;
                                sizeOfImage : dWORD;
                                sizeOfHeaders : dWORD;
                                checkSum : dWORD;
                                subsystem : wORD;
                                dllCharacteristics : wORD;
                                sizeOfStackReserve : dWORD;
                                sizeOfStackCommit : dWORD;
                                sizeOfHeapReserve : dWORD;
                                sizeOfHeapCommit : dWORD;
                                loaderFlags : dWORD;
                                numberOfRvaAndSizes : dWORD;
                                dataDirectory : _IMAGE_DATA_DIRECTORY
                                                vector }

val magic :
  _IMAGE_OPTIONAL_HEADER
  ->
  wORD

val majorLinkerVersion :
  _IMAGE_OPTIONAL_HEADER
  ->
  bYTE

val minorLinkerVersion :
  _IMAGE_OPTIONAL_HEADER
  ->
  bYTE

val sizeOfCode :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val sizeOfInitializedData :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val sizeOfUninitializedData :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val addressOfEntryPoint :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val baseOfCode :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val baseOfData :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val imageBase :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val sectionAlignment :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val fileAlignment :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val majorOperatingSystemVersion :
  _IMAGE_OPTIONAL_HEADER
  ->
  wORD

val minorOperatingSystemVersion :
  _IMAGE_OPTIONAL_HEADER
  ->
  wORD

val majorImageVersion :
  _IMAGE_OPTIONAL_HEADER
  ->
  wORD

val minorImageVersion :
  _IMAGE_OPTIONAL_HEADER
  ->
  wORD

val majorSubsystemVersion :
  _IMAGE_OPTIONAL_HEADER
  ->
  wORD

val minorSubsystemVersion :
  _IMAGE_OPTIONAL_HEADER
  ->
  wORD

val win32VersionValue :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val sizeOfImage :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val sizeOfHeaders :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val checkSum :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val subsystem :
  _IMAGE_OPTIONAL_HEADER
  ->
  wORD

val dllCharacteristics :
  _IMAGE_OPTIONAL_HEADER
  ->
  wORD

val sizeOfStackReserve :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val sizeOfStackCommit :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val sizeOfHeapReserve :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val sizeOfHeapCommit :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val loaderFlags :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val numberOfRvaAndSizes :
  _IMAGE_OPTIONAL_HEADER
  ->
  dWORD

val dataDirectory :
  _IMAGE_OPTIONAL_HEADER
  ->
  _IMAGE_DATA_DIRECTORY
  vector

type _IMAGE_FILE_HEADER = { machine : wORD;
                            numberOfSections : wORD;
                            timeDateStamp_IFH : dWORD;
                            pointerToSymbolTable : dWORD;
                            numberOfSymbols : dWORD;
                            sizeOfOptionalHeader : wORD;
                            characteristics_IFH : wORD }

val machine :
  _IMAGE_FILE_HEADER
  ->
  wORD

val numberOfSections :
  _IMAGE_FILE_HEADER
  ->
  wORD

val timeDateStamp_IFH :
  _IMAGE_FILE_HEADER
  ->
  dWORD

val pointerToSymbolTable :
  _IMAGE_FILE_HEADER
  ->
  dWORD

val numberOfSymbols :
  _IMAGE_FILE_HEADER
  ->
  dWORD

val sizeOfOptionalHeader :
  _IMAGE_FILE_HEADER
  ->
  wORD

val characteristics_IFH :
  _IMAGE_FILE_HEADER
  ->
  wORD

type _IMAGE_NT_HEADER = { signature : dWORD;
                          fileHeader : _IMAGE_FILE_HEADER;
                          optionalHeader : _IMAGE_OPTIONAL_HEADER }

val signature :
  _IMAGE_NT_HEADER
  ->
  dWORD

val fileHeader :
  _IMAGE_NT_HEADER
  ->
  _IMAGE_FILE_HEADER

val optionalHeader :
  _IMAGE_NT_HEADER
  ->
  _IMAGE_OPTIONAL_HEADER

type _IMAGE_DOS_HEADER = { e_magic : wORD;
                           e_cblp : wORD;
                           e_cp : wORD;
                           e_crlc : wORD;
                           e_cparhdr : wORD;
                           e_minalloc : wORD;
                           e_maxalloc : wORD;
                           e_ss : wORD;
                           e_sp : wORD;
                           e_csum : wORD;
                           e_ip : wORD;
                           e_cs : wORD;
                           e_lfarlc : wORD;
                           e_ovno : wORD;
                           e_res : wORD
                                   vector;
                           e_oemid : wORD;
                           e_oeminfo : wORD;
                           e_res2 : wORD
                                    vector;
                           e_lfanew : _IMAGE_NT_HEADER
                                      ptr }

val e_magic :
  _IMAGE_DOS_HEADER
  ->
  wORD

val e_cblp :
  _IMAGE_DOS_HEADER
  ->
  wORD

val e_cp :
  _IMAGE_DOS_HEADER
  ->
  wORD

val e_crlc :
  _IMAGE_DOS_HEADER
  ->
  wORD

val e_cparhdr :
  _IMAGE_DOS_HEADER
  ->
  wORD

val e_minalloc :
  _IMAGE_DOS_HEADER
  ->
  wORD

val e_maxalloc :
  _IMAGE_DOS_HEADER
  ->
  wORD

val e_ss :
  _IMAGE_DOS_HEADER
  ->
  wORD

val e_sp :
  _IMAGE_DOS_HEADER
  ->
  wORD

val e_csum :
  _IMAGE_DOS_HEADER
  ->
  wORD

val e_ip :
  _IMAGE_DOS_HEADER
  ->
  wORD

val e_cs :
  _IMAGE_DOS_HEADER
  ->
  wORD

val e_lfarlc :
  _IMAGE_DOS_HEADER
  ->
  wORD

val e_ovno :
  _IMAGE_DOS_HEADER
  ->
  wORD

val e_res :
  _IMAGE_DOS_HEADER
  ->
  wORD
  vector

val e_oemid :
  _IMAGE_DOS_HEADER
  ->
  wORD

val e_oeminfo :
  _IMAGE_DOS_HEADER
  ->
  wORD

val e_res2 :
  _IMAGE_DOS_HEADER
  ->
  wORD
  vector

val e_lfanew :
  _IMAGE_DOS_HEADER
  ->
  _IMAGE_NT_HEADER
  ptr

val iMAGE_DIRECTORY_ENTRY_IAT :
  int

type _IMAGE_EXPORT_DIRECTORY = { characteristics_IED : dWORD;
                                 timeDateStamp : dWORD;
                                 majorVersion : wORD;
                                 minorVersion : wORD;
                                 name_IED : dWORD;
                                 base : dWORD;
                                 numberOfFunctions : dWORD;
                                 numberOfNames : dWORD;
                                 addressOfFunctions : dWORD;
                                 addressOfNames : dWORD;
                                 addressOfNameOrdinals : dWORD }

val characteristics_IED :
  _IMAGE_EXPORT_DIRECTORY
  ->
  dWORD

val timeDateStamp :
  _IMAGE_EXPORT_DIRECTORY
  ->
  dWORD

val majorVersion :
  _IMAGE_EXPORT_DIRECTORY
  ->
  wORD

val minorVersion :
  _IMAGE_EXPORT_DIRECTORY
  ->
  wORD

val name_IED :
  _IMAGE_EXPORT_DIRECTORY
  ->
  dWORD

val base :
  _IMAGE_EXPORT_DIRECTORY
  ->
  dWORD

val numberOfFunctions :
  _IMAGE_EXPORT_DIRECTORY
  ->
  dWORD

val numberOfNames :
  _IMAGE_EXPORT_DIRECTORY
  ->
  dWORD

val addressOfFunctions :
  _IMAGE_EXPORT_DIRECTORY
  ->
  dWORD

val addressOfNames :
  _IMAGE_EXPORT_DIRECTORY
  ->
  dWORD

val addressOfNameOrdinals :
  _IMAGE_EXPORT_DIRECTORY
  ->
  dWORD

val iMAGE_SIZEOF_SHORT_NAME :
  int

type _IMAGE_SECTION_HEADER = { name_ISH : bYTE
                                          vector;
                               physicalAddressORVirtualSize : dWORD;
                               virtualAddress_ISH : dWORD;
                               sizeOfRawData : dWORD;
                               pointerToRawData : dWORD;
                               pointerToRelocations : dWORD;
                               pointerToLinenumbers : dWORD;
                               numberOfRelocations : wORD;
                               numberOfLinenumbers : wORD;
                               characteristics_ISH : dWORD }

val name_ISH :
  _IMAGE_SECTION_HEADER
  ->
  bYTE
  vector

val physicalAddressORVirtualSize :
  _IMAGE_SECTION_HEADER
  ->
  dWORD

val virtualAddress_ISH :
  _IMAGE_SECTION_HEADER
  ->
  dWORD

val sizeOfRawData :
  _IMAGE_SECTION_HEADER
  ->
  dWORD

val pointerToRawData :
  _IMAGE_SECTION_HEADER
  ->
  dWORD

val pointerToRelocations :
  _IMAGE_SECTION_HEADER
  ->
  dWORD

val pointerToLinenumbers :
  _IMAGE_SECTION_HEADER
  ->
  dWORD

val numberOfRelocations :
  _IMAGE_SECTION_HEADER
  ->
  wORD

val numberOfLinenumbers :
  _IMAGE_SECTION_HEADER
  ->
  wORD

val characteristics_ISH :
  _IMAGE_SECTION_HEADER
  ->
  dWORD

val iMAGE_SCN_CNT_CODE :
  int32

val block_size :
  z

val z_to_nat :
  z
  ->
  int

val word_to_nat :
  wORD
  ->
  int

val dword_to_nat :
  dWORD
  ->
  int

val dword_to_Z :
  dWORD
  ->
  z

val ptr_to_Z :
  'a1
  ptr
  ->
  z

val getChunk :
  int8
  list
  list
  ->
  z
  ->
  int8
  list

val int8_to_int16 :
  int8
  ->
  int16

val bytes_to_word :
  int16
  ->
  int16
  ->
  wORD

val parseByte :
  bYTE
  list
  list
  ->
  z
  ->
  bYTE

val parseWord :
  bYTE
  list
  list
  ->
  z
  ->
  wORD

val int8_to_int32 :
  int8
  ->
  int32

val bytes_to_dword :
  int32
  ->
  int32
  ->
  int32
  ->
  int32
  ->
  dWORD

val parseDoubleWord :
  bYTE
  list
  list
  ->
  z
  ->
  dWORD

val parsePtr :
  bYTE
  list
  list
  ->
  z
  ->
  'a1
  ptr

val parseVector :
  (bYTE
  list
  list
  ->
  z
  ->
  'a1)
  ->
  bYTE
  list
  list
  ->
  z
  ->
  z
  ->
  int
  ->
  'a1
  vector

val copySection :
  bYTE
  list
  list
  ->
  z
  ->
  z
  ->
  int
  ->
  bYTE
  list
  list

val parseImageDosHeader :
  bYTE
  list
  list
  ->
  _IMAGE_DOS_HEADER

val parseImageFileHeader :
  bYTE
  list
  list
  ->
  z
  ->
  _IMAGE_FILE_HEADER

val parseImageDataDirectory :
  bYTE
  list
  list
  ->
  z
  ->
  _IMAGE_DATA_DIRECTORY

val parseImageOptionalHeader :
  bYTE
  list
  list
  ->
  z
  ->
  _IMAGE_OPTIONAL_HEADER

val parseImageNtHeader :
  bYTE
  list
  list
  ->
  z
  ->
  _IMAGE_NT_HEADER

val iSSN :
  z

val parseImageSectionHeader :
  bYTE
  list
  list
  ->
  z
  ->
  _IMAGE_SECTION_HEADER

val parseImageExportDirectory :
  bYTE
  list
  list
  ->
  z
  ->
  _IMAGE_EXPORT_DIRECTORY

val findSection :
  bYTE
  list
  list
  ->
  dWORD
  ->
  z
  ->
  int
  ->
  _IMAGE_SECTION_HEADER
  option

val vAddr_to_offset :
  dWORD
  ->
  _IMAGE_SECTION_HEADER
  ->
  dWORD

val derefImageNtHeader :
  bYTE
  list
  list
  ->
  _IMAGE_NT_HEADER
  ptr
  ->
  _IMAGE_NT_HEADER

val getExports :
  bYTE
  list
  list
  ->
  dWORD
  list

val checkExports :
  bYTE
  list
  list
  ->
  dWORD
  ->
  bool

val derefDataDirectoryIAT :
  _IMAGE_OPTIONAL_HEADER
  ->
  _IMAGE_DATA_DIRECTORY

val derefImageOptionalHeader :
  bYTE
  list
  list
  ->
  _IMAGE_OPTIONAL_HEADER

type iATBounds =
  dWORD * dWORD
  (* singleton inductive, whose constructor was iatbounds *)

val getIATBounds :
  bYTE
  list
  list
  ->
  iATBounds

val getExecutableBounds :
  bYTE
  list
  list
  ->
  z
  ->
  int
  ->
  ((dWORD * dWORD) * bYTE
  list
  list)
  list

val getExecutableSections :
  bYTE
  list
  list
  ->
  ((dWORD * dWORD) * bYTE
  list
  list)
  list

module MakeListOrdering : 
 functor (O:OrderedType) ->
 sig 
  module MO : 
   sig 
    module OrderTac : 
     sig 
      module OTF : 
       sig 
        type t
          =
          O.t
        
        val compare :
          t
          ->
          t
          ->
          comparison
        
        val eq_dec :
          t
          ->
          t
          ->
          bool
       end
      
      module TO : 
       sig 
        type t
          =
          OTF.t
        
        val compare :
          t
          ->
          t
          ->
          comparison
        
        val eq_dec :
          t
          ->
          t
          ->
          bool
       end
     end
    
    val eq_dec :
      O.t
      ->
      O.t
      ->
      bool
    
    val lt_dec :
      O.t
      ->
      O.t
      ->
      bool
    
    val eqb :
      O.t
      ->
      O.t
      ->
      bool
   end
 end

module type Int = 
 sig 
  type int 
  
  val i2z :
    int
    ->
    z
  
  val _0 :
    int
  
  val _1 :
    int
  
  val _2 :
    int
  
  val _3 :
    int
  
  val plus :
    int
    ->
    int
    ->
    int
  
  val opp :
    int
    ->
    int
  
  val minus :
    int
    ->
    int
    ->
    int
  
  val mult :
    int
    ->
    int
    ->
    int
  
  val max :
    int
    ->
    int
    ->
    int
  
  val gt_le_dec :
    int
    ->
    int
    ->
    bool
  
  val ge_lt_dec :
    int
    ->
    int
    ->
    bool
  
  val eq_dec :
    int
    ->
    int
    ->
    bool
 end

module Z_as_Int : 
 sig 
  type int
    =
    z
  
  val _0 :
    z
  
  val _1 :
    z
  
  val _2 :
    z
  
  val _3 :
    z
  
  val plus :
    z
    ->
    z
    ->
    z
  
  val opp :
    z
    ->
    z
  
  val minus :
    z
    ->
    z
    ->
    z
  
  val mult :
    z
    ->
    z
    ->
    z
  
  val max :
    z
    ->
    z
    ->
    z
  
  val gt_le_dec :
    z
    ->
    z
    ->
    bool
  
  val ge_lt_dec :
    z
    ->
    z
    ->
    bool
  
  val eq_dec :
    z
    ->
    z
    ->
    bool
  
  val i2z :
    int
    ->
    z
 end

module MakeRaw : 
 functor (I:Int) ->
 functor (X:OrderedType) ->
 sig 
  type elt
    =
    X.t
  
  type tree =
  | Leaf
  | Node of tree
     * X.t
     * tree
     * I.int
  
  type t
    =
    tree
  
  val height :
    t
    ->
    I.int
  
  val cardinal :
    t
    ->
    int
  
  val empty :
    tree
  
  val is_empty :
    tree
    ->
    bool
  
  val mem :
    X.t
    ->
    tree
    ->
    bool
  
  val singleton :
    X.t
    ->
    tree
  
  val create :
    tree
    ->
    X.t
    ->
    tree
    ->
    tree
  
  val assert_false :
    tree
    ->
    X.t
    ->
    tree
    ->
    tree
  
  val bal :
    t
    ->
    X.t
    ->
    t
    ->
    tree
  
  val add :
    X.t
    ->
    tree
    ->
    tree
  
  val join :
    tree
    ->
    elt
    ->
    t
    ->
    t
  
  val remove_min :
    tree
    ->
    elt
    ->
    t
    ->
    t * elt
  
  val merge :
    tree
    ->
    tree
    ->
    tree
  
  val remove :
    X.t
    ->
    tree
    ->
    tree
  
  val min_elt :
    tree
    ->
    X.t
    option
  
  val max_elt :
    tree
    ->
    X.t
    option
  
  val choose :
    tree
    ->
    X.t
    option
  
  val concat :
    tree
    ->
    tree
    ->
    tree
  
  type triple = { t_left : t;
                  t_in : bool;
                  t_right : t }
  
  val t_left :
    triple
    ->
    t
  
  val t_in :
    triple
    ->
    bool
  
  val t_right :
    triple
    ->
    t
  
  val split :
    X.t
    ->
    tree
    ->
    triple
  
  val inter :
    tree
    ->
    tree
    ->
    tree
  
  val diff :
    tree
    ->
    tree
    ->
    tree
  
  val union :
    tree
    ->
    tree
    ->
    tree
  
  val elements_aux :
    X.t
    list
    ->
    t
    ->
    X.t
    list
  
  val elements :
    t
    ->
    X.t
    list
  
  val filter_acc :
    (elt
    ->
    bool)
    ->
    tree
    ->
    tree
    ->
    tree
  
  val filter :
    (elt
    ->
    bool)
    ->
    tree
    ->
    tree
  
  val partition_acc :
    (elt
    ->
    bool)
    ->
    (t * t)
    ->
    t
    ->
    t * t
  
  val partition :
    (elt
    ->
    bool)
    ->
    t
    ->
    t * t
  
  val for_all :
    (elt
    ->
    bool)
    ->
    tree
    ->
    bool
  
  val exists_ :
    (elt
    ->
    bool)
    ->
    tree
    ->
    bool
  
  val fold :
    (elt
    ->
    'a1
    ->
    'a1)
    ->
    t
    ->
    'a1
    ->
    'a1
  
  val subsetl :
    (t
    ->
    bool)
    ->
    X.t
    ->
    tree
    ->
    bool
  
  val subsetr :
    (t
    ->
    bool)
    ->
    X.t
    ->
    tree
    ->
    bool
  
  val subset :
    tree
    ->
    tree
    ->
    bool
  
  type enumeration =
  | End
  | More of elt
     * t
     * enumeration
  
  val cons :
    tree
    ->
    enumeration
    ->
    enumeration
  
  val compare_more :
    X.t
    ->
    (enumeration
    ->
    comparison)
    ->
    enumeration
    ->
    comparison
  
  val compare_cont :
    tree
    ->
    (enumeration
    ->
    comparison)
    ->
    enumeration
    ->
    comparison
  
  val compare_end :
    enumeration
    ->
    comparison
  
  val compare :
    tree
    ->
    tree
    ->
    comparison
  
  val equal :
    tree
    ->
    tree
    ->
    bool
  
  val ltb_tree :
    X.t
    ->
    tree
    ->
    bool
  
  val gtb_tree :
    X.t
    ->
    tree
    ->
    bool
  
  val isok :
    tree
    ->
    bool
  
  module MX : 
   sig 
    module OrderTac : 
     sig 
      module OTF : 
       sig 
        type t
          =
          X.t
        
        val compare :
          t
          ->
          t
          ->
          comparison
        
        val eq_dec :
          t
          ->
          t
          ->
          bool
       end
      
      module TO : 
       sig 
        type t = OTF.t
        
        val compare : t -> t -> comparison
        
        val eq_dec : t -> t -> bool
       end
     end
    
    val eq_dec : X.t -> X.t -> bool
    
    val lt_dec : X.t -> X.t -> bool
    
    val eqb : X.t -> X.t -> bool
   end
  
  type coq_R_bal =
  | R_bal_0 of t * X.t * t
  | R_bal_1 of t * X.t * t * tree * X.t * tree * I.int
  | R_bal_2 of t * X.t * t * tree * X.t * tree * I.int
  | R_bal_3 of t * X.t * t * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int
  | R_bal_4 of t * X.t * t
  | R_bal_5 of t * X.t * t * tree * X.t * tree * I.int
  | R_bal_6 of t * X.t * t * tree * X.t * tree * I.int
  | R_bal_7 of t * X.t * t * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int
  | R_bal_8 of t * X.t * t
  
  type coq_R_remove_min =
  | R_remove_min_0 of tree * elt * t
  | R_remove_min_1 of tree * elt * t * tree * X.t * tree * I.int * (t * elt)
     * coq_R_remove_min * t * elt
  
  type coq_R_merge =
  | R_merge_0 of tree * tree
  | R_merge_1 of tree * tree * tree * X.t * tree * I.int
  | R_merge_2 of tree * tree * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int * t * elt
  
  type coq_R_min_elt =
  | R_min_elt_0 of tree
  | R_min_elt_1 of tree * tree * X.t * tree * I.int
  | R_min_elt_2 of tree * tree * X.t * tree * I.int * tree * X.t * tree
     * I.int * X.t option * coq_R_min_elt
  
  type coq_R_max_elt =
  | R_max_elt_0 of tree
  | R_max_elt_1 of tree * tree * X.t * tree * I.int
  | R_max_elt_2 of tree * tree * X.t * tree * I.int * tree * X.t * tree
     * I.int * X.t option * coq_R_max_elt
  
  type coq_R_concat =
  | R_concat_0 of tree * tree
  | R_concat_1 of tree * tree * tree * X.t * tree * I.int
  | R_concat_2 of tree * tree * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int * t * elt
  
  type coq_R_inter =
  | R_inter_0 of tree * tree
  | R_inter_1 of tree * tree * tree * X.t * tree * I.int
  | R_inter_2 of tree * tree * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int * t * bool * t * tree * coq_R_inter * tree * coq_R_inter
  | R_inter_3 of tree * tree * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int * t * bool * t * tree * coq_R_inter * tree * coq_R_inter
  
  type coq_R_diff =
  | R_diff_0 of tree * tree
  | R_diff_1 of tree * tree * tree * X.t * tree * I.int
  | R_diff_2 of tree * tree * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int * t * bool * t * tree * coq_R_diff * tree * coq_R_diff
  | R_diff_3 of tree * tree * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int * t * bool * t * tree * coq_R_diff * tree * coq_R_diff
  
  type coq_R_union =
  | R_union_0 of tree * tree
  | R_union_1 of tree * tree * tree * X.t * tree * I.int
  | R_union_2 of tree * tree * tree * X.t * tree * I.int * tree * X.t * 
     tree * I.int * t * bool * t * tree * coq_R_union * tree * coq_R_union
  
  module L : 
   sig 
    module MO : 
     sig 
      module OrderTac : 
       sig 
        module OTF : 
         sig 
          type t = X.t
          
          val compare : t -> t -> comparison
          
          val eq_dec : t -> t -> bool
         end
        
        module TO : 
         sig 
          type t = OTF.t
          
          val compare : t -> t -> comparison
          
          val eq_dec : t -> t -> bool
         end
       end
      
      val eq_dec : X.t -> X.t -> bool
      
      val lt_dec : X.t -> X.t -> bool
      
      val eqb : X.t -> X.t -> bool
     end
   end
  
  val flatten_e : enumeration -> elt list
 end

module IntMake : 
 functor (I:Int) ->
 functor (X:OrderedType) ->
 sig 
  module Raw : 
   sig 
    type elt = X.t
    
    type tree =
    | Leaf
    | Node of tree * X.t * tree * I.int
    
    type t = tree
    
    val height : t -> I.int
    
    val cardinal : t -> int
    
    val empty : tree
    
    val is_empty : tree -> bool
    
    val mem : X.t -> tree -> bool
    
    val singleton : X.t -> tree
    
    val create : tree -> X.t -> tree -> tree
    
    val assert_false : tree -> X.t -> tree -> tree
    
    val bal : t -> X.t -> t -> tree
    
    val add : X.t -> tree -> tree
    
    val join : tree -> elt -> t -> t
    
    val remove_min : tree -> elt -> t -> t * elt
    
    val merge : tree -> tree -> tree
    
    val remove : X.t -> tree -> tree
    
    val min_elt : tree -> X.t option
    
    val max_elt : tree -> X.t option
    
    val choose : tree -> X.t option
    
    val concat : tree -> tree -> tree
    
    type triple = { t_left : t; t_in : bool; t_right : t }
    
    val t_left : triple -> t
    
    val t_in : triple -> bool
    
    val t_right : triple -> t
    
    val split : X.t -> tree -> triple
    
    val inter : tree -> tree -> tree
    
    val diff : tree -> tree -> tree
    
    val union : tree -> tree -> tree
    
    val elements_aux : X.t list -> t -> X.t list
    
    val elements : t -> X.t list
    
    val filter_acc : (elt -> bool) -> tree -> tree -> tree
    
    val filter : (elt -> bool) -> tree -> tree
    
    val partition_acc : (elt -> bool) -> (t * t) -> t -> t * t
    
    val partition : (elt -> bool) -> t -> t * t
    
    val for_all : (elt -> bool) -> tree -> bool
    
    val exists_ : (elt -> bool) -> tree -> bool
    
    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
    
    val subsetl : (t -> bool) -> X.t -> tree -> bool
    
    val subsetr : (t -> bool) -> X.t -> tree -> bool
    
    val subset : tree -> tree -> bool
    
    type enumeration =
    | End
    | More of elt * t * enumeration
    
    val cons : tree -> enumeration -> enumeration
    
    val compare_more :
      X.t -> (enumeration -> comparison) -> enumeration -> comparison
    
    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison
    
    val compare_end : enumeration -> comparison
    
    val compare : tree -> tree -> comparison
    
    val equal : tree -> tree -> bool
    
    val ltb_tree : X.t -> tree -> bool
    
    val gtb_tree : X.t -> tree -> bool
    
    val isok : tree -> bool
    
    module MX : 
     sig 
      module OrderTac : 
       sig 
        module OTF : 
         sig 
          type t = X.t
          
          val compare : t -> t -> comparison
          
          val eq_dec : t -> t -> bool
         end
        
        module TO : 
         sig 
          type t = OTF.t
          
          val compare : t -> t -> comparison
          
          val eq_dec : t -> t -> bool
         end
       end
      
      val eq_dec : X.t -> X.t -> bool
      
      val lt_dec : X.t -> X.t -> bool
      
      val eqb : X.t -> X.t -> bool
     end
    
    type coq_R_bal =
    | R_bal_0 of t * X.t * t
    | R_bal_1 of t * X.t * t * tree * X.t * tree * I.int
    | R_bal_2 of t * X.t * t * tree * X.t * tree * I.int
    | R_bal_3 of t * X.t * t * tree * X.t * tree * I.int * tree * X.t * 
       tree * I.int
    | R_bal_4 of t * X.t * t
    | R_bal_5 of t * X.t * t * tree * X.t * tree * I.int
    | R_bal_6 of t * X.t * t * tree * X.t * tree * I.int
    | R_bal_7 of t * X.t * t * tree * X.t * tree * I.int * tree * X.t * 
       tree * I.int
    | R_bal_8 of t * X.t * t
    
    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * tree * X.t * tree * I.int
       * (t * elt) * coq_R_remove_min * t * elt
    
    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * tree * X.t * tree * I.int
    | R_merge_2 of tree * tree * tree * X.t * tree * I.int * tree * X.t
       * tree * I.int * t * elt
    
    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * tree * X.t * tree * I.int
    | R_min_elt_2 of tree * tree * X.t * tree * I.int * tree * X.t * 
       tree * I.int * X.t option * coq_R_min_elt
    
    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * tree * X.t * tree * I.int
    | R_max_elt_2 of tree * tree * X.t * tree * I.int * tree * X.t * 
       tree * I.int * X.t option * coq_R_max_elt
    
    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * tree * X.t * tree * I.int
    | R_concat_2 of tree * tree * tree * X.t * tree * I.int * tree * 
       X.t * tree * I.int * t * elt
    
    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * tree * X.t * tree * I.int
    | R_inter_2 of tree * tree * tree * X.t * tree * I.int * tree * X.t
       * tree * I.int * t * bool * t * tree * coq_R_inter * tree
       * coq_R_inter
    | R_inter_3 of tree * tree * tree * X.t * tree * I.int * tree * X.t
       * tree * I.int * t * bool * t * tree * coq_R_inter * tree
       * coq_R_inter
    
    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * tree * X.t * tree * I.int
    | R_diff_2 of tree * tree * tree * X.t * tree * I.int * tree * X.t * 
       tree * I.int * t * bool * t * tree * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * tree * X.t * tree * I.int * tree * X.t * 
       tree * I.int * t * bool * t * tree * coq_R_diff * tree * coq_R_diff
    
    type coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * tree * X.t * tree * I.int
    | R_union_2 of tree * tree * tree * X.t * tree * I.int * tree * X.t
       * tree * I.int * t * bool * t * tree * coq_R_union * tree
       * coq_R_union
    
    module L : 
     sig 
      module MO : 
       sig 
        module OrderTac : 
         sig 
          module OTF : 
           sig 
            type t = X.t
            
            val compare : t -> t -> comparison
            
            val eq_dec : t -> t -> bool
           end
          
          module TO : 
           sig 
            type t = OTF.t
            
            val compare : t -> t -> comparison
            
            val eq_dec : t -> t -> bool
           end
         end
        
        val eq_dec : X.t -> X.t -> bool
        
        val lt_dec : X.t -> X.t -> bool
        
        val eqb : X.t -> X.t -> bool
       end
     end
    
    val flatten_e : enumeration -> elt list
   end
  
  module E : 
   sig 
    type t = X.t
    
    val compare : t -> t -> comparison
    
    val eq_dec : t -> t -> bool
   end
  
  type elt = X.t
  
  type t_ =
    Raw.t
    (* singleton inductive, whose constructor was Mkt *)
  
  val this : t_ -> Raw.t
  
  type t = t_
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val remove : elt -> t -> t
  
  val singleton : elt -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val empty : t
  
  val is_empty : t -> bool
  
  val elements : t -> elt list
  
  val choose : t -> elt option
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val cardinal : t -> int
  
  val filter : (elt -> bool) -> t -> t
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val partition : (elt -> bool) -> t -> t * t
  
  val eq_dec : t -> t -> bool
  
  val compare : t -> t -> comparison
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
 end

module Make : 
 functor (X:OrderedType) ->
 sig 
  module Raw : 
   sig 
    type elt = X.t
    
    type tree =
    | Leaf
    | Node of tree * X.t * tree * Z_as_Int.int
    
    type t = tree
    
    val height : t -> Z_as_Int.int
    
    val cardinal : t -> int
    
    val empty : tree
    
    val is_empty : tree -> bool
    
    val mem : X.t -> tree -> bool
    
    val singleton : X.t -> tree
    
    val create : tree -> X.t -> tree -> tree
    
    val assert_false : tree -> X.t -> tree -> tree
    
    val bal : t -> X.t -> t -> tree
    
    val add : X.t -> tree -> tree
    
    val join : tree -> elt -> t -> t
    
    val remove_min : tree -> elt -> t -> t * elt
    
    val merge : tree -> tree -> tree
    
    val remove : X.t -> tree -> tree
    
    val min_elt : tree -> X.t option
    
    val max_elt : tree -> X.t option
    
    val choose : tree -> X.t option
    
    val concat : tree -> tree -> tree
    
    type triple = { t_left : t; t_in : bool; t_right : t }
    
    val t_left : triple -> t
    
    val t_in : triple -> bool
    
    val t_right : triple -> t
    
    val split : X.t -> tree -> triple
    
    val inter : tree -> tree -> tree
    
    val diff : tree -> tree -> tree
    
    val union : tree -> tree -> tree
    
    val elements_aux : X.t list -> t -> X.t list
    
    val elements : t -> X.t list
    
    val filter_acc : (elt -> bool) -> tree -> tree -> tree
    
    val filter : (elt -> bool) -> tree -> tree
    
    val partition_acc : (elt -> bool) -> (t * t) -> t -> t * t
    
    val partition : (elt -> bool) -> t -> t * t
    
    val for_all : (elt -> bool) -> tree -> bool
    
    val exists_ : (elt -> bool) -> tree -> bool
    
    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
    
    val subsetl : (t -> bool) -> X.t -> tree -> bool
    
    val subsetr : (t -> bool) -> X.t -> tree -> bool
    
    val subset : tree -> tree -> bool
    
    type enumeration =
    | End
    | More of elt * t * enumeration
    
    val cons : tree -> enumeration -> enumeration
    
    val compare_more :
      X.t -> (enumeration -> comparison) -> enumeration -> comparison
    
    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison
    
    val compare_end : enumeration -> comparison
    
    val compare : tree -> tree -> comparison
    
    val equal : tree -> tree -> bool
    
    val ltb_tree : X.t -> tree -> bool
    
    val gtb_tree : X.t -> tree -> bool
    
    val isok : tree -> bool
    
    module MX : 
     sig 
      module OrderTac : 
       sig 
        module OTF : 
         sig 
          type t = X.t
          
          val compare : t -> t -> comparison
          
          val eq_dec : t -> t -> bool
         end
        
        module TO : 
         sig 
          type t = OTF.t
          
          val compare : t -> t -> comparison
          
          val eq_dec : t -> t -> bool
         end
       end
      
      val eq_dec : X.t -> X.t -> bool
      
      val lt_dec : X.t -> X.t -> bool
      
      val eqb : X.t -> X.t -> bool
     end
    
    type coq_R_bal =
    | R_bal_0 of t * X.t * t
    | R_bal_1 of t * X.t * t * tree * X.t * tree * Z_as_Int.int
    | R_bal_2 of t * X.t * t * tree * X.t * tree * Z_as_Int.int
    | R_bal_3 of t * X.t * t * tree * X.t * tree * Z_as_Int.int * tree * 
       X.t * tree * Z_as_Int.int
    | R_bal_4 of t * X.t * t
    | R_bal_5 of t * X.t * t * tree * X.t * tree * Z_as_Int.int
    | R_bal_6 of t * X.t * t * tree * X.t * tree * Z_as_Int.int
    | R_bal_7 of t * X.t * t * tree * X.t * tree * Z_as_Int.int * tree * 
       X.t * tree * Z_as_Int.int
    | R_bal_8 of t * X.t * t
    
    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * tree * X.t * tree * Z_as_Int.int
       * (t * elt) * coq_R_remove_min * t * elt
    
    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * tree * X.t * tree * Z_as_Int.int
    | R_merge_2 of tree * tree * tree * X.t * tree * Z_as_Int.int * tree
       * X.t * tree * Z_as_Int.int * t * elt
    
    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * tree * X.t * tree * Z_as_Int.int
    | R_min_elt_2 of tree * tree * X.t * tree * Z_as_Int.int * tree * 
       X.t * tree * Z_as_Int.int * X.t option * coq_R_min_elt
    
    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * tree * X.t * tree * Z_as_Int.int
    | R_max_elt_2 of tree * tree * X.t * tree * Z_as_Int.int * tree * 
       X.t * tree * Z_as_Int.int * X.t option * coq_R_max_elt
    
    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * tree * X.t * tree * Z_as_Int.int
    | R_concat_2 of tree * tree * tree * X.t * tree * Z_as_Int.int * 
       tree * X.t * tree * Z_as_Int.int * t * elt
    
    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * tree * X.t * tree * Z_as_Int.int
    | R_inter_2 of tree * tree * tree * X.t * tree * Z_as_Int.int * tree
       * X.t * tree * Z_as_Int.int * t * bool * t * tree * coq_R_inter * 
       tree * coq_R_inter
    | R_inter_3 of tree * tree * tree * X.t * tree * Z_as_Int.int * tree
       * X.t * tree * Z_as_Int.int * t * bool * t * tree * coq_R_inter * 
       tree * coq_R_inter
    
    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * tree * X.t * tree * Z_as_Int.int
    | R_diff_2 of tree * tree * tree * X.t * tree * Z_as_Int.int * tree * 
       X.t * tree * Z_as_Int.int * t * bool * t * tree * coq_R_diff * 
       tree * coq_R_diff
    | R_diff_3 of tree * tree * tree * X.t * tree * Z_as_Int.int * tree * 
       X.t * tree * Z_as_Int.int * t * bool * t * tree * coq_R_diff * 
       tree * coq_R_diff
    
    type coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * tree * X.t * tree * Z_as_Int.int
    | R_union_2 of tree * tree * tree * X.t * tree * Z_as_Int.int * tree
       * X.t * tree * Z_as_Int.int * t * bool * t * tree * coq_R_union * 
       tree * coq_R_union
    
    module L : 
     sig 
      module MO : 
       sig 
        module OrderTac : 
         sig 
          module OTF : 
           sig 
            type t = X.t
            
            val compare : t -> t -> comparison
            
            val eq_dec : t -> t -> bool
           end
          
          module TO : 
           sig 
            type t = OTF.t
            
            val compare : t -> t -> comparison
            
            val eq_dec : t -> t -> bool
           end
         end
        
        val eq_dec : X.t -> X.t -> bool
        
        val lt_dec : X.t -> X.t -> bool
        
        val eqb : X.t -> X.t -> bool
       end
     end
    
    val flatten_e : enumeration -> elt list
   end
  
  module E : 
   sig 
    type t = X.t
    
    val compare : t -> t -> comparison
    
    val eq_dec : t -> t -> bool
   end
  
  type elt = X.t
  
  type t_ =
    Raw.t
    (* singleton inductive, whose constructor was Mkt *)
  
  val this : t_ -> Raw.t
  
  type t = t_
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val remove : elt -> t -> t
  
  val singleton : elt -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val empty : t
  
  val is_empty : t -> bool
  
  val elements : t -> elt list
  
  val choose : t -> elt option
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val cardinal : t -> int
  
  val filter : (elt -> bool) -> t -> t
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val partition : (elt -> bool) -> t -> t * t
  
  val eq_dec : t -> t -> bool
  
  val compare : t -> t -> comparison
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
 end

module type OrderedTypeOrig = 
 Coq_OrderedType

module Update_OT : 
 functor (O:OrderedTypeOrig) ->
 sig 
  type t = O.t
  
  val eq_dec : t -> t -> bool
  
  val compare : O.t -> O.t -> comparison
 end

val reinsjmp_nonIAT_dfa : X86_PARSER.X86_BASE_PARSER.coq_DFA

val reinsjmp_IAT_JMP_or_RET_dfa : X86_PARSER.X86_BASE_PARSER.coq_DFA

val reinsjmp_IAT_CALL_dfa : X86_PARSER.X86_BASE_PARSER.coq_DFA

val dir_cflow_dfa : X86_PARSER.X86_BASE_PARSER.coq_DFA

val non_cflow_dfa : X86_PARSER.X86_BASE_PARSER.coq_DFA

module New_Int32_OT : 
 sig 
  type t = Word.wint
  
  val eq_dec : Word.wint -> Word.wint -> bool
  
  val compare : Word.wint -> Word.wint -> comparison
 end

module Int32Set : 
 sig 
  module Raw : 
   sig 
    type elt = Word.wint
    
    type tree =
    | Leaf
    | Node of tree * Word.wint * tree * Z_as_Int.int
    
    type t = tree
    
    val height : t -> Z_as_Int.int
    
    val cardinal : t -> int
    
    val empty : tree
    
    val is_empty : tree -> bool
    
    val mem : Word.wint -> tree -> bool
    
    val singleton : Word.wint -> tree
    
    val create : tree -> Word.wint -> tree -> tree
    
    val assert_false : tree -> Word.wint -> tree -> tree
    
    val bal : t -> Word.wint -> t -> tree
    
    val add : Word.wint -> tree -> tree
    
    val join : tree -> elt -> t -> t
    
    val remove_min : tree -> elt -> t -> t * elt
    
    val merge : tree -> tree -> tree
    
    val remove : Word.wint -> tree -> tree
    
    val min_elt : tree -> Word.wint option
    
    val max_elt : tree -> Word.wint option
    
    val choose : tree -> Word.wint option
    
    val concat : tree -> tree -> tree
    
    type triple = { t_left : t; t_in : bool; t_right : t }
    
    val t_left : triple -> t
    
    val t_in : triple -> bool
    
    val t_right : triple -> t
    
    val split : Word.wint -> tree -> triple
    
    val inter : tree -> tree -> tree
    
    val diff : tree -> tree -> tree
    
    val union : tree -> tree -> tree
    
    val elements_aux : Word.wint list -> t -> Word.wint list
    
    val elements : t -> Word.wint list
    
    val filter_acc : (elt -> bool) -> tree -> tree -> tree
    
    val filter : (elt -> bool) -> tree -> tree
    
    val partition_acc : (elt -> bool) -> (t * t) -> t -> t * t
    
    val partition : (elt -> bool) -> t -> t * t
    
    val for_all : (elt -> bool) -> tree -> bool
    
    val exists_ : (elt -> bool) -> tree -> bool
    
    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
    
    val subsetl : (t -> bool) -> Word.wint -> tree -> bool
    
    val subsetr : (t -> bool) -> Word.wint -> tree -> bool
    
    val subset : tree -> tree -> bool
    
    type enumeration =
    | End
    | More of elt * t * enumeration
    
    val cons : tree -> enumeration -> enumeration
    
    val compare_more :
      Word.wint -> (enumeration -> comparison) -> enumeration -> comparison
    
    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison
    
    val compare_end : enumeration -> comparison
    
    val compare : tree -> tree -> comparison
    
    val equal : tree -> tree -> bool
    
    val ltb_tree : Word.wint -> tree -> bool
    
    val gtb_tree : Word.wint -> tree -> bool
    
    val isok : tree -> bool
    
    module MX : 
     sig 
      module OrderTac : 
       sig 
        module OTF : 
         sig 
          type t = Word.wint
          
          val compare : Word.wint -> Word.wint -> comparison
          
          val eq_dec : Word.wint -> Word.wint -> bool
         end
        
        module TO : 
         sig 
          type t = Word.wint
          
          val compare : Word.wint -> Word.wint -> comparison
          
          val eq_dec : Word.wint -> Word.wint -> bool
         end
       end
      
      val eq_dec : Word.wint -> Word.wint -> bool
      
      val lt_dec : Word.wint -> Word.wint -> bool
      
      val eqb : Word.wint -> Word.wint -> bool
     end
    
    type coq_R_bal =
    | R_bal_0 of t * Word.wint * t
    | R_bal_1 of t * Word.wint * t * tree * Word.wint * tree * Z_as_Int.int
    | R_bal_2 of t * Word.wint * t * tree * Word.wint * tree * Z_as_Int.int
    | R_bal_3 of t * Word.wint * t * tree * Word.wint * tree * Z_as_Int.int
       * tree * Word.wint * tree * Z_as_Int.int
    | R_bal_4 of t * Word.wint * t
    | R_bal_5 of t * Word.wint * t * tree * Word.wint * tree * Z_as_Int.int
    | R_bal_6 of t * Word.wint * t * tree * Word.wint * tree * Z_as_Int.int
    | R_bal_7 of t * Word.wint * t * tree * Word.wint * tree * Z_as_Int.int
       * tree * Word.wint * tree * Z_as_Int.int
    | R_bal_8 of t * Word.wint * t
    
    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * tree * Word.wint * tree
       * Z_as_Int.int * (t * elt) * coq_R_remove_min * t * elt
    
    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * tree * Word.wint * tree * Z_as_Int.int
    | R_merge_2 of tree * tree * tree * Word.wint * tree * Z_as_Int.int
       * tree * Word.wint * tree * Z_as_Int.int * t * elt
    
    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * tree * Word.wint * tree * Z_as_Int.int
    | R_min_elt_2 of tree * tree * Word.wint * tree * Z_as_Int.int * 
       tree * Word.wint * tree * Z_as_Int.int * Word.wint option
       * coq_R_min_elt
    
    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * tree * Word.wint * tree * Z_as_Int.int
    | R_max_elt_2 of tree * tree * Word.wint * tree * Z_as_Int.int * 
       tree * Word.wint * tree * Z_as_Int.int * Word.wint option
       * coq_R_max_elt
    
    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * tree * Word.wint * tree * Z_as_Int.int
    | R_concat_2 of tree * tree * tree * Word.wint * tree * Z_as_Int.int
       * tree * Word.wint * tree * Z_as_Int.int * t * elt
    
    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * tree * Word.wint * tree * Z_as_Int.int
    | R_inter_2 of tree * tree * tree * Word.wint * tree * Z_as_Int.int
       * tree * Word.wint * tree * Z_as_Int.int * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * tree * Word.wint * tree * Z_as_Int.int
       * tree * Word.wint * tree * Z_as_Int.int * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter
    
    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * tree * Word.wint * tree * Z_as_Int.int
    | R_diff_2 of tree * tree * tree * Word.wint * tree * Z_as_Int.int * 
       tree * Word.wint * tree * Z_as_Int.int * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * tree * Word.wint * tree * Z_as_Int.int * 
       tree * Word.wint * tree * Z_as_Int.int * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff
    
    type coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * tree * Word.wint * tree * Z_as_Int.int
    | R_union_2 of tree * tree * tree * Word.wint * tree * Z_as_Int.int
       * tree * Word.wint * tree * Z_as_Int.int * t * bool * t * tree
       * coq_R_union * tree * coq_R_union
    
    module L : 
     sig 
      module MO : 
       sig 
        module OrderTac : 
         sig 
          module OTF : 
           sig 
            type t = Word.wint
            
            val compare : Word.wint -> Word.wint -> comparison
            
            val eq_dec : Word.wint -> Word.wint -> bool
           end
          
          module TO : 
           sig 
            type t = Word.wint
            
            val compare : Word.wint -> Word.wint -> comparison
            
            val eq_dec : Word.wint -> Word.wint -> bool
           end
         end
        
        val eq_dec : Word.wint -> Word.wint -> bool
        
        val lt_dec : Word.wint -> Word.wint -> bool
        
        val eqb : Word.wint -> Word.wint -> bool
       end
     end
    
    val flatten_e : enumeration -> elt list
   end
  
  module E : 
   sig 
    type t = Word.wint
    
    val compare : Word.wint -> Word.wint -> comparison
    
    val eq_dec : Word.wint -> Word.wint -> bool
   end
  
  type elt = Word.wint
  
  type t_ =
    Raw.t
    (* singleton inductive, whose constructor was Mkt *)
  
  val this : t_ -> Raw.t
  
  type t = t_
  
  val mem : elt -> t -> bool
  
  val add : elt -> t -> t
  
  val remove : elt -> t -> t
  
  val singleton : elt -> t
  
  val union : t -> t -> t
  
  val inter : t -> t -> t
  
  val diff : t -> t -> t
  
  val equal : t -> t -> bool
  
  val subset : t -> t -> bool
  
  val empty : t
  
  val is_empty : t -> bool
  
  val elements : t -> elt list
  
  val choose : t -> elt option
  
  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
  
  val cardinal : t -> int
  
  val filter : (elt -> bool) -> t -> t
  
  val for_all : (elt -> bool) -> t -> bool
  
  val exists_ : (elt -> bool) -> t -> bool
  
  val partition : (elt -> bool) -> t -> t * t
  
  val eq_dec : t -> t -> bool
  
  val compare : t -> t -> comparison
  
  val min_elt : t -> elt option
  
  val max_elt : t -> elt option
 end

val byte2token : int8 -> X86_PARSER.X86_BASE_PARSER.token_id

val token2byte : X86_PARSER.X86_BASE_PARSER.token_id -> int8

val parseloop :
  X86_PARSER.instParserState -> int8 list -> ((prefix * instr) * int8 list)
  option

type jumptype =
| JMP_t
| JCC_t
| CALL_t

val extract_disp_and_type : int8 list -> (int32 * jumptype) option

type instParserState' = { inst_ctxt' : X86_PARSER.X86_BASE_PARSER.ctxt_t;
                          inst_regexp' : X86_PARSER.X86_BASE_PARSER.regexp }

val inst_ctxt' : instParserState' -> X86_PARSER.X86_BASE_PARSER.ctxt_t

val inst_regexp' : instParserState' -> X86_PARSER.X86_BASE_PARSER.regexp

val parse_byte' :
  instParserState' -> int8 -> instParserState' * (instr * instr) list

val parseloop' :
  instParserState' -> int8 list -> ((instr * instr) * int8 list) option

val extract_IAT_jmp_dest :
  X86_PARSER.X86_BASE_PARSER.coq_parser -> int8 list -> address option option

type instParserState'' = { inst_ctxt'' : X86_PARSER.X86_BASE_PARSER.ctxt_t;
                           inst_regexp'' : X86_PARSER.X86_BASE_PARSER.regexp }

val inst_ctxt'' : instParserState'' -> X86_PARSER.X86_BASE_PARSER.ctxt_t

val inst_regexp'' : instParserState'' -> X86_PARSER.X86_BASE_PARSER.regexp

val parse_byte'' :
  instParserState'' -> int8 -> instParserState'' * instr list

val parseloop'' :
  instParserState'' -> int8 list -> (instr * int8 list) option

val extract_IAT_call_dest :
  X86_PARSER.X86_BASE_PARSER.coq_parser -> int8 list -> address option

val is_nonIAT_call :
  X86_PARSER.X86_BASE_PARSER.coq_parser -> int8 list -> bool

val process_buffer_aux :
  X86_PARSER.X86_BASE_PARSER.coq_DFA -> X86_PARSER.X86_BASE_PARSER.coq_DFA ->
  X86_PARSER.X86_BASE_PARSER.coq_DFA -> X86_PARSER.X86_BASE_PARSER.coq_DFA ->
  X86_PARSER.X86_BASE_PARSER.coq_DFA -> X86_PARSER.X86_BASE_PARSER.coq_parser
  -> X86_PARSER.X86_BASE_PARSER.coq_parser ->
  X86_PARSER.X86_BASE_PARSER.coq_parser -> int32 -> int ->
  X86_PARSER.X86_BASE_PARSER.token_id list list ->
  (((Int32Set.t * Int32Set.t) * Int32Set.t) * Int32Set.t) ->
  (((Int32Set.t * Int32Set.t) * Int32Set.t) * Int32Set.t) option

val process_buffer :
  X86_PARSER.X86_BASE_PARSER.coq_DFA -> X86_PARSER.X86_BASE_PARSER.coq_DFA ->
  X86_PARSER.X86_BASE_PARSER.coq_DFA -> X86_PARSER.X86_BASE_PARSER.coq_DFA ->
  X86_PARSER.X86_BASE_PARSER.coq_DFA -> X86_PARSER.X86_BASE_PARSER.coq_parser
  -> X86_PARSER.X86_BASE_PARSER.coq_parser ->
  X86_PARSER.X86_BASE_PARSER.coq_parser -> int8 list list ->
  (((Int32Set.t * Int32Set.t) * Int32Set.t) * Int32Set.t) option

val aligned_bool : int32 -> bool

val checkAligned_aux_terminate : ((Int32Set.t * z) * int) -> bool

val checkAligned_aux : ((Int32Set.t * z) * int) -> bool

val checkAligned : Int32Set.t -> int -> bool

val checkJmpTargets : Int32Set.t -> bool

val checkIATAddresses :
  iATBounds
  ->
  Int32Set.t
  ->
  bool

val checkCallAlignment :
  Int32Set.t
  ->
  bool

val checkExecSectionLowMemory :
  int32
  ->
  int32
  ->
  bool

val checkExecSection :
  X86_PARSER.X86_BASE_PARSER.coq_DFA
  ->
  X86_PARSER.X86_BASE_PARSER.coq_DFA
  ->
  X86_PARSER.X86_BASE_PARSER.coq_DFA
  ->
  X86_PARSER.X86_BASE_PARSER.coq_DFA
  ->
  X86_PARSER.X86_BASE_PARSER.coq_DFA
  ->
  X86_PARSER.X86_BASE_PARSER.coq_parser
  ->
  X86_PARSER.X86_BASE_PARSER.coq_parser
  ->
  X86_PARSER.X86_BASE_PARSER.coq_parser
  ->
  iATBounds
  ->
  ((int32 * int32) * int8
  list
  list)
  ->
  bool * Int32Set.t

val checkProgram :
  X86_PARSER.X86_BASE_PARSER.coq_DFA
  ->
  X86_PARSER.X86_BASE_PARSER.coq_DFA
  ->
  X86_PARSER.X86_BASE_PARSER.coq_DFA
  ->
  X86_PARSER.X86_BASE_PARSER.coq_DFA
  ->
  X86_PARSER.X86_BASE_PARSER.coq_DFA
  ->
  X86_PARSER.X86_BASE_PARSER.coq_parser
  ->
  X86_PARSER.X86_BASE_PARSER.coq_parser
  ->
  X86_PARSER.X86_BASE_PARSER.coq_parser
  ->
  int8
  list
  list
  ->
  bool * Int32Set.t

val checkProgram' :
  int8
  list
  list
  ->
  bool * Int32Set.t

