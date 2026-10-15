import SpecTecDecl0132

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «sub:value:defaultValue» : value → Bool
  | .DEFAULT => true
  | _ => false


def «sub:value:enumValue» : value → Bool
  | .«% '.' %» _ _ => true
  | .«% '.' % '.' %» _ _ _ => true
  | _ => false


def «sub:value:errorValue» : value → Bool
  | .«ERROR '.' %» _ => true
  | _ => false


def «sub:value:headerStackValue» : value → Bool
  | .«HEADER_STACK `[ % `( % `) `]» _ _ => true
  | _ => false


def «sub:value:headerUnionValue» : value → Bool
  | .«HEADER_UNION % `{ % `}» _ _ => true
  | _ => false


def «sub:value:headerValue» : value → Bool
  | .«HEADER % `{ % ';' % `}» _ _ _ => true
  | _ => false


def «sub:value:integerLiteral» : value → Bool
  | .D _ => true
  | .«% W %» _ _ => true
  | .«% S %» _ _ => true
  | _ => false


def «sub:value:integerValue» : value → Bool
  | .D _ => true
  | .«% W %» _ _ => true
  | .«% S %» _ _ => true
  | .«% '.' % V %» _ _ _ => true
  | _ => false


def «sub:value:invalidHeaderValue» : value → Bool
  | .«'{#}'» => true
  | _ => false


def «sub:value:listValue» : value → Bool
  | .«LIST `[ % `]» _ => true
  | _ => false


def «sub:value:matchKindValue» : value → Bool
  | .«MATCH_KIND '.' %» _ => true
  | _ => false


def «sub:value:objectReferenceValue» : value → Bool
  | .REF _ => true
  | _ => false


def «sub:value:recordValue» : value → Bool
  | .«RECORD `{ % `}» _ => true
  | .«RECORD `{ % ',' '...' `}» _ => true
  | _ => false


def «sub:value:sequenceValue» : value → Bool
  | .«SEQ `( % `)» _ => true
  | .«SEQ `( % ',' '...' `)» _ => true
  | _ => false


def «sub:value:setValue» : value → Bool
  | .«SET `{ % `}» _ => true
  | .«SET `{ % `( % `) `}» _ _ => true
  | .«SET `{ % '&&&' % `}» _ _ => true
  | .«SET `{ % '..' % `}» _ _ => true
  | .«SET `{ '...' `}» => true
  | _ => false


def «sub:value:stringLiteral» : value → Bool
  | .«'"' % '"'» _ => true
  | _ => false


def «sub:value:structValue» : value → Bool
  | .«STRUCT % `{ % `}» _ _ => true
  | _ => false


def «sub:value:tableMetadataEnumValue» : value → Bool
  | .«TABLE_ENUM % '.' %» _ _ => true
  | _ => false


def «sub:value:tableMetadataStructValue» : value → Bool
  | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» _ _ _ _ => true
  | _ => false


def «sub:value:tupleValue» : value → Bool
  | .«TUPLE `( % `)» _ => true
  | _ => false


set_option inductive.autoPromoteIndices false in
inductive SpecTecCall : Type → Type 1 where
  | «$ite» (X : Type) (input0 : _root_.Bool) (input1 : X) (input2 : X) : SpecTecCall X
  | «$max_nat» (input0 : (_root_.List _root_.Nat)) : SpecTecCall _root_.Nat
  | «$min_nat» (input0 : (_root_.List _root_.Nat)) : SpecTecCall _root_.Nat
  | «$text_to_int» (input0 : _root_.String) : SpecTecCall _root_.Int
  | «$split_text» (input0 : _root_.String) (input1 : _root_.String) : SpecTecCall (_root_.List _root_.String)
  | «$concat_text» (input0 : (_root_.List _root_.String)) : SpecTecCall _root_.String
  | «$join_text» (input0 : (_root_.List _root_.String)) (input1 : _root_.String) : SpecTecCall _root_.String
  | «$replace_text'» (input0 : _root_.Nat) (input1 : _root_.Nat) (input2 : _root_.String) (input3 : _root_.String) (input4 : _root_.String) : SpecTecCall _root_.String
  | «$replace_text» (input0 : _root_.String) (input1 : _root_.String) (input2 : _root_.String) : SpecTecCall _root_.String
  | «$replace_text_except'» (input0 : _root_.Nat) (input1 : _root_.Nat) (input2 : _root_.String) (input3 : _root_.String) (input4 : _root_.String) : SpecTecCall _root_.String
  | «$replace_text_except» (input0 : _root_.String) (input1 : _root_.String) (input2 : _root_.String) : SpecTecCall _root_.String
  | «$strip_prefix» (input0 : _root_.String) (input1 : _root_.String) : SpecTecCall _root_.String
  | «$strip_suffix» (input0 : _root_.String) (input1 : _root_.String) : SpecTecCall _root_.String
  | «$starts_with» (input0 : _root_.String) (input1 : _root_.String) : SpecTecCall _root_.Bool
  | «$ends_with» (input0 : _root_.String) (input1 : _root_.String) : SpecTecCall _root_.Bool
  | «$strip_prefix_rec» (input0 : _root_.String) (input1 : _root_.String) : SpecTecCall _root_.String
  | «$strip_suffix_rec» (input0 : _root_.String) (input1 : _root_.String) : SpecTecCall _root_.String
  | «$contains'» (input0 : _root_.Nat) (input1 : _root_.Nat) (input2 : _root_.String) (input3 : _root_.String) : SpecTecCall _root_.Bool
  | «$contains» (input0 : _root_.String) (input1 : _root_.String) : SpecTecCall _root_.Bool
  | «$is_some_» (X_T : Type) (input0 : (_root_.Option X_T)) : SpecTecCall _root_.Bool
  | «$opt_as_seq_» (X_T : Type) (input0 : (_root_.Option X_T)) : SpecTecCall (_root_.List X_T)
  | «$exists_» (input0 : (_root_.List _root_.Bool)) : SpecTecCall _root_.Bool
  | «$forall_» (input0 : (_root_.List _root_.Bool)) : SpecTecCall _root_.Bool
  | «$init_» (input0 : _root_.Nat) : SpecTecCall (_root_.List _root_.Nat)
  | «$repeat_» (X_T : Type) (input0 : X_T) (input1 : _root_.Nat) : SpecTecCall (_root_.List X_T)
  | «$partition_» (X : Type) (input0 : (_root_.List X)) (input1 : _root_.Nat) : SpecTecCall ((_root_.List X) × (_root_.List X))
  | «$filter_» (X : Type) (input0 : (_root_.List X)) (input1 : (_root_.List _root_.Bool)) : SpecTecCall (_root_.List X)
  | «$assoc_» (X : Type) (Y : Type) (input0 : X) (input1 : (_root_.List (X × Y))) : SpecTecCall (_root_.Option Y)
  | «$distinct_» (K : Type) (input0 : (_root_.List K)) : SpecTecCall _root_.Bool
  | «$empty_set» (K : Type) : SpecTecCall (set K)
  | «$in_set» (K_T : Type) [_root_.DecidableEq K_T] (input0 : K_T) (input1 : (set K_T)) : SpecTecCall _root_.Bool
  | «$sub_set» (K : Type) (input0 : (set K)) (input1 : (set K)) : SpecTecCall _root_.Bool
  | «$eq_set» (K : Type) (input0 : (set K)) (input1 : (set K)) : SpecTecCall _root_.Bool
  | «$empty_map» (K : Type) (V : Type) : SpecTecCall (map K V)
  | «$dom_map:case_1:pattern-iter:0» (K_T : Type) (V_T : Type) (input0 : (_root_.List (pair K_T V_T))) : SpecTecCall ((_root_.List K_T) × (_root_.List V_T))
  | «$dom_map» (K_T : Type) (V_T : Type) (input0 : (map K_T V_T)) : SpecTecCall (set K_T)
  | «$codom_map:case_1:pattern-iter:0» (K_T : Type) (V_T : Type) (input0 : (_root_.List (pair K_T V_T))) : SpecTecCall ((_root_.List K_T) × (_root_.List V_T))
  | «$codom_map» (K_T : Type) (V_T : Type) (input0 : (map K_T V_T)) : SpecTecCall (set V_T)
  | «$find_map:list» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) (input1 : K) : SpecTecCall (_root_.Option V)
  | «$find_map» (K : Type) (V : Type) (input0 : (map K V)) (input1 : K) : SpecTecCall (_root_.Option V)
  | «$find_maps» (K : Type) (V : Type) (input0 : (_root_.List (map K V))) (input1 : K) : SpecTecCall (_root_.Option V)
  | «$add_map:list» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) (input1 : K) (input2 : V) : SpecTecCall (_root_.List (pair K V))
  | «$add_map» (K : Type) (V : Type) (input0 : (map K V)) (input1 : K) (input2 : V) : SpecTecCall (map K V)
  | «$adds_map» (K : Type) (V : Type) (input0 : (map K V)) (input1 : (_root_.List K)) (input2 : (_root_.List V)) : SpecTecCall (map K V)
  | «$update_map:list» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) (input1 : K) (input2 : V) : SpecTecCall (_root_.List (pair K V))
  | «$update_map» (K : Type) (V : Type) (input0 : (map K V)) (input1 : K) (input2 : V) : SpecTecCall (map K V)
  | «$extend_map:case_1:pattern-iter:0» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) : SpecTecCall ((_root_.List K) × (_root_.List V))
  | «$extend_map:case_1:pattern-iter:2» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) : SpecTecCall ((_root_.List K) × (_root_.List V))
  | «$extend_map:case_1:iter:4» (K : Type) (V : Type) (input0 : (_root_.List K)) (input1 : (_root_.List V)) : SpecTecCall (_root_.List (pair K V))
  | «$extend_map:case_1:pattern-iter:7» (K : Type) (V : Type) (input0 : (_root_.List (pair K V))) : SpecTecCall ((_root_.List K) × (_root_.List V))
  | «$extend_map:case_1:iter:9» (K : Type) (V : Type) (input0 : (_root_.List K)) (input1 : (_root_.List V)) : SpecTecCall (_root_.List (pair K V))
  | «$extend_map» (K : Type) (V : Type) (input0 : (map K V)) (input1 : (map K V)) : SpecTecCall (map K V)
  | «$print_» (X : Type) [_root_.SpecTecPrint X] (input0 : X) : SpecTecCall _root_.String
  | «$modulo» (input0 : _root_.Nat) (input1 : _root_.Nat) : SpecTecCall (_root_.Option _root_.Nat)
  | «$modulo_42» (input0 : _root_.Nat) : SpecTecCall _root_.Nat
  | «$name» (input0 : name) : SpecTecCall nameIR
  | «$tableCustomName» (input0 : tableCustomName) : SpecTecCall nameIR
  | «$fresh_typeId» : SpecTecCall typeId
  | «$fresh_typeIds» (input0 : _root_.Nat) : SpecTecCall (_root_.List typeId)
  | «$objectId_ends_with» (input0 : objectId) (input1 : nameIR) : SpecTecCall _root_.Bool
  | «$bitstr_to_int» (input0 : _root_.Int) (input1 : _root_.Int) : SpecTecCall _root_.Int
  | «$int_to_bitstr» (input0 : _root_.Int) (input1 : _root_.Int) : SpecTecCall _root_.Int
  | «$bits_to_int_signed» (input0 : bits) : SpecTecCall _root_.Int
  | «$int_to_bits_unsigned» (input0 : _root_.Nat) (input1 : _root_.Int) : SpecTecCall bits
  | «$int_to_bits_signed» (input0 : _root_.Nat) (input1 : _root_.Int) : SpecTecCall bits
  | «$update_fieldValue» (input0 : (_root_.List fieldValue)) (input1 : nameIR) (input2 : value) : SpecTecCall (_root_.List fieldValue)
  | «$invalidate_header» (input0 : headerValue) : SpecTecCall headerValue
  | «$invalidate_headerUnion:case_1:pattern-iter:0» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$invalidate_headerUnion:case_1:iter:4» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «$write_bits_from_value:case_7:pattern-iter:1» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List id) × (_root_.List value))
  | «$write_bits_from_value:case_8:pattern-iter:1» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List id) × (_root_.List value))
  | «$write_bits_from_value:case_10:pattern-iter:1» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List id) × (_root_.List value))
  | «$capture_avoiding_:case_1:iter:8» (input0 : bound) (input1 : (_root_.List typeParameterIR)) : SpecTecCall _root_.Unit
  | «$capture_avoiding:case_1:iter:8» (input0 : bound) (input1 : (_root_.List typeId)) : SpecTecCall _root_.Unit
  | «Type_alpha:serializable:pattern-iter:1» (input0 : (_root_.List valueFieldIR)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «Type_alpha:serializable:iter:4» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List valueFieldIR)
  | «Type_alpha:non-default_2:iter:6» (input0 : (_root_.List annotationList)) (input1 : (_root_.List annotationList)) : SpecTecCall _root_.Unit
  | «Type_alpha:non-default_2:iter:7» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecCall _root_.Unit
  | «Type_alpha:default_2:iter:6» (input0 : (_root_.List annotationList)) (input1 : (_root_.List annotationList)) : SpecTecCall _root_.Unit
  | «Type_alpha:default_2:iter:7» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecCall _root_.Unit
  | «$shl» (input0 : _root_.Int) (input1 : _root_.Int) : SpecTecCall _root_.Int
  | «$shr» (input0 : _root_.Int) (input1 : _root_.Int) : SpecTecCall _root_.Int
  | «$shr_arith» (input0 : _root_.Int) (input1 : _root_.Int) (input2 : _root_.Int) : SpecTecCall _root_.Int
  | «$bitacc» (input0 : _root_.Int) (input1 : _root_.Int) (input2 : _root_.Int) : SpecTecCall _root_.Int
  | «$bitacc_replace» (input0 : _root_.Int) (input1 : _root_.Int) (input2 : _root_.Int) (input3 : _root_.Int) : SpecTecCall _root_.Int
  | «$bin_eq:case_14:iter:2» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$bin_eq:case_14:iter:3» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$bin_eq:case_14:iter:8» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$bin_eq:case_15:iter:2» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$bin_eq:case_15:iter:3» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$bin_eq:case_15:iter:8» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$bin_eq:case_16:iter:2» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$bin_eq:case_16:iter:3» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$bin_eq:case_16:iter:8» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$default:case_17:pattern-iter:1» (input0 : (_root_.List valueFieldIR)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$default:case_17:iter:4» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (value × _root_.String))
  | «$default:case_18:pattern-iter:1» (input0 : (_root_.List valueFieldIR)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$default:case_18:iter:4» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (value × _root_.String))
  | «$cast_struct:case_1:pattern-iter:0» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$cast_struct:case_1:iter:3» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «$cast_header:case_1:pattern-iter:0» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$cast_header:case_1:iter:3» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «$cast_header_union:case_1:pattern-iter:0» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$cast_header_union:case_1:iter:3» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «$cast_sequence:case_7:iter:5» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «$cast_sequence:case_8:iter:5» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «$cast_sequence:case_13:iter:8» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «$cast_sequence:case_14:iter:8» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «$cast_record:case_1:pattern-iter:3» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$cast_record:case_1:iter:6» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (pair _root_.String value))
  | «$cast_record:case_1:iter:5» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option value))
  | «$cast_record:case_1:iter:9» (input0 : (_root_.List (_root_.Option value))) : SpecTecCall _root_.Unit
  | «$cast_record:case_1:iter:10» (input0 : (_root_.List (_root_.Option value))) : SpecTecCall (_root_.List value)
  | «$cast_record:case_1:iter:13» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «$cast_record:case_2:pattern-iter:3» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$cast_record:case_2:iter:6» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (pair _root_.String value))
  | «$cast_record:case_2:iter:5» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option value))
  | «$cast_record:case_2:iter:9» (input0 : (_root_.List (_root_.Option value))) : SpecTecCall _root_.Unit
  | «$cast_record:case_2:iter:10» (input0 : (_root_.List (_root_.Option value))) : SpecTecCall (_root_.List value)
  | «$cast_record:case_2:iter:13» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «$cast_record:case_3:pattern-iter:3» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$cast_record:case_3:iter:6» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (pair _root_.String value))
  | «$cast_record:case_3:iter:5» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option value))
  | «$cast_record:case_3:iter:9» (input0 : (_root_.List (_root_.Option value))) : SpecTecCall _root_.Unit
  | «$cast_record:case_3:iter:10» (input0 : (_root_.List (_root_.Option value))) : SpecTecCall (_root_.List value)
  | «$cast_record:case_3:iter:13» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «$cast_record:case_4:pattern-iter:3» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$cast_record:case_4:iter:6» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (pair _root_.String value))
  | «$cast_record:case_4:iter:5» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option value))
  | «$cast_record:case_4:iter:9» (input0 : (_root_.List (_root_.Option value))) : SpecTecCall _root_.Unit
  | «$cast_record:case_4:iter:10» (input0 : (_root_.List (_root_.Option value))) : SpecTecCall (_root_.List value)
  | «$cast_record:case_4:iter:13» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «$cast_record:case_5:pattern-iter:3» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$cast_record:case_5:iter:6» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (pair _root_.String value))
  | «$cast_record:case_5:iter:9» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «$cast_record:case_6:pattern-iter:3» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$cast_record:case_6:iter:6» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (pair _root_.String value))
  | «$cast_record:case_6:iter:9» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «$cast_record_field:case_1:pattern-iter:0» (input0 : (_root_.List (pair _root_.String value))) : SpecTecCall ((_root_.List id) × (_root_.List value))
  | «$cast_record_field:case_1:iter:2» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (pair _root_.String value))
  | «$cast_record_field:case_2:pattern-iter:0» (input0 : (_root_.List (pair _root_.String value))) : SpecTecCall ((_root_.List id) × (_root_.List value))
  | «$cast_record_field:case_2:iter:2» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (pair _root_.String value))
  | «$is_defaultable_typeIR:row_9:pattern-iter:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$is_defaultable_typeIR:row_10:pattern-iter:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$is_defaultable_typeIR:row_11:pattern-iter:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$is_defaultable_typeIR» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$is_defaultable_typeIR:row_6:iter:0» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$is_defaultable_typeIR:row_9:iter:2» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$is_defaultable_typeIR:row_10:iter:2» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$is_defaultable_typeIR:row_11:iter:2» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$is_equalable_typeIR» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$is_assignable_typeIR» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$is_serializable_typeIR:row_10:pattern-iter:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$is_serializable_typeIR:row_11:pattern-iter:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$is_serializable_typeIR:row_12:pattern-iter:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$is_serializable_typeIR» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$is_serializable_typeIR:row_7:iter:0» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$is_serializable_typeIR:row_10:iter:2» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$is_serializable_typeIR:row_11:iter:2» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$is_serializable_typeIR:row_12:iter:2» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$typeIR_of_typeDefIR:case_3:iter:1» (input0 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List typeIR)
  | «$typeIR_of_typeDefIR:case_4:iter:1» (input0 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List typeIR)
  | «$typeIR_of_typeDefIR:case_5:iter:1» (input0 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List typeIR)
  | «$typeIR_of_typeDefIR:case_7:pattern-iter:1» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : SpecTecCall ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))
  | «$typeIR_of_typeDefIR:case_7:iter:3» (input0 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List typeIR)
  | «$typeIR_of_typeDefIR:case_7:iter:5» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecCall (_root_.List (pair callTargetId externMethodTypeDefIR))
  | «$typeIR_of_typeDefIR:case_8:iter:1» (input0 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List typeIR)
  | «$typeIR_of_typeDefIR:case_9:iter:1» (input0 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List typeIR)
  | «$typeIR_of_typeDefIR:case_10:iter:1» (input0 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List typeIR)
  | «$id_of_parameterIR» (input0 : parameterIR) : SpecTecCall id
  | «$is_default_parameterIR» (input0 : parameterIR) : SpecTecCall _root_.Bool
  | «$annotationList_of_parameterIR» (input0 : parameterIR) : SpecTecCall annotationList
  | «$parameterListIR_of_actionTypeDefIR» (input0 : actionTypeDefIR) : SpecTecCall (_root_.List parameterIR)
  | «$parameterListIR_of_definedFunctionTypeDefIR» (input0 : definedFunctionTypeDefIR) : SpecTecCall (_root_.List parameterIR)
  | «$parameterListIR_of_externFunctionTypeDefIR» (input0 : externFunctionTypeDefIR) : SpecTecCall (_root_.List parameterIR)
  | «$parameterListIR_of_parserApplyMethodTypeIR» (input0 : parserApplyMethodTypeIR) : SpecTecCall (_root_.List parameterIR)
  | «$parameterListIR_of_controlApplyMethodTypeIR» (input0 : controlApplyMethodTypeIR) : SpecTecCall (_root_.List parameterIR)
  | «$parameterListIR_of_tableApplyMethodTypeDefIR» (input0 : tableApplyMethodTypeDefIR) : SpecTecCall (_root_.List parameterIR)
  | «$parameterListIR_of_constructorTypeDefIR» (input0 : constructorTypeDefIR) : SpecTecCall (_root_.List parameterIR)
  | «$free_typeIR:case_9:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$free_typeIR:case_10:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$free_typeIR:case_11:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$free_typeIR:case_14:pattern-iter:1» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : SpecTecCall ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))
  | «$free_typeIR:case_23:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$free_typeIR:case_24:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$empty_theta» : SpecTecCall theta
  | «$capture_avoiding_:case_1:iter:0» (input0 : theta) (input1 : (_root_.List typeId)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «$capture_avoiding_:case_1:iter:2» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «$capture_avoiding_:case_1:iter:3» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «$capture_avoiding_:case_1:iter:10» (input0 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List typeIR)
  | «$capture_avoiding:case_1:iter:0» (input0 : theta) (input1 : (_root_.List typeId)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «$capture_avoiding:case_1:iter:2» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «$capture_avoiding:case_1:iter:3» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «$capture_avoiding:case_1:iter:10» (input0 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List typeIR)
  | «$capture_avoiding:case_1:iter:12» (input0 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List typeIR)
  | «$subst_typeIR':case_10:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$subst_typeIR':case_10:iter:7» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldTypeIR)
  | «$subst_typeIR':case_11:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$subst_typeIR':case_11:iter:7» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldTypeIR)
  | «$subst_typeIR':case_12:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$subst_typeIR':case_12:iter:7» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldTypeIR)
  | «$subst_typeIR':case_15:pattern-iter:1» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : SpecTecCall ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))
  | «$subst_typeIR':case_15:iter:8» (input0 : (_root_.List callableTypeDefIR)) : SpecTecCall (_root_.List externMethodTypeDefIR)
  | «$subst_typeIR':case_15:iter:10» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecCall (_root_.List (pair callTargetId externMethodTypeDefIR))
  | «$subst_typeIR':case_24:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «$subst_typeIR':case_24:iter:5» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldTypeIR)
  | «$subst_typeIR':case_25:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «$subst_typeIR':case_25:iter:5» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldTypeIR)
  | «$specialize_typeDefIR:case_1:iter:1» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «$specialize_callableTypeDefIR:case_1:iter:2» (input0 : (_root_.List typeId)) : SpecTecCall (_root_.List typeArgumentIR)
  | «$specialize_callableTypeDefIR:case_1:iter:3» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «$specialize_callableTypeDefIR:case_1:iter:5» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «$specialize_callableTypeDefIR:case_2:iter:2» (input0 : (_root_.List typeId)) : SpecTecCall (_root_.List typeArgumentIR)
  | «$specialize_callableTypeDefIR:case_2:iter:3» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «$specialize_constructorTypeDefIR:case_1:iter:1» (input0 : (_root_.List typeId)) : SpecTecCall (_root_.List typeArgumentIR)
  | «$specialize_constructorTypeDefIR:case_1:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «$specialize_constructorTypeDefIR:case_1:iter:4» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «$specialize_constructorTypeDefIR:case_2:iter:1» (input0 : (_root_.List typeId)) : SpecTecCall (_root_.List typeArgumentIR)
  | «$specialize_constructorTypeDefIR:case_2:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Type_alpha:non-default_2:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Type_alpha:non-default_2:pattern-iter:4» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List typeIR) × ((_root_.List annotationList) × (_root_.List nameIR)))
  | «Type_alpha:default_2:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Type_alpha:default_2:pattern-iter:4» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List typeIR) × ((_root_.List annotationList) × (_root_.List nameIR)))
  | «ExternMethodTypeDef_alpha:rule:iter:3» (input0 : (_root_.List typeParameterIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «ExternMethodTypeDef_alpha:rule:iter:9» (input0 : (_root_.List typeParameterIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «$default:case_13:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «$default:case_14:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «$default:case_15:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «$cast_sequence:case_7:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$cast_sequence:case_8:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$cast_sequence:case_13:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$cast_sequence:case_14:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$cast_record:case_1:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «$cast_record:case_2:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «$cast_record:case_3:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «$cast_record:case_4:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «$cast_record:case_5:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «$cast_record:case_6:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «$sizeof_minSizeInBits':case_11:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$sizeof_minSizeInBits':case_12:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$sizeof_minSizeInBits':case_13:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$sizeof_maxSizeInBits':case_11:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$sizeof_maxSizeInBits':case_12:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$sizeof_maxSizeInBits':case_13:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$type_of_typedExpressionIR» (input0 : typedExpressionIR) : SpecTecCall typeIR
  | «$ctk_of_typedExpressionIR» (input0 : typedExpressionIR) : SpecTecCall ctk
  | «$type_of_typedLvalueIR» (input0 : typedLvalueIR) : SpecTecCall typeIR
  | «$flatten_objectInitializerOptIR» (input0 : objectInitializerOptIR) : SpecTecCall objectDeclarationListIR
  | «$tableEntryPriorityOptIR_of_tableEntryIR» (input0 : tableEntryIR) : SpecTecCall tableEntryPriorityOptIR
  | «$partition_parameterListIR» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List nameIR)) : SpecTecCall ((_root_.List parameterIR) × ((_root_.List parameterIR) × (_root_.List parameterIR)))
  | «$align_parameterListIR:case_1:iter:1» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR)))))
  | «$align_parameterListIR:case_1:iter:2» (input0 : (_root_.List nameIR)) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List (pair _root_.String parameterIR))
  | «$align_parameterListIR_given:case_1:pattern-iter:0» (input0 : (_root_.List (pair _root_.String parameterIR))) : SpecTecCall ((_root_.List id) × (_root_.List parameterIR))
  | «$align_parameterListIR_given:case_2:pattern-iter:0» (input0 : (_root_.List (pair _root_.String parameterIR))) : SpecTecCall ((_root_.List id) × (_root_.List parameterIR))
  | «$align_parameterListIR_given:case_2:iter:3» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List (pair _root_.String parameterIR))
  | «$align_parameterListIR_given:case_3:pattern-iter:0» (input0 : (_root_.List (pair _root_.String parameterIR))) : SpecTecCall ((_root_.List id) × (_root_.List parameterIR))
  | «$align_parameterListIR_given:case_3:iter:2» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List (pair _root_.String parameterIR))
  | «$align_parameterListIR_given:case_4:pattern-iter:0» (input0 : (_root_.List (pair _root_.String parameterIR))) : SpecTecCall ((_root_.List id) × (_root_.List parameterIR))
  | «$align_parameterListIR_given:case_4:iter:2» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List (pair _root_.String parameterIR))
  | «$align_parameterListIR_given:case_4:iter:5» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List (pair _root_.String parameterIR))
  | «$align_parameterListIR_given:case_5:pattern-iter:0» (input0 : (_root_.List (pair _root_.String parameterIR))) : SpecTecCall ((_root_.List id) × (_root_.List parameterIR))
  | «$align_parameterListIR_given:case_5:iter:2» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List (pair _root_.String parameterIR))
  | «$align_parameterListIR_given:case_5:iter:5» (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List (pair _root_.String parameterIR))
  | «$match_overloaded_named:case_1:iter:1» (V_T : Type) (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «$match_overloaded_named:case_2:iter:1» (V_T : Type) (input0 : (_root_.List id)) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «$match_overloaded_named:case_2:iter:3» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$match_overloaded_named:case_2:iter:7» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$match_overloaded_named:case_2:iter:11» (V_T : Type) (input0 : (_root_.List id)) (input1 : (_root_.List id)) : SpecTecCall (_root_.List _root_.Bool)
  | «$match_overloaded_named:case_2:iter:18» (V_T : Type) (input0 : (_root_.List id)) (input1 : (_root_.List id)) : SpecTecCall (_root_.List _root_.Bool)
  | «$match_overloaded_unnamed:case_1:iter:1» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$match_overloaded_unnamed:case_2:iter:1» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$match_overloaded_unnamed:case_2:iter:10» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «$match_overloaded_unnamed:case_2:iter:12» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List id)
  | «$match_overloaded_unnamed:case_3:iter:1» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$match_overloaded_unnamed:case_3:iter:8» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «$match_overloaded_unnamed:case_3:iter:12» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List id)
  | «$find_overloadeds_named:case_2:pattern-iter:0» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecCall ((_root_.List V) × (_root_.List callTargetId))
  | «$find_overloadeds_named:case_2:iter:3» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callTargetId)) : SpecTecCall (_root_.List (pair callTargetId V))
  | «$find_overloadeds_named:case_3:pattern-iter:0» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecCall ((_root_.List V) × (_root_.List callTargetId))
  | «$find_overloadeds_named:case_3:iter:3» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callTargetId)) : SpecTecCall (_root_.List (pair callTargetId V))
  | «$find_overloadeds_unnamed:case_2:pattern-iter:0» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecCall ((_root_.List V) × (_root_.List callTargetId))
  | «$find_overloadeds_unnamed:case_2:iter:3» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callTargetId)) : SpecTecCall (_root_.List (pair callTargetId V))
  | «$find_overloadeds_unnamed:case_3:pattern-iter:0» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecCall ((_root_.List V) × (_root_.List callTargetId))
  | «$find_overloadeds_unnamed:case_3:iter:3» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callTargetId)) : SpecTecCall (_root_.List (pair callTargetId V))
  | «$find_overloaded:case_1:pattern-iter:0» (V_T : Type) (input0 : (_root_.List (pair callTargetId V_T))) : SpecTecCall ((_root_.List V_T) × (_root_.List callableId))
  | «$find_overloaded:case_1:iter:2» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : SpecTecCall (_root_.List (_root_.Option id))
  | «$find_overloaded:case_1:iter:3» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : SpecTecCall _root_.Unit
  | «$find_overloaded:case_1:iter:4» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : SpecTecCall (_root_.List id)
  | «$find_overloaded:case_1:iter:5» (V_T : Type) (input0 : (_root_.List V_T)) (input1 : (_root_.List callableId)) : SpecTecCall (_root_.List (pair callTargetId V_T))
  | «$find_overloaded:case_2:pattern-iter:0» (V_T : Type) (input0 : (_root_.List (pair callTargetId V_T))) : SpecTecCall ((_root_.List V_T) × (_root_.List callableId))
  | «$find_overloaded:case_2:iter:2» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : SpecTecCall (_root_.List (_root_.Option id))
  | «$find_overloaded:case_2:iter:3» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : SpecTecCall _root_.Unit
  | «$find_overloaded:case_2:iter:4» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : SpecTecCall (_root_.List id)
  | «$find_overloaded:case_2:iter:5» (V_T : Type) (input0 : (_root_.List V_T)) (input1 : (_root_.List callableId)) : SpecTecCall (_root_.List (pair callTargetId V_T))
  | «$find_overloaded:case_3:pattern-iter:0» (V_T : Type) (input0 : (_root_.List (pair callTargetId V_T))) : SpecTecCall ((_root_.List V_T) × (_root_.List callableId))
  | «$find_overloaded:case_3:iter:2» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : SpecTecCall _root_.Unit
  | «$find_overloaded:case_3:iter:3» (V_T : Type) (input0 : (_root_.List V_T)) (input1 : (_root_.List callableId)) : SpecTecCall (_root_.List (pair callTargetId V_T))
  | «$find_overloaded:case_4:pattern-iter:0» (V_T : Type) (input0 : (_root_.List (pair callTargetId V_T))) : SpecTecCall ((_root_.List V_T) × (_root_.List callableId))
  | «$find_overloaded:case_4:iter:2» (V_T : Type) (input0 : (_root_.List (_root_.Option id))) : SpecTecCall _root_.Unit
  | «$find_overloaded:case_4:iter:3» (V_T : Type) (input0 : (_root_.List V_T)) (input1 : (_root_.List callableId)) : SpecTecCall (_root_.List (pair callTargetId V_T))
  | «$find_non_overloaded:case_1:pattern-iter:0» (V_T : Type) (input0 : (_root_.List (pair callTargetId V_T))) : SpecTecCall ((_root_.List V_T) × (_root_.List callableId))
  | «$find_non_overloaded:case_1:iter:2» (V_T : Type) (input0 : (_root_.List V_T)) (input1 : (_root_.List callableId)) : SpecTecCall (_root_.List (pair callTargetId V_T))
  | «$find_non_overloaded:case_2:pattern-iter:0» (V_T : Type) (input0 : (_root_.List (pair callTargetId V_T))) : SpecTecCall ((_root_.List V_T) × (_root_.List callableId))
  | «$find_non_overloadeds:case_2:pattern-iter:0» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecCall ((_root_.List V) × (_root_.List callableId))
  | «$find_non_overloadeds:case_2:iter:2» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callableId)) : SpecTecCall (_root_.List (pair callTargetId V))
  | «$find_non_overloadeds:case_2:pattern-iter:5» (V : Type) (input0 : (_root_.List (callTargetId × V))) : SpecTecCall ((_root_.List V) × (_root_.List callableId))
  | «$find_non_overloadeds:case_2:iter:7» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callableId)) : SpecTecCall (_root_.List (callTargetId × V))
  | «$find_non_overloadeds:case_3:pattern-iter:0» (V : Type) (input0 : (_root_.List (pair callTargetId V))) : SpecTecCall ((_root_.List V) × (_root_.List callableId))
  | «$find_non_overloadeds:case_3:iter:2» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callableId)) : SpecTecCall (_root_.List (pair callTargetId V))
  | «$find_non_overloadeds:case_3:pattern-iter:5» (V : Type) (input0 : (_root_.List (callTargetId × V))) : SpecTecCall ((_root_.List V) × (_root_.List callableId))
  | «$find_non_overloadeds:case_3:iter:7» (V : Type) (input0 : (_root_.List V)) (input1 : (_root_.List callableId)) : SpecTecCall (_root_.List (callTargetId × V))
  | «$find_non_overloadeds» (V : Type) (input0 : (map callableId V)) (input1 : nameIR) : SpecTecCall (_root_.List (callableId × V))
  | «$find_non_overloaded» (V_T : Type) (input0 : (map callableId V_T)) (input1 : nameIR) : SpecTecCall (_root_.Option (callableId × V_T))
  | «$name_annotation:case_1:iter:3» (input0 : (_root_.List (_root_.Option nameIR))) : SpecTecCall (_root_.List (_root_.List _root_.String))
  | «$subexpressions_of_expressionIR:case_7:pattern-iter:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecCall ((_root_.List nameIR) × (_root_.List typedExpressionIR))
  | «$subexpressions_of_expressionIR:case_8:pattern-iter:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecCall ((_root_.List nameIR) × (_root_.List typedExpressionIR))
  | «$sink» (T : Type) : SpecTecCall T
  | «$lift_nameIR_as_identifier» (input0 : nameIR) : SpecTecCall identifier
  | «$lift_nameIR_as_typeIdentifier» (input0 : nameIR) : SpecTecCall typeIdentifier
  | «$lift_nameIR_as_nonTypeName» (input0 : nameIR) : SpecTecCall nonTypeName
  | «$lift_nameIR_as_typeName» (input0 : nameIR) : SpecTecCall typeName
  | «$unflatten_nameList'» (input0 : nameList) (input1 : (_root_.List name)) : SpecTecCall nameList
  | «$lift_value» (input0 : value) : SpecTecCall expression
  | «$unflatten_typeParameterList'» (input0 : typeParameterList) (input1 : (_root_.List typeParameter)) : SpecTecCall typeParameterList
  | «$unflatten_nonEmptyParameterList'» (input0 : nonEmptyParameterList) (input1 : (_root_.List parameter)) : SpecTecCall nonEmptyParameterList
  | «$lift_constantInitializerIR_as_initializer» (input0 : constantInitializerIR) : SpecTecCall initializer
  | «$unflatten_namedExpressionList'» (input0 : namedExpressionList) (input1 : (_root_.List namedExpression)) : SpecTecCall namedExpressionList
  | «$lift_literalExpressionIR» (input0 : literalExpressionIR) : SpecTecCall literalExpression
  | «$lift_defaultExpressionIR» (input0 : defaultExpressionIR) : SpecTecCall defaultExpression
  | «$unflatten_expressionList'» (input0 : expressionList) (input1 : (_root_.List expression)) : SpecTecCall expressionList
  | «$unflatten_simpleKeysetExpressionList'» (input0 : simpleKeysetExpressionList) (input1 : (_root_.List simpleKeysetExpression)) : SpecTecCall simpleKeysetExpressionList
  | «$unflatten_realTypeArgumentList'» (input0 : realTypeArgumentList) (input1 : (_root_.List realTypeArgument)) : SpecTecCall realTypeArgumentList
  | «$unflatten_typeArgumentList'» (input0 : typeArgumentList) (input1 : (_root_.List typeArgument)) : SpecTecCall typeArgumentList
  | «$unflatten_argumentListNonEmpty'» (input0 : argumentListNonEmpty) (input1 : (_root_.List argument)) : SpecTecCall argumentListNonEmpty
  | «$lift_emptyStatementIR» (input0 : emptyStatementIR) : SpecTecCall emptyStatement
  | «$lift_exitStatementIR» (input0 : exitStatementIR) : SpecTecCall exitStatement
  | «$unflatten_blockElementStatementList'» (input0 : blockElementStatementList) (input1 : (_root_.List blockElementStatement)) : SpecTecCall blockElementStatementList
  | «$unflatten_blockElementStatementList» (input0 : (_root_.List blockElementStatement)) : SpecTecCall blockElementStatementList
  | «$unflatten_switchCaseList'» (input0 : switchCaseList) (input1 : (_root_.List switchCase)) : SpecTecCall switchCaseList
  | «$unflatten_switchCaseList» (input0 : (_root_.List switchCase)) : SpecTecCall switchCaseList
  | «$lift_breakStatementIR» (input0 : breakStatementIR) : SpecTecCall breakStatement
  | «$lift_continueStatementIR» (input0 : continueStatementIR) : SpecTecCall continueStatement
  | «$unflatten_objectDeclarationList'» (input0 : objectDeclarationList) (input1 : (_root_.List objectDeclaration)) : SpecTecCall objectDeclarationList
  | «$unflatten_objectDeclarationList» (input0 : (_root_.List objectDeclaration)) : SpecTecCall objectDeclarationList
  | «$unflatten_typeFieldList'» (input0 : typeFieldList) (input1 : (_root_.List typeField)) : SpecTecCall typeFieldList
  | «$unflatten_typeFieldList» (input0 : (_root_.List typeField)) : SpecTecCall typeFieldList
  | «$unflatten_externConstructorOrMethodPrototypeList'» (input0 : externConstructorOrMethodPrototypeList) (input1 : (_root_.List externConstructorOrMethodPrototype)) : SpecTecCall externConstructorOrMethodPrototypeList
  | «$unflatten_externConstructorOrMethodPrototypeList» (input0 : (_root_.List externConstructorOrMethodPrototype)) : SpecTecCall externConstructorOrMethodPrototypeList
  | «$unflatten_selectCaseList'» (input0 : selectCaseList) (input1 : (_root_.List selectCase)) : SpecTecCall selectCaseList
  | «$unflatten_selectCaseList» (input0 : (_root_.List selectCase)) : SpecTecCall selectCaseList
  | «$unflatten_parserBlockElementStatementList'» (input0 : parserBlockElementStatementList) (input1 : (_root_.List parserBlockElementStatement)) : SpecTecCall parserBlockElementStatementList
  | «$unflatten_parserBlockElementStatementList» (input0 : (_root_.List parserBlockElementStatement)) : SpecTecCall parserBlockElementStatementList
  | «$unflatten_parserStateList'» (input0 : parserStateList) (input1 : (_root_.List parserState)) : SpecTecCall parserStateList
  | «$unflatten_parserLocalDeclarationList'» (input0 : parserLocalDeclarationList) (input1 : (_root_.List parserLocalDeclaration)) : SpecTecCall parserLocalDeclarationList
  | «$unflatten_parserLocalDeclarationList» (input0 : (_root_.List parserLocalDeclaration)) : SpecTecCall parserLocalDeclarationList
  | «$lift_constOptIR» (input0 : constOptIR) : SpecTecCall constOpt
  | «$unflatten_tableKeyList'» (input0 : tableKeyList) (input1 : (_root_.List tableKey)) : SpecTecCall tableKeyList
  | «$unflatten_tableKeyList» (input0 : (_root_.List tableKey)) : SpecTecCall tableKeyList
  | «$unflatten_tableActionList'» (input0 : tableActionList) (input1 : (_root_.List tableAction)) : SpecTecCall tableActionList
  | «$unflatten_tableActionList» (input0 : (_root_.List tableAction)) : SpecTecCall tableActionList
  | «$lift_tableEntryPriorityIR» (input0 : tableEntryPriorityIR) : SpecTecCall tableEntryPriority
  | «$unflatten_tableEntryList'» (input0 : tableEntryList) (input1 : (_root_.List tableEntry)) : SpecTecCall tableEntryList
  | «$unflatten_tableEntryList» (input0 : (_root_.List tableEntry)) : SpecTecCall tableEntryList
  | «$unflatten_tablePropertyList'» (input0 : tablePropertyList) (input1 : (_root_.List tableProperty)) : SpecTecCall tablePropertyList
  | «$unflatten_tablePropertyList» (input0 : (_root_.List tableProperty)) : SpecTecCall tablePropertyList
  | «$unflatten_controlLocalDeclarationList'» (input0 : controlLocalDeclarationList) (input1 : (_root_.List controlLocalDeclaration)) : SpecTecCall controlLocalDeclarationList
  | «$unflatten_controlLocalDeclarationList» (input0 : (_root_.List controlLocalDeclaration)) : SpecTecCall controlLocalDeclarationList
  | «$unflatten_p4program'» (input0 : p4program) (input1 : (_root_.List declaration)) : SpecTecCall p4program
  | «$unflatten_p4program» (input0 : (_root_.List declaration)) : SpecTecCall p4program
  | «$empty_typeFrame» : SpecTecCall typeFrame
  | «$empty_typeDefEnv» : SpecTecCall typeDefEnv
  | «$empty_callableTypeDefEnv» : SpecTecCall callableTypeDefEnv
  | «$empty_constructorTypeDefEnv» : SpecTecCall constructorTypeDefEnv
  | «$empty_typingContext» : SpecTecCall typingContext
  | «$enter_t» (input0 : typingContext) : SpecTecCall typingContext
  | «$exit_t» (input0 : typingContext) : SpecTecCall typingContext
  | «$set_control_t» (input0 : typingContext) (input1 : flow) : SpecTecCall typingContext
  | «$enter_loop_t» (input0 : typingContext) : SpecTecCall typingContext
  | «$set_loop_t» (input0 : typingContext) (input1 : loop) : SpecTecCall typingContext
  | «$add_typeParameters_t:case_1:iter:0» (input0 : (_root_.List typeId)) : SpecTecCall (_root_.List typeDefIR)
  | «$add_callableDef_non_overload_t:case_1:pattern-iter:1» (input0 : (_root_.List callTargetId)) : SpecTecCall ((_root_.List (_root_.List id)) × (_root_.List nameIR))
  | «$add_callableDef_non_overload_t:case_2:pattern-iter:1» (input0 : (_root_.List callTargetId)) : SpecTecCall ((_root_.List (_root_.List id)) × (_root_.List nameIR))
  | «$add_constructorDef_t» (input0 : typingContext) (input1 : callableId) (input2 : constructorTypeDefIR) : SpecTecCall typingContext
  | «$add_constructorDef_non_overload_t:case_1:pattern-iter:1» (input0 : (_root_.List callTargetId)) : SpecTecCall ((_root_.List (_root_.List id)) × (_root_.List nameIR))
  | «$add_constructorDef_non_overload_t» (input0 : typingContext) (input1 : callableId) (input2 : constructorTypeDefIR) : SpecTecCall typingContext
  | «$add_constructorDefs_t» (input0 : typingContext) (input1 : (_root_.List callableId)) (input2 : (_root_.List constructorTypeDefIR)) : SpecTecCall typingContext
  | «$empty_tableContext» : SpecTecCall tableContext
  | «$add_key_tbl» (input0 : tableContext) (input1 : id) (input2 : typeIR) : SpecTecCall tableContext
  | «$add_action_tbl» (input0 : tableContext) (input1 : prefixedNameIR) (input2 : (_root_.List parameterIR)) (input3 : argumentListIR) : SpecTecCall tableContext
  | «$is_lpm_key'» (input0 : nameIR) : SpecTecCall _root_.Bool
  | «$is_lpm_key» (input0 : tableKeyIR) : SpecTecCall _root_.Bool
  | «$requires_priority'» (input0 : nameIR) : SpecTecCall _root_.Bool
  | «$requires_priority» (input0 : tableKeyIR) : SpecTecCall _root_.Bool
  | «$update_mode_tbl:case_1:iter:0» (input0 : (_root_.List tableKeyIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$update_mode_tbl:case_2:iter:0» (input0 : (_root_.List tableKeyIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$update_mode_tbl:case_2:iter:3» (input0 : (_root_.List tableKeyIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$update_mode_tbl:case_3:iter:0» (input0 : (_root_.List tableKeyIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$update_mode_tbl:case_3:iter:3» (input0 : (_root_.List tableKeyIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$find_action'» (input0 : (_root_.List matchAction)) (input1 : prefixedNameIR) : SpecTecCall (_root_.Option ((_root_.List parameterIR) × argumentListIR))
  | «$find_action» (input0 : tableContext) (input1 : prefixedNameIR) : SpecTecCall (_root_.Option ((_root_.List parameterIR) × argumentListIR))
  | «$set_priorities_of_tableEntryListIR:case_1:iter:0» (input0 : (_root_.List tableEntryIR)) : SpecTecCall _root_.Unit
  | «$set_priorities_of_tableEntryListIR:case_2:iter:0» (input0 : (_root_.List tableEntryState)) : SpecTecCall (_root_.List tableEntryState)
  | «$set_priorities_of_tableEntryListIR:case_2:iter:2» (input0 : (_root_.List tableEntryState)) : SpecTecCall (_root_.List _root_.Nat)
  | «$set_priorities_of_tableEntryListIR:case_2:iter:3» (input0 : (_root_.List tableEntryIR)) : SpecTecCall _root_.Unit
  | «$set_priorities_of_tableEntryListIR:case_4:iter:1» (input0 : (_root_.List tableEntryIR)) : SpecTecCall _root_.Unit
  | «$set_priority_of_tableEntryIR» (input0 : tableEntryIR) (input1 : _root_.Nat) : SpecTecCall tableEntryIR
  | «$set_priorities_of_tableEntryListIR:case_2:iter:5» (input0 : (_root_.List _root_.Nat)) (input1 : (_root_.List tableEntryIR)) : SpecTecCall (_root_.List tableEntryIR)
  | «Type_wf:structTypeIR:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Type_wf:headerTypeIR:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Type_wf:headerUnionTypeIR:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Type_wf:serializable:pattern-iter:1» (input0 : (_root_.List valueFieldIR)) : SpecTecCall ((_root_.List value) × (_root_.List nameIR))
  | «Type_wf:externObjectTypeIR:pattern-iter:1» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : SpecTecCall ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))
  | «Type_wf:non-default_2:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Type_wf:default_2:pattern-iter:1» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «CallableType_wf:actionTypeIR:iter:4» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR)))))
  | «CallableType_wf:definedFunctionTypeIR:iter:4» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))
  | «CallableType_wf:externFunctionTypeIR:iter:2» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))
  | «CallableType_wf:non-abstract:iter:2» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))
  | «CallableType_wf:abstract:iter:4» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))
  | «CallableType_wf:parserApplyMethodTypeIR:iter:4» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))
  | «CallableType_wf:controlApplyMethodTypeIR:iter:4» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))
  | «ConstructorType_wf:externObjectTypeIR:iter:3» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))
  | «ConstructorType_wf:parserObjectTypeIR:iter:5» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))
  | «ConstructorType_wf:controlObjectTypeIR:iter:5» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))
  | «ConstructorType_wf:packageObjectTypeIR:iter:3» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))
  | «$nestable_typedef» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$nestable_new» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$nestable_list» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$nestable_array_in_tuple» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$nestable_tuple» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «Type_wf:tupleTypeIR:iter:1» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «$nestable_array» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$nestable_headerStack» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$nestable_struct» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «Type_wf:structTypeIR:iter:4» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «$nestable_header:row_8:pattern-iter:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$nestable_struct_in_header:row_7:pattern-iter:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$nestable_struct_in_header» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$nestable_struct_in_header:row_7:iter:2» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$nestable_header:row_8:iter:2» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$nestable_array_in_header» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$nestable_header» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «Type_wf:headerTypeIR:iter:4» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «$nestable_headerUnion» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «Type_wf:headerUnionTypeIR:iter:4» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «$nestable_new_in_enum_serializable» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$nestable_enum_serializable» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$nestable_tuple_in_set» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$nestable_tuple_in_set:row_6:iter:0» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$nestable_set:row_7:iter:0» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$nestable_sequence_in_set» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$nestable_sequence_in_set:row_6:iter:0» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$nestable_sequence_in_set:row_8:iter:0» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$nestable_set:row_9:iter:0» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$nestable_set» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$nestable_action» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «CallableType_wf:actionTypeIR:iter:6» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «$nestable_definedFunction» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «CallableType_wf:definedFunctionTypeIR:iter:5» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «$nestable_externFunction» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «CallableType_wf:externFunctionTypeIR:iter:3» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «$nestable_externMethod» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «CallableType_wf:non-abstract:iter:3» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «CallableType_wf:abstract:iter:5» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «$nestable_parserApplyMethod» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «CallableType_wf:parserApplyMethodTypeIR:iter:5» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «$nestable_controlApplyMethod» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «CallableType_wf:controlApplyMethodTypeIR:iter:5» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «$nestable_constructor_extern» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «ConstructorType_wf:externObjectTypeIR:iter:4» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «$nestable_constructor_parser» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «ConstructorType_wf:parserObjectTypeIR:iter:6» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «$nestable_constructor_control» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «ConstructorType_wf:controlObjectTypeIR:iter:6» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «$nestable_constructor_package» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «ConstructorType_wf:packageObjectTypeIR:iter:4» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «$definable_constructor» (input0 : typeIR) : SpecTecCall _root_.Bool
  | ExternFunctionCall_eval_lctk (input0 : typingContext) (input1 : nameIR) (input2 : (_root_.List nameIR)) : SpecTecCall value
  | «Expr_eval_lctk:non-default_2:pattern-iter:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecCall ((_root_.List nameIR) × (_root_.List typedExpressionIR))
  | «Expr_eval_lctk:non-default_2:iter:4» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «Expr_eval_lctk:default_2:pattern-iter:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecCall ((_root_.List nameIR) × (_root_.List typedExpressionIR))
  | «Expr_eval_lctk:default_2:iter:4» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «Expr_eval_lctk:serenum:pattern-iter:6» (input0 : (_root_.List valueFieldIR)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «Expr_eval_lctk:serenum:iter:8» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.String × value))
  | «Expr_eval_lctk:struct:pattern-iter:3» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «Expr_eval_lctk:struct:iter:5» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.String × value))
  | «Expr_eval_lctk:header:pattern-iter:3» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «Expr_eval_lctk:header:iter:5» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.String × value))
  | «Expr_eval_lctk:header-union:pattern-iter:3» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «Expr_eval_lctk:header-union:iter:5» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.String × value))
  | «Expr_eval_lctk:static_assert:iter:4» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR)))))
  | «Expr_eval_lctk:static_assert:iter:8» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × ((_root_.List nameIR) × (_root_.List typeIR)))))
  | «Expr_eval_lctk:static_assert:iter:9» (input0 : (_root_.List direction)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List value)) : SpecTecCall (_root_.List varTypeIR)
  | «TypeParameterListOpt_ok:rule:iter:1» (input0 : (_root_.List typeParameter)) : SpecTecCall (_root_.List typeId)
  | «Cast_expl_neq:listTypeIR:iter:4» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_expl_neq:tupleTypeIR:iter:4» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_expl_neq:arrayTypeIR:iter:4» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_expl_neq:headerStackTypeIR:iter:4» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_expl_neq:structTypeIR:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Cast_expl_neq:structTypeIR:iter:6» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_expl_neq:headerTypeIR_2:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Cast_expl_neq:headerTypeIR_2:iter:6» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_expl_neq:tupleTypeIR_2:iter:5» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_expl_neq:tupleTypeIR_2:iter:6» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:arrayTypeIR_2:iter:4» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_expl_neq:headerStackTypeIR_2:iter:4» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_expl_neq:structTypeIR_2:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Cast_expl_neq:structTypeIR_2:iter:7» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_expl_neq:structTypeIR_2:iter:8» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:headerTypeIR_3:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Cast_expl_neq:headerTypeIR_3:iter:7» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_expl_neq:headerTypeIR_3:iter:8» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:structTypeIR_3:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «Cast_expl_neq:structTypeIR_3:pattern-iter:4» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «Cast_expl_neq:structTypeIR_3:iter:7» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:structTypeIR_3:iter:9» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_expl_neq:structTypeIR_3:iter:8» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_expl_neq:structTypeIR_3:iter:12» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:structTypeIR_3:iter:13» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_expl_neq:structTypeIR_3:iter:15» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_expl_neq:structTypeIR_3:iter:14» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_expl_neq:structTypeIR_3:iter:18» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:structTypeIR_3:iter:19» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_expl_neq:structTypeIR_3:iter:22» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_expl_neq:headerTypeIR_4:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «Cast_expl_neq:headerTypeIR_4:pattern-iter:4» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «Cast_expl_neq:headerTypeIR_4:iter:7» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:headerTypeIR_4:iter:9» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_expl_neq:headerTypeIR_4:iter:8» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_expl_neq:headerTypeIR_4:iter:12» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:headerTypeIR_4:iter:13» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_expl_neq:headerTypeIR_4:iter:15» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_expl_neq:headerTypeIR_4:iter:14» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_expl_neq:headerTypeIR_4:iter:18» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:headerTypeIR_4:iter:19» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_expl_neq:headerTypeIR_4:iter:22» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_expl_neq:structTypeIR_4:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «Cast_expl_neq:structTypeIR_4:pattern-iter:4» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «Cast_expl_neq:structTypeIR_4:iter:7» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:structTypeIR_4:iter:9» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_expl_neq:structTypeIR_4:iter:8» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_expl_neq:structTypeIR_4:iter:12» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:structTypeIR_4:iter:13» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_expl_neq:structTypeIR_4:iter:15» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_expl_neq:structTypeIR_4:iter:14» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_expl_neq:structTypeIR_4:iter:18» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:structTypeIR_4:iter:19» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_expl_neq:structTypeIR_4:iter:22» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_expl_neq:structTypeIR_4:iter:24» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_expl_neq:structTypeIR_4:iter:23» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_expl_neq:structTypeIR_4:iter:27» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:structTypeIR_4:iter:28» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_expl_neq:structTypeIR_4:iter:29» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:headerTypeIR_5:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «Cast_expl_neq:headerTypeIR_5:pattern-iter:4» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «Cast_expl_neq:headerTypeIR_5:iter:7» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:headerTypeIR_5:iter:9» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_expl_neq:headerTypeIR_5:iter:8» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_expl_neq:headerTypeIR_5:iter:12» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:headerTypeIR_5:iter:13» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_expl_neq:headerTypeIR_5:iter:15» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_expl_neq:headerTypeIR_5:iter:14» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_expl_neq:headerTypeIR_5:iter:18» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:headerTypeIR_5:iter:19» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_expl_neq:headerTypeIR_5:iter:22» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_expl_neq:headerTypeIR_5:iter:24» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_expl_neq:headerTypeIR_5:iter:23» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_expl_neq:headerTypeIR_5:iter:27» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:headerTypeIR_5:iter:28» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_expl_neq:headerTypeIR_5:iter:29» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:listTypeIR:iter:4» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_impl_neq:tupleTypeIR:iter:4» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_impl_neq:arrayTypeIR:iter:4» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_impl_neq:headerStackTypeIR:iter:4» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_impl_neq:structTypeIR:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Cast_impl_neq:structTypeIR:iter:6» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_impl_neq:headerTypeIR_2:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Cast_impl_neq:headerTypeIR_2:iter:6» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_impl_neq:sequenceTypeIR:iter:4» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_impl_neq:tupleTypeIR_2:iter:5» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_impl_neq:tupleTypeIR_2:iter:6» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:arrayTypeIR_2:iter:4» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_impl_neq:headerStackTypeIR_2:iter:4» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_impl_neq:structTypeIR_2:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Cast_impl_neq:structTypeIR_2:iter:7» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_impl_neq:structTypeIR_2:iter:8» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:headerTypeIR_3:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Cast_impl_neq:headerTypeIR_3:iter:7» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_impl_neq:headerTypeIR_3:iter:8» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:structTypeIR_3:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «Cast_impl_neq:structTypeIR_3:pattern-iter:4» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «Cast_impl_neq:structTypeIR_3:iter:7» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:structTypeIR_3:iter:9» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_impl_neq:structTypeIR_3:iter:8» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_impl_neq:structTypeIR_3:iter:12» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:structTypeIR_3:iter:13» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_impl_neq:structTypeIR_3:iter:15» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_impl_neq:structTypeIR_3:iter:14» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_impl_neq:structTypeIR_3:iter:18» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:structTypeIR_3:iter:19» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_impl_neq:structTypeIR_3:iter:22» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_impl_neq:headerTypeIR_4:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «Cast_impl_neq:headerTypeIR_4:pattern-iter:4» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «Cast_impl_neq:headerTypeIR_4:iter:7» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:headerTypeIR_4:iter:9» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_impl_neq:headerTypeIR_4:iter:8» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_impl_neq:headerTypeIR_4:iter:12» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:headerTypeIR_4:iter:13» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_impl_neq:headerTypeIR_4:iter:15» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_impl_neq:headerTypeIR_4:iter:14» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_impl_neq:headerTypeIR_4:iter:18» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:headerTypeIR_4:iter:19» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_impl_neq:headerTypeIR_4:iter:22» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_impl_neq:structTypeIR_4:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «Cast_impl_neq:structTypeIR_4:pattern-iter:4» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «Cast_impl_neq:structTypeIR_4:iter:7» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:structTypeIR_4:iter:9» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_impl_neq:structTypeIR_4:iter:8» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_impl_neq:structTypeIR_4:iter:12» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:structTypeIR_4:iter:13» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_impl_neq:structTypeIR_4:iter:15» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_impl_neq:structTypeIR_4:iter:14» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_impl_neq:structTypeIR_4:iter:18» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:structTypeIR_4:iter:19» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_impl_neq:structTypeIR_4:iter:22» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_impl_neq:structTypeIR_4:iter:24» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_impl_neq:structTypeIR_4:iter:23» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_impl_neq:structTypeIR_4:iter:27» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:structTypeIR_4:iter:28» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_impl_neq:structTypeIR_4:iter:29» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:headerTypeIR_5:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «Cast_impl_neq:headerTypeIR_5:pattern-iter:4» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «Cast_impl_neq:headerTypeIR_5:iter:7» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:headerTypeIR_5:iter:9» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_impl_neq:headerTypeIR_5:iter:8» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_impl_neq:headerTypeIR_5:iter:12» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:headerTypeIR_5:iter:13» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_impl_neq:headerTypeIR_5:iter:15» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_impl_neq:headerTypeIR_5:iter:14» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_impl_neq:headerTypeIR_5:iter:18» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:headerTypeIR_5:iter:19» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_impl_neq:headerTypeIR_5:iter:22» (input0 : (_root_.List castResult)) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «Cast_impl_neq:headerTypeIR_5:iter:24» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Cast_impl_neq:headerTypeIR_5:iter:23» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option typeIR))
  | «Cast_impl_neq:headerTypeIR_5:iter:27» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:headerTypeIR_5:iter:28» (input0 : (_root_.List (_root_.Option typeIR))) : SpecTecCall (_root_.List typeIR)
  | «Cast_impl_neq:headerTypeIR_5:iter:29» (input0 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Expr_ok:non-default:iter:4» (input0 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List typeIR)
  | «Expr_ok:non-default:iter:6» (input0 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List ctk)
  | «Expr_ok:default:iter:5» (input0 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List typeIR)
  | «Expr_ok:default:iter:7» (input0 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List ctk)
  | «Expr_ok:multiple-non-default:pattern-iter:3» (input0 : (_root_.List namedExpression)) : SpecTecCall ((_root_.List expression) × (_root_.List name))
  | «Expr_ok:multiple-non-default:iter:5» (input0 : (_root_.List name)) : SpecTecCall (_root_.List nameIR)
  | «Expr_ok:multiple-non-default:iter:9» (input0 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List typeIR)
  | «Expr_ok:multiple-non-default:iter:11» (input0 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List ctk)
  | «Expr_ok:multiple-non-default:iter:13» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldTypeIR)
  | «Expr_ok:multiple-non-default:iter:16» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List namedExpressionIR)
  | «Expr_ok:multiple-default:pattern-iter:3» (input0 : (_root_.List namedExpression)) : SpecTecCall ((_root_.List expression) × (_root_.List name))
  | «Expr_ok:multiple-default:iter:5» (input0 : (_root_.List name)) : SpecTecCall (_root_.List nameIR)
  | «Expr_ok:multiple-default:iter:9» (input0 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List typeIR)
  | «Expr_ok:multiple-default:iter:11» (input0 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List ctk)
  | «Expr_ok:multiple-default:iter:13» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldTypeIR)
  | «Expr_ok:multiple-default:iter:16» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List namedExpressionIR)
  | «Expr_ok:serenum:pattern-iter:8» (input0 : (_root_.List valueFieldIR)) : SpecTecCall ((_root_.List value) × (_root_.List nameIR))
  | «Expr_ok:struct:pattern-iter:6» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Expr_ok:struct:iter:9» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (_root_.String × typeIR))
  | «Expr_ok:header:pattern-iter:6» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Expr_ok:header:iter:9» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (_root_.String × typeIR))
  | «Expr_ok:header-union:pattern-iter:6» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Expr_ok:header-union:iter:9» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (_root_.String × typeIR))
  | «Expr_ok:non-typeArgumentList-static_assert:iter:2» (input0 : (_root_.List typeId)) : SpecTecCall (_root_.List typeIR)
  | «Expr_ok:non-typeArgumentList:iter:2» (input0 : (_root_.List typeId)) : SpecTecCall (_root_.List typeIR)
  | «Expr_ok:typeArgumentList:iter:2» (input0 : (_root_.List typeId)) : SpecTecCall (_root_.List typeIR)
  | «Expr_ok:prefixedTypeName:iter:3» (input0 : (_root_.List typeId)) : SpecTecCall (_root_.List typeIR)
  | «Expr_ok:specializedType:iter:3» (input0 : (_root_.List typeId)) : SpecTecCall (_root_.List typeIR)
  | «Lvalue_ok:structTypeIR:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Lvalue_ok:structTypeIR:iter:5» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (_root_.String × typeIR))
  | «Lvalue_ok:headerTypeIR:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Lvalue_ok:headerTypeIR:iter:5» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (_root_.String × typeIR))
  | «Lvalue_ok:headerUnionTypeIR:pattern-iter:2» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Lvalue_ok:headerUnionTypeIR:iter:5» (input0 : (_root_.List nameIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List (_root_.String × typeIR))
  | «Stmt_ok:callStatement-no-typeArgumentList-static_assert:iter:1» (input0 : (_root_.List typeId)) : SpecTecCall (_root_.List typeIR)
  | «Stmt_ok:callStatement-no-typeArgumentList:iter:1» (input0 : (_root_.List typeId)) : SpecTecCall (_root_.List typeIR)
  | «Stmt_ok:callStatement-typeArgumentList:iter:1» (input0 : (_root_.List typeId)) : SpecTecCall (_root_.List typeIR)
  | «ParserSelect_ok:rule:iter:4» (input0 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List typeIR)
  | «ParserStateList_ok:rule:iter:1» (input0 : (_root_.List parserState)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List parserBlockElementStatementList) × ((_root_.List transitionStatement) × (_root_.List name))))
  | «ParserStateList_ok:rule:iter:2» (input0 : (_root_.List name)) : SpecTecCall (_root_.List nameIR)
  | «TableDefaultAction_ok:prefixedNonTypeName-argumentList:iter:4» (input0 : (_root_.List argumentIR)) (input1 : (_root_.List argumentIR)) : SpecTecCall _root_.Unit
  | «TableEntry_action_ok:prefixedNonTypeName-argumentList:iter:2» (input0 : (_root_.List argumentIR)) (input1 : (_root_.List argumentIR)) : SpecTecCall _root_.Unit
  | «TableType_ok:rule:pattern-iter:1» (input0 : (_root_.List matchAction)) : SpecTecCall ((_root_.List argumentListIR) × ((_root_.List (_root_.List parameterIR)) × (_root_.List prefixedNameIR)))
  | «TableType_ok:rule:iter:5» (input0 : typeId) (input1 : (_root_.List nameIR)) : SpecTecCall (_root_.List value)
  | «TableType_ok:rule:iter:7» (input0 : typeId) (input1 : (_root_.List nameIR)) : SpecTecCall (_root_.List _root_.String)
  | «Decl_ok:errorDeclaration:iter:2» (input0 : (_root_.List name)) : SpecTecCall (_root_.List nameIR)
  | «Decl_ok:errorDeclaration:iter:5» (input0 : (_root_.List nameIR)) : SpecTecCall (_root_.List nameIR)
  | «Decl_ok:errorDeclaration:iter:6» (input0 : (_root_.List nameIR)) : SpecTecCall (_root_.List value)
  | «Decl_ok:errorDeclaration:iter:7» (input0 : (_root_.List value)) : SpecTecCall (_root_.List varTypeIR)
  | «Decl_ok:matchKindDeclaration:iter:2» (input0 : (_root_.List name)) : SpecTecCall (_root_.List nameIR)
  | «Decl_ok:matchKindDeclaration:iter:5» (input0 : (_root_.List nameIR)) : SpecTecCall (_root_.List value)
  | «Decl_ok:matchKindDeclaration:iter:6» (input0 : (_root_.List value)) : SpecTecCall (_root_.List varTypeIR)
  | «Decl_ok:externObjectDeclaration:iter:9» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecCall (_root_.List (pair callTargetId externMethodTypeDefIR))
  | «Decl_ok:enumTypeDeclaration-non-serializable:iter:3» (input0 : (_root_.List name)) : SpecTecCall (_root_.List nameIR)
  | «Decl_ok:enumTypeDeclaration-non-serializable:iter:7» (input0 : nameIR) (input1 : (_root_.List nameIR)) : SpecTecCall (_root_.List id)
  | «Decl_ok:enumTypeDeclaration-non-serializable:iter:8» (input0 : nameIR) (input1 : (_root_.List nameIR)) : SpecTecCall (_root_.List value)
  | «Decl_ok:enumTypeDeclaration-serializable:iter:3» (input0 : (_root_.List namedValueIR)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «Decl_ok:enumTypeDeclaration-serializable:iter:4» (input0 : nameIR) (input1 : (_root_.List nameIR)) : SpecTecCall (_root_.List id)
  | «Decl_ok:enumTypeDeclaration-serializable:iter:5» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List valueFieldIR)
  | «Decl_ok:structTypeDeclaration:pattern-iter:2» (input0 : (_root_.List typeField)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List name) × (_root_.List type)))
  | «Decl_ok:structTypeDeclaration:iter:5» (input0 : (_root_.List (_root_.List typeId))) : SpecTecCall _root_.Unit
  | «Decl_ok:structTypeDeclaration:iter:7» (input0 : (_root_.List name)) : SpecTecCall (_root_.List nameIR)
  | «Decl_ok:structTypeDeclaration:iter:9» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldTypeIR)
  | «Decl_ok:structTypeDeclaration:iter:13» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List typeFieldIR)
  | «Decl_ok:headerTypeDeclaration:pattern-iter:2» (input0 : (_root_.List typeField)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List name) × (_root_.List type)))
  | «Decl_ok:headerTypeDeclaration:iter:5» (input0 : (_root_.List (_root_.List typeId))) : SpecTecCall _root_.Unit
  | «Decl_ok:headerTypeDeclaration:iter:7» (input0 : (_root_.List name)) : SpecTecCall (_root_.List nameIR)
  | «Decl_ok:headerTypeDeclaration:iter:9» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldTypeIR)
  | «Decl_ok:headerTypeDeclaration:iter:13» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List typeFieldIR)
  | «Decl_ok:headerUnionTypeDeclaration:pattern-iter:2» (input0 : (_root_.List typeField)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List name) × (_root_.List type)))
  | «Decl_ok:headerUnionTypeDeclaration:iter:5» (input0 : (_root_.List (_root_.List typeId))) : SpecTecCall _root_.Unit
  | «Decl_ok:headerUnionTypeDeclaration:iter:7» (input0 : (_root_.List name)) : SpecTecCall (_root_.List nameIR)
  | «Decl_ok:headerUnionTypeDeclaration:iter:9» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldTypeIR)
  | «Decl_ok:headerUnionTypeDeclaration:iter:13» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List typeFieldIR)
  | «Decl_ok:packageTypeDeclaration:iter:3» (input0 : (_root_.List constructorParameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))
  | «CallableType_ok:externMethodTypeIR:pattern-iter:3» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : SpecTecCall ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))
  | «CallableType_ok:externMethodTypeIR:iter:6» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecCall (_root_.List (pair callTargetId externMethodTypeDefIR))
  | «CallableType_ok:parserApplyMethodTypeIR:iter:3» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))
  | «CallableType_ok:controlApplyMethodTypeIR:iter:3» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))
  | «$chain_casts'» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecCall (typeIR × (_root_.List typeIR))
  | «$chain_casts:case_2:iter:0» (input0 : (_root_.List (_root_.List typeIR))) (input1 : (_root_.List typeIR)) : SpecTecCall ((_root_.List (_root_.List typeIR)) × (_root_.List typeIR))
  | «$chain_casts» (input0 : (_root_.List typeIR)) (input1 : (_root_.List (_root_.List typeIR))) : SpecTecCall (_root_.List (_root_.List typeIR))
  | «$chain_casts_sequenceTypeIR:case_1:iter:1» (input0 : (_root_.List (_root_.List typeIR))) : SpecTecCall (_root_.List typeIR)
  | «$chain_casts_sequenceTypeIR» (input0 : (_root_.List typeIR)) (input1 : (_root_.List (_root_.List typeIR))) (input2 : typeIR) : SpecTecCall (_root_.List typeIR)
  | «$chain_casts_sequenceTypeIR_default:case_1:iter:1» (input0 : (_root_.List (_root_.List typeIR))) : SpecTecCall (_root_.List typeIR)
  | «$chain_casts_sequenceTypeIR_default» (input0 : (_root_.List typeIR)) (input1 : (_root_.List (_root_.List typeIR))) (input2 : typeIR) : SpecTecCall (_root_.List typeIR)
  | «$chain_casts_recordTypeIR:case_1:pattern-iter:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «$chain_casts_recordTypeIR:case_1:iter:3» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List (_root_.List typeIR))) : SpecTecCall _root_.Unit
  | «$chain_casts_recordTypeIR:case_1:iter:5» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldTypeIR)
  | «$chain_casts_recordTypeIR:case_1:iter:4» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List (_root_.List typeIR))) : SpecTecCall (_root_.List typeIR)
  | «$chain_casts_recordTypeIR» (input0 : (_root_.List fieldTypeIR)) (input1 : (_root_.List (_root_.List typeIR))) (input2 : typeIR) : SpecTecCall (_root_.List typeIR)
  | «$chain_casts_recordTypeIR_default:case_1:pattern-iter:0» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × (_root_.List typeIR)))
  | «$chain_casts_recordTypeIR_default:case_1:iter:3» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List (_root_.List typeIR))) : SpecTecCall _root_.Unit
  | «$chain_casts_recordTypeIR_default:case_1:iter:5» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldTypeIR)
  | «$chain_casts_recordTypeIR_default:case_1:iter:4» (input0 : (_root_.List annotationList)) (input1 : (_root_.List id)) (input2 : (_root_.List (_root_.List typeIR))) : SpecTecCall (_root_.List typeIR)
  | «$chain_casts_recordTypeIR_default» (input0 : (_root_.List fieldTypeIR)) (input1 : (_root_.List (_root_.List typeIR))) (input2 : typeIR) : SpecTecCall (_root_.List typeIR)
  | «$apply_cast» (input0 : typedExpressionIR) (input1 : (_root_.List typeIR)) : SpecTecCall typedExpressionIR
  | «$compat_lnot» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_bnot» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_uplusminus» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_plusminusmult» (input0 : typeIR) (input1 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_satplusminus» (input0 : typeIR) (input1 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_divmod» (input0 : typeIR) (input1 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_shift» (input0 : typeIR) (input1 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_compare» (input0 : typeIR) (input1 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_bitwise» (input0 : typeIR) (input1 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_concat» (input0 : typeIR) (input1 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_logical» (input0 : typeIR) (input1 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_array_index» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_bitslice_base» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_bitslice_range_index» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_bitslice_offset_index» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_bitslice_offset_width» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$is_concrete_extern_object':case_2:pattern-iter:1» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : SpecTecCall ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))
  | «$compat_range» (input0 : typeIR) (input1 : typeIR) : SpecTecCall _root_.Bool
  | «$check_switchLabelIR_default» (input0 : (_root_.List switchLabelIR)) : SpecTecCall _root_.Bool
  | «$compat_switch» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «InstDecl_non_objectInitializer_ok:rule:iter:1» (input0 : (_root_.List typeId)) : SpecTecCall (_root_.List typeIR)
  | «$subst_externMethodTypeDefEnv:case_2:pattern-iter:0» (input0 : (_root_.List (pair callTargetId externMethodTypeDefIR))) : SpecTecCall ((_root_.List callableId) × (_root_.List externMethodTypeDefIR))
  | «$subst_externMethodTypeDefEnv:case_2:iter:4» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecCall (_root_.List (pair callTargetId externMethodTypeDefIR))
  | «InstDecl_objectInitializer_ok:rule:iter:1» (input0 : (_root_.List typeId)) : SpecTecCall (_root_.List typeIR)
  | «$constructorTypeDef_of_externConstructorPrototypeIR» (input0 : typeParameterListIR) (input1 : typeIR) (input2 : externConstructorPrototypeIR) : SpecTecCall constructorTypeDefIR
  | «Decl_ok:externObjectDeclaration:iter:17» (input0 : (_root_.List typeId)) (input1 : typeIR) (input2 : (_root_.List externConstructorPrototypeIR)) : SpecTecCall (_root_.List constructorTypeDefIR)
  | «$compat_mask» (input0 : typeIR) (input1 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_table_exact_optional_key» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_table_lpm_ternary_range_key» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$compat_table_key» (input0 : nameIR) (input1 : typeIR) : SpecTecCall _root_.Bool
  | «$insert_NoAction_tablePropertyIR:case_2:iter:1» (input0 : (_root_.List tableActionIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List parameterListIR) × ((_root_.List parameterListIR) × (_root_.List tableActionReferenceIR))))
  | «$insert_NoAction_tablePropertyIR:case_3:iter:1» (input0 : (_root_.List tableActionIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List parameterListIR) × ((_root_.List parameterListIR) × (_root_.List tableActionReferenceIR))))
  | «$empty_strictness:case_1:iter:0» (input0 : (_root_.List typeId)) : SpecTecCall (_root_.List (pair _root_.String strict))
  | «$empty_strictness» (input0 : (_root_.List typeId)) : SpecTecCall strictness
  | «$empty_constraint:case_1:iter:0» (input0 : (_root_.List typeId)) : SpecTecCall (_root_.List (pair _root_.String infer))
  | «$empty_constraint» (input0 : (_root_.List typeId)) : SpecTecCall constraint
  | «$resolve_inference:case_1:pattern-iter:0» (input0 : (_root_.List (pair _root_.String typeIR))) : SpecTecCall ((_root_.List typeIR) × (_root_.List typeId))
  | «$resolve_inference:case_1:iter:4» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeId)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «$gen_constraint_pair:case_13:iter:2» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR)))))
  | «$gen_constraint_pair:case_13:iter:3» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR)))))
  | «$gen_constraint_pair:case_13:iter:4» (input0 : (_root_.List direction)) (input1 : (_root_.List direction)) : SpecTecCall _root_.Unit
  | «$gen_constraint_pair:case_14:iter:2» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR)))))
  | «$gen_constraint_pair:case_14:iter:3» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × ((_root_.List direction) × (_root_.List typeIR)))))
  | «$gen_constraint_pair:case_14:iter:4» (input0 : (_root_.List direction)) (input1 : (_root_.List direction)) : SpecTecCall _root_.Unit
  | «$resolve_constraint:case_2:pattern-iter:0» (input0 : (_root_.List (pair _root_.String infer))) : SpecTecCall ((_root_.List infer) × (_root_.List typeId))
  | «$resolve_constraint:case_2:iter:2» (input0 : (_root_.List infer)) (input1 : (_root_.List typeId)) : SpecTecCall (_root_.List (pair _root_.String infer))
  | «$resolve_constraint:case_2:pattern-iter:5» (input0 : (_root_.List (pair _root_.String typeIR))) : SpecTecCall ((_root_.List typeIR) × (_root_.List typeId))
  | «$resolve_constraint:case_2:iter:7» (input0 : (_root_.List typeId)) (input1 : (_root_.List typeId)) : SpecTecCall _root_.Unit
  | «$resolve_constraint:case_2:iter:8» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeId)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «$resolve_constraint:case_3:pattern-iter:0» (input0 : (_root_.List (pair _root_.String infer))) : SpecTecCall ((_root_.List infer) × (_root_.List typeId))
  | «$resolve_constraint:case_3:iter:3» (input0 : (_root_.List infer)) (input1 : (_root_.List typeId)) : SpecTecCall (_root_.List (pair _root_.String infer))
  | «$resolve_constraint:case_3:pattern-iter:6» (input0 : (_root_.List (pair _root_.String typeIR))) : SpecTecCall ((_root_.List typeIR) × (_root_.List typeId))
  | «$resolve_constraint:case_3:iter:8» (input0 : (_root_.List typeId)) (input1 : (_root_.List typeId)) : SpecTecCall _root_.Unit
  | «$resolve_constraint:case_3:iter:9» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeId)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «$callableId_IR:case_1:iter:0» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))
  | «$callableId_IR» (input0 : nameIR) (input1 : parameterListIR) : SpecTecCall callableId
  | «$parameterListIR_of_actionDef» (input0 : actionDef) : SpecTecCall (_root_.List parameterIR)
  | «$parameterListIR_of_definedFunctionDef» (input0 : definedFunctionDef) : SpecTecCall (_root_.List parameterIR)
  | «$parameterListIR_of_externFunctionDef» (input0 : externFunctionDef) : SpecTecCall (_root_.List parameterIR)
  | «$parameterListIR_of_tableApplyMethodDef» (input0 : tableApplyMethodDef) : SpecTecCall (_root_.List parameterIR)
  | «$init_objectState» (input0 : nameIR) (input1 : (_root_.List typeIR)) (input2 : (_root_.List id)) (input3 : (_root_.List value)) : SpecTecCall objectState
  | «$parameterListIR_of_controlApplyMethodDef» (input0 : controlApplyMethodDef) : SpecTecCall (_root_.List parameterIR)
  | «$empty_frame» : SpecTecCall frame
  | «$parameterListIR_of_parserApplyMethodDef» (input0 : parserApplyMethodDef) : SpecTecCall (_root_.List parameterIR)
  | «$empty_stateEnv» : SpecTecCall stateEnv
  | «$empty_callableDefEnv» : SpecTecCall callableDefEnv
  | «$empty_constructorDefEnv» : SpecTecCall constructorDefEnv
  | «$empty_store» : SpecTecCall store
  | «$add_store» (input0 : store) (input1 : objectId) (input2 : object) : SpecTecCall store
  | «$find_store» (input0 : store) (input1 : objectId) : SpecTecCall object
  | «$empty_instContext» : SpecTecCall instContext
  | «$enter_i» (input0 : instContext) : SpecTecCall instContext
  | «$exit_i» (input0 : instContext) : SpecTecCall instContext
  | «$enter_path_i» (input0 : instContext) (input1 : id) : SpecTecCall instContext
  | «$add_parserState_i» (input0 : instContext) (input1 : nameIR) (input2 : parserStateIR) : SpecTecCall instContext
  | «$add_callableDef_non_overload_i:case_1:pattern-iter:1» (input0 : (_root_.List callTargetId)) : SpecTecCall ((_root_.List (_root_.List id)) × (_root_.List id))
  | «$add_callableDef_non_overload_i:case_2:pattern-iter:1» (input0 : (_root_.List callTargetId)) : SpecTecCall ((_root_.List (_root_.List id)) × (_root_.List id))
  | «$add_constructorDef_i» (input0 : instContext) (input1 : callableId) (input2 : constructorDef) : SpecTecCall instContext
  | «$add_constructorDefs_i» (input0 : instContext) (input1 : (_root_.List callableId)) (input2 : (_root_.List constructorDef)) : SpecTecCall instContext
  | «Expr_inst:non-default_2:pattern-iter:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecCall ((_root_.List nameIR) × (_root_.List typedExpressionIR))
  | «Expr_inst:non-default_2:iter:3» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «Expr_inst:default_2:pattern-iter:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecCall ((_root_.List nameIR) × (_root_.List typedExpressionIR))
  | «Expr_inst:default_2:iter:3» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «Expr_inst:serenum:pattern-iter:5» (input0 : (_root_.List valueFieldIR)) : SpecTecCall ((_root_.List id) × (_root_.List value))
  | «Expr_inst:serenum:iter:7» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.String × value))
  | «Expr_inst:struct:pattern-iter:3» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List id) × (_root_.List value))
  | «Expr_inst:struct:iter:5» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.String × value))
  | «Expr_inst:header:pattern-iter:3» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List id) × (_root_.List value))
  | «Expr_inst:header:iter:5» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.String × value))
  | «Expr_inst:header-union:pattern-iter:3» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List id) × (_root_.List value))
  | «Expr_inst:header-union:iter:5» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.String × value))
  | «Decl_inst:errorDeclarationIR:iter:1» (input0 : (_root_.List nameIR)) : SpecTecCall (_root_.List nameIR)
  | «Decl_inst:errorDeclarationIR:iter:3» (input0 : (_root_.List nameIR)) : SpecTecCall (_root_.List value)
  | «Decl_inst:matchKindDeclarationIR:iter:1» (input0 : (_root_.List nameIR)) : SpecTecCall (_root_.List value)
  | «Decl_inst:non-constructor:iter:5» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecCall (_root_.List (pair callTargetId externMethodTypeDefIR))
  | «Decl_inst:constructor:iter:5» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecCall (_root_.List (pair callTargetId externMethodTypeDefIR))
  | «Decl_inst:enumTypeDeclarationIR-non-serializable:iter:1» (input0 : nameIR) (input1 : (_root_.List nameIR)) : SpecTecCall (_root_.List nameIR)
  | «Decl_inst:enumTypeDeclarationIR-non-serializable:iter:2» (input0 : nameIR) (input1 : (_root_.List nameIR)) : SpecTecCall (_root_.List value)
  | «Decl_inst:enumTypeDeclarationIR-serializable:pattern-iter:1» (input0 : (_root_.List namedValueIR)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «Decl_inst:enumTypeDeclarationIR-serializable:iter:3» (input0 : nameIR) (input1 : (_root_.List nameIR)) : SpecTecCall (_root_.List nameIR)
  | «Decl_inst:enumTypeDeclarationIR-serializable:iter:4» (input0 : nameIR) (input1 : (_root_.List nameIR)) (input2 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «Decl_inst:enumTypeDeclarationIR-serializable:iter:6» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List valueFieldIR)
  | «Decl_inst:structTypeDeclarationIR:iter:1» (input0 : (_root_.List typeFieldIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Decl_inst:structTypeDeclarationIR:iter:2» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldTypeIR)
  | «Decl_inst:headerTypeDeclarationIR:iter:1» (input0 : (_root_.List typeFieldIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Decl_inst:headerTypeDeclarationIR:iter:2» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldTypeIR)
  | «Decl_inst:headerUnionTypeDeclarationIR:iter:1» (input0 : (_root_.List typeFieldIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «Decl_inst:headerUnionTypeDeclarationIR:iter:2» (input0 : (_root_.List annotationList)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldTypeIR)
  | «Decl_inst:packageTypeDeclarationIR:iter:1» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))
  | «Constructor_call:externConstructorDef:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Constructor_call:externConstructorDef:iter:5» (input0 : (_root_.List constructorParameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))
  | «Constructor_call:externConstructorDef:pattern-iter:6» (input0 : (_root_.List (pair callTargetId callableDef))) : SpecTecCall ((_root_.List callableId) × (_root_.List callableDef))
  | «Constructor_call:externConstructorDef:iter:9» (input0 : (_root_.List callableDef)) : SpecTecCall (_root_.List externMethodDef)
  | «Constructor_call:externConstructorDef:iter:11» (input0 : (_root_.List constructorParameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))
  | «Constructor_call:externConstructorDef:iter:12» (input0 : (_root_.List id)) (input1 : (_root_.List id)) : SpecTecCall _root_.Unit
  | «Constructor_call:externConstructorDef:iter:13» (input0 : instContext) (input1 : (_root_.List id)) : SpecTecCall (_root_.List (_root_.Option value))
  | «Constructor_call:externConstructorDef:iter:15» (input0 : (_root_.List (_root_.Option value))) : SpecTecCall _root_.Unit
  | «Constructor_call:externConstructorDef:iter:16» (input0 : (_root_.List (_root_.Option value))) : SpecTecCall (_root_.List value)
  | «Constructor_call:externConstructorDef:iter:18» (input0 : (_root_.List callableId)) (input1 : (_root_.List externMethodDef)) : SpecTecCall (_root_.List (pair callTargetId externMethodDef))
  | «Constructor_call:parserConstructorDef:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Constructor_call:parserConstructorDef:iter:5» (input0 : (_root_.List constructorParameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))
  | «Constructor_call:controlConstructorDef:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Constructor_call:controlConstructorDef:iter:5» (input0 : (_root_.List constructorParameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))
  | «Constructor_call:controlConstructorDef:pattern-iter:6» (input0 : (_root_.List (pair callTargetId callableDef))) : SpecTecCall ((_root_.List callableId) × (_root_.List callableDef))
  | «Constructor_call:controlConstructorDef:iter:9» (input0 : (_root_.List callableDef)) : SpecTecCall (_root_.List actionDef)
  | «Constructor_call:controlConstructorDef:iter:11» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : SpecTecCall (_root_.List (pair callTargetId actionDef))
  | «Constructor_call:controlConstructorDef:iter:13» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : SpecTecCall (_root_.List (pair callTargetId actionDef))
  | «Constructor_call:packageConstructorDef:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Constructor_call:packageConstructorDef:iter:5» (input0 : (_root_.List constructorParameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List id)))))
  | «$merge_frames:case_1:pattern-iter:0» (input0 : (_root_.List (pair _root_.String value))) : SpecTecCall ((_root_.List id) × (_root_.List value))
  | «$merge_frames» (input0 : frame) (input1 : frame) : SpecTecCall frame
  | «$merge_externMethodDefEnvs:case_2:pattern-iter:0» (input0 : (_root_.List (pair callTargetId callableDef))) : SpecTecCall ((_root_.List callableDef) × (_root_.List callableId))
  | «$merge_externMethodDefEnvs:case_2:iter:4» (input0 : (_root_.List callableDef)) (input1 : (_root_.List callableId)) : SpecTecCall (_root_.List (pair callTargetId callableDef))
  | «$callableId_of_externConstructorPrototypeIR» (input0 : externConstructorPrototypeIR) : SpecTecCall callableId
  | «Decl_inst:constructor:iter:8» (input0 : (_root_.List externConstructorPrototypeIR)) : SpecTecCall (_root_.List callableId)
  | «$constructor_of_externConstructorPrototypeIR» (input0 : typeParameterListIR) (input1 : externMethodPrototypeListIR) (input2 : externConstructorPrototypeIR) : SpecTecCall constructorDef
  | «Decl_inst:constructor:iter:10» (input0 : typeParameterListIR) (input1 : (_root_.List externMethodPrototypeIR)) (input2 : (_root_.List externConstructorPrototypeIR)) : SpecTecCall (_root_.List constructorDef)
  | «$enter_e» (input0 : evalContext) : SpecTecCall evalContext
  | «$exit_e» (input0 : evalContext) : SpecTecCall evalContext
  | «$find_parserState_e» (input0 : evalContext) (input1 : nameIR) : SpecTecCall (_root_.Option parserStateIR)
  | «$init_archState» : SpecTecCall archState
  | «$add_object_e» (input0 : arch) (input1 : objectId) (input2 : object) : SpecTecCall arch
  | «$find_archState_e» (input0 : arch) : SpecTecCall archState
  | «$find_object_e» (input0 : arch) (input1 : objectId) : SpecTecCall (_root_.Option object)
  | «$find_object_qualified_e» (input0 : arch) (input1 : objectId) : SpecTecCall (_root_.Option object)
  | «$find_object_unqualified_e:case_1:pattern-iter:0» (input0 : (_root_.List (pair (_root_.List _root_.String) object))) : SpecTecCall ((_root_.List object) × (_root_.List objectId))
  | «$find_object_unqualified_e:case_1:iter:2» (input0 : id) (input1 : (_root_.List object)) (input2 : (_root_.List objectId)) : SpecTecCall (_root_.List (_root_.Option object))
  | «$find_object_unqualified_e:case_1:iter:5» (input0 : (_root_.List (_root_.Option object))) : SpecTecCall (_root_.List _root_.Bool)
  | «$find_object_unqualified_e» (input0 : arch) (input1 : id) : SpecTecCall (_root_.Option object)
  | «$update_archState_e» (input0 : arch) (input1 : archState) : SpecTecCall arch
  | «$update_object_qualified_e» (input0 : arch) (input1 : objectId) (input2 : object) : SpecTecCall arch
  | «$update_object_unqualified_e:case_1:pattern-iter:0» (input0 : (_root_.List (pair (_root_.List _root_.String) object))) : SpecTecCall ((_root_.List object) × (_root_.List objectId))
  | «$update_object_unqualified_e:case_1:iter:2» (input0 : id) (input1 : (_root_.List objectId)) : SpecTecCall (_root_.List (_root_.Option objectId))
  | «$update_object_unqualified_e:case_1:iter:5» (input0 : (_root_.List (_root_.Option objectId))) : SpecTecCall (_root_.List _root_.Bool)
  | «$update_object_unqualified_e» (input0 : arch) (input1 : id) (input2 : object) : SpecTecCall arch
  | «Expr_eval:non-default-abort_2:pattern-iter:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecCall ((_root_.List nameIR) × (_root_.List typedExpressionIR))
  | «Expr_eval:non-default-cont_2:pattern-iter:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecCall ((_root_.List nameIR) × (_root_.List typedExpressionIR))
  | «Expr_eval:non-default-cont_2:iter:4» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «Expr_eval:default-abort_2:pattern-iter:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecCall ((_root_.List nameIR) × (_root_.List typedExpressionIR))
  | «Expr_eval:default-cont_2:pattern-iter:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecCall ((_root_.List nameIR) × (_root_.List typedExpressionIR))
  | «Expr_eval:default-cont_2:iter:4» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List fieldValue)
  | «Expr_eval:serenum:pattern-iter:5» (input0 : (_root_.List valueFieldIR)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «Expr_eval:serenum:iter:7» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.String × value))
  | «Expr_eval:struct:pattern-iter:4» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List id) × (_root_.List value))
  | «Expr_eval:struct:iter:6» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.String × value))
  | «Expr_eval:header:pattern-iter:4» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List id) × (_root_.List value))
  | «Expr_eval:header:iter:6» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.String × value))
  | «Expr_eval:headerunion:pattern-iter:4» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List id) × (_root_.List value))
  | «Expr_eval:headerunion:iter:6» (input0 : (_root_.List id)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.String × value))
  | «Lvalue_read:struct:pattern-iter:1» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «Lvalue_read:struct:iter:3» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.String × value))
  | «Lvalue_read:header:pattern-iter:1» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «Lvalue_read:header:iter:3» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.String × value))
  | «Lvalue_read:header-union:pattern-iter:1» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «Lvalue_read:header-union:iter:3» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.String × value))
  | «Lvalue_write:header-union-keep-valid-header:pattern-iter:1» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «Lvalue_write:header-union-keep-valid-header:iter:3» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.String × value))
  | «Lvalue_write:header-union-replace-valid-header:pattern-iter:1» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «Lvalue_write:header-union-replace-valid-header:iter:3» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.String × value))
  | «Copy_in_default:rule:iter:0» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List typeIR) × ((_root_.List nameIR) × (_root_.List parameterInitializerOptIR)))))
  | «Copy_in_default:rule:iter:1» (input0 : (_root_.List parameterInitializerOptIR)) : SpecTecCall _root_.Unit
  | «Copy_in_default:rule:iter:2» (input0 : (_root_.List parameterInitializerOptIR)) : SpecTecCall (_root_.List parameterInitializerIR)
  | «Copy_in_default:rule:iter:4» (input0 : (_root_.List parameterInitializerIR)) : SpecTecCall (_root_.List value)
  | «Copy_in_default:rule:iter:6» (input0 : (_root_.List nameIR)) : SpecTecCall (_root_.List prefixedNameIR)
  | «Call_eval:definedFunctionCallee-copyin-abort:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Call_eval:definedFunctionCallee-cont:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Call_eval:externFunctionCallee-copyin-abort:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Call_eval:externFunctionCallee-copyin-cont-call-reject:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Call_eval:externFunctionCallee-copyin-cont-call-reject:iter:6» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR)))))
  | «Call_eval:externFunctionCallee-copyin-cont-call-non-reject:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Call_eval:externFunctionCallee-copyin-cont-call-non-reject:iter:6» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR)))))
  | «Call_eval:builtinIsValidMethodCallee-header-union:iter:2» (input0 : (_root_.List fieldValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «Call_eval:copyin-abort-initializer:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Call_eval:copyin-cont-initializer:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Call_eval:copyin-abort:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Call_eval:copyin-cont-non-abstract-reject:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Call_eval:copyin-cont-non-abstract-reject:iter:6» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR)))))
  | «Call_eval:copyin-cont-non-abstract-non-reject:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List (pair _root_.String typeIR))
  | «Call_eval:copyin-cont-non-abstract-non-reject:iter:6» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR)))))
  | «Call_eval:controlApplyMethodCallee-copyin-exit:pattern-iter:2» (input0 : (_root_.List (pair callTargetId actionDef))) : SpecTecCall ((_root_.List actionDef) × (_root_.List callableId))
  | «Call_eval:controlApplyMethodCallee-localDecl-exit:pattern-iter:2» (input0 : (_root_.List (pair callTargetId actionDef))) : SpecTecCall ((_root_.List actionDef) × (_root_.List callableId))
  | «Call_eval:controlApplyMethodCallee-controlBodyIR-exit:pattern-iter:2» (input0 : (_root_.List (pair callTargetId actionDef))) : SpecTecCall ((_root_.List actionDef) × (_root_.List callableId))
  | «Call_eval:controlApplyMethodCallee-cont:pattern-iter:2» (input0 : (_root_.List (pair callTargetId actionDef))) : SpecTecCall ((_root_.List actionDef) × (_root_.List callableId))
  | ExternFunctionCall_eval (input0 : evalContext) (input1 : arch) (input2 : nameIR) (input3 : (_root_.List nameIR)) : SpecTecCall (evalContext × (arch × callResult))
  | ExternMethodCall_eval (input0 : evalContext) (input1 : arch) (input2 : objectId) (input3 : nameIR) (input4 : (_root_.List nameIR)) : SpecTecCall (evalContext × (arch × callResult))
  | «TableMatch_eval:no-match:iter:2» (input0 : (_root_.List tableKeyValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «TableMatch_eval:match:iter:2» (input0 : (_root_.List tableKeyValue)) : SpecTecCall ((_root_.List nameIR) × (_root_.List value))
  | «$select_action:case_3:iter:0» (input0 : (_root_.List tableMatch)) : SpecTecCall ((_root_.List (_root_.Option _root_.Nat)) × (_root_.List tableActionReferenceIR))
  | «$select_action:case_3:iter:1» (input0 : (_root_.List (_root_.Option _root_.Nat))) : SpecTecCall _root_.Unit
  | «$select_action:case_3:iter:2» (input0 : (_root_.List (_root_.Option _root_.Nat))) : SpecTecCall (_root_.List _root_.Nat)
  | «$select_action:case_3:iter:3» (input0 : (_root_.List _root_.Nat)) (input1 : (_root_.List tableActionReferenceIR)) : SpecTecCall (_root_.List (_root_.Nat × tableActionReferenceIR))
  | «$select_action:case_3:pattern-iter:5» (input0 : (_root_.List (_root_.Nat × tableActionReferenceIR))) : SpecTecCall ((_root_.List _root_.Nat) × (_root_.List tableActionReferenceIR))
  | «$select_action:case_4:iter:0» (input0 : (_root_.List tableMatch)) : SpecTecCall ((_root_.List (_root_.Option _root_.Nat)) × (_root_.List tableActionReferenceIR))
  | «$select_action:case_4:iter:1» (input0 : (_root_.List (_root_.Option _root_.Nat))) : SpecTecCall _root_.Unit
  | «$select_action:case_4:iter:2» (input0 : (_root_.List (_root_.Option _root_.Nat))) : SpecTecCall (_root_.List _root_.Nat)
  | «$select_action:case_4:iter:3» (input0 : (_root_.List _root_.Nat)) (input1 : (_root_.List tableActionReferenceIR)) : SpecTecCall (_root_.List (_root_.Nat × tableActionReferenceIR))
  | «$select_action:case_4:pattern-iter:5» (input0 : (_root_.List (_root_.Nat × tableActionReferenceIR))) : SpecTecCall ((_root_.List _root_.Nat) × (_root_.List tableActionReferenceIR))
  | «$reverse_bytes_of_hex'» (input0 : _root_.String) : SpecTecCall _root_.String
  | «$reverse_bytes_of_hex» (input0 : _root_.String) : SpecTecCall _root_.String
  | «$tableObject_create_entry_priority» (input0 : tableEntryPriorityInterface) : SpecTecCall tableEntryPriorityOptIR
  | «$needs_priority_tableKeysPropertyIR:case_1:iter:0» (input0 : (_root_.List tableKeyIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List nameIR) × ((_root_.List typedExpressionIR) × (_root_.List nameIR))))
  | «$needs_priority_tableKeysPropertyIR:case_1:iter:1» (input0 : (_root_.List nameIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$needs_priority_tableKeysPropertyIR» (input0 : tableKeysPropertyIR) : SpecTecCall _root_.Bool
  | «$tableObject_create_entry_keys:case_2:pattern-iter:0» (input0 : (_root_.List (_root_.String × (_root_.String × typeIR)))) : SpecTecCall ((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$tableObject_create_entry_keys:case_2:iter:3» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List (_root_.String × (_root_.String × typeIR)))
  | «$interface_of_tableKeyIR» (input0 : tableKeyIR) : SpecTecCall (nameIR × (nameIR × typeIR))
  | «$key_interface_of_tableObject:case_1:iter:0» (input0 : (_root_.List tableKeyIR)) : SpecTecCall ((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$key_interface_of_tableObject:case_1:iter:2» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List (_root_.String × (_root_.String × typeIR)))
  | «$key_interface_of_tableObject» (input0 : tableObject) : SpecTecCall (_root_.List (nameIR × (nameIR × typeIR)))
  | «$tableObject_create_entry_keyset:case_1:iter:0» (input0 : (_root_.List tableKeyIR)) : SpecTecCall ((_root_.List nameIR) × ((_root_.List nameIR) × (_root_.List typeIR)))
  | «$tableObject_create_entry_keyset:case_1:iter:2» (input0 : (_root_.List tableKeyInterface)) : SpecTecCall ((_root_.List nameIR) × (_root_.List tableKeyValueInterface))
  | «$tableObject_create_entry_keyset:case_1:iter:3» (input0 : (_root_.List nameIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$tableObject_create_entry_keyset:case_1:iter:7» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List (_root_.String × (_root_.String × typeIR)))
  | «$alias_to_original_lookup_map:case_1:iter:0» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × ((_root_.List annotationList) × (_root_.List id)))))
  | «$alias_to_original_lookup_map:case_1:iter:7» (input0 : (_root_.List (_root_.Option nameIR))) : SpecTecCall (_root_.List (_root_.List nameIR))
  | «$alias_to_original_lookup_map:case_1:iter:6» (input0 : (_root_.List (_root_.List (_root_.Option nameIR)))) : SpecTecCall (_root_.List (_root_.List (_root_.List nameIR)))
  | «$alias_to_original_lookup_map:case_1:iter:9» (input0 : (_root_.List (_root_.List (_root_.List nameIR)))) : SpecTecCall (_root_.List (_root_.List nameIR))
  | «$alias_to_original_lookup_map:case_1:iter:10» (input0 : (_root_.List id)) (input1 : (_root_.List (_root_.List nameIR))) : SpecTecCall (_root_.List (_root_.String × (_root_.List _root_.String)))
  | «$alias_to_original_lookup_map:case_1:iter:12» (input0 : (_root_.List (_root_.List nameIR))) : SpecTecCall (_root_.List _root_.Bool)
  | «$alias_to_original_lookup_map:case_1:pattern-iter:15» (input0 : (_root_.List (_root_.String × (_root_.List _root_.String)))) : SpecTecCall ((_root_.List (_root_.List nameIR)) × (_root_.List nameIR))
  | «$alias_to_original_lookup_map:case_1:iter:17» (input0 : (_root_.List (_root_.List nameIR))) : SpecTecCall _root_.Unit
  | «$alias_to_original_lookup_map:case_1:iter:18» (input0 : (_root_.List (_root_.List nameIR))) : SpecTecCall (_root_.List _root_.String)
  | «$alias_to_original_lookup_map:case_1:iter:21» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecCall (_root_.List (pair _root_.String _root_.String))
  | «$alias_to_original_lookup_map:case_1:iter:23» (input0 : (_root_.List id)) : SpecTecCall (_root_.List (pair _root_.String _root_.String))
  | «$align_tableActionArgumentInterfaces:case_1:pattern-iter:0» (input0 : (_root_.List (_root_.String × _root_.Int))) : SpecTecCall ((_root_.List _root_.Int) × (_root_.List nameIR))
  | «$align_tableActionArgumentInterfaces:case_1:pattern-iter:3» (input0 : (_root_.List (pair _root_.String _root_.String))) : SpecTecCall ((_root_.List nameIR) × (_root_.List nameIR))
  | «$align_tableActionArgumentInterfaces:case_1:iter:6» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) : SpecTecCall (_root_.List (pair _root_.String _root_.String))
  | «$align_tableActionArgumentInterfaces:case_1:iter:5» (input0 : (_root_.List nameIR)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List nameIR)) : SpecTecCall (_root_.List (_root_.Option nameIR))
  | «$align_tableActionArgumentInterfaces:case_1:iter:9» (input0 : (_root_.List (_root_.Option nameIR))) : SpecTecCall _root_.Unit
  | «$align_tableActionArgumentInterfaces:case_1:iter:10» (input0 : (_root_.List (_root_.Option nameIR))) : SpecTecCall (_root_.List nameIR)
  | «$align_tableActionArgumentInterfaces:case_1:iter:11» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List parameterInitializerOptIR) × ((_root_.List typeIR) × (_root_.List nameIR)))))
  | «$align_tableActionArgumentInterfaces:case_1:iter:14» (input0 : (_root_.List _root_.Int)) (input1 : (_root_.List nameIR)) : SpecTecCall (_root_.List (pair _root_.String _root_.Int))
  | «$align_tableActionArgumentInterfaces':case_1:pattern-iter:0» (input0 : (_root_.List (pair _root_.String _root_.Int))) : SpecTecCall ((_root_.List _root_.Int) × (_root_.List id))
  | «$align_tableActionArgumentInterfaces':case_1:iter:2» (input0 : (_root_.List _root_.Int)) (input1 : (_root_.List id)) : SpecTecCall (_root_.List (pair _root_.String _root_.Int))
  | «$align_tableActionArgumentInterfaces':case_2:pattern-iter:0» (input0 : (_root_.List (pair _root_.String _root_.Int))) : SpecTecCall ((_root_.List _root_.Int) × (_root_.List id))
  | «$align_tableActionArgumentInterfaces':case_2:iter:2» (input0 : (_root_.List _root_.Int)) (input1 : (_root_.List id)) : SpecTecCall (_root_.List (pair _root_.String _root_.Int))
  | «$align_tableActionArgumentInterfaces'» (input0 : (map id _root_.Int)) (input1 : parameterIR) : SpecTecCall _root_.Int
  | «$align_tableActionArgumentInterfaces:case_1:iter:13» (input0 : (_root_.List _root_.Int)) (input1 : (_root_.List nameIR)) (input2 : (_root_.List parameterIR)) : SpecTecCall (_root_.List _root_.Int)
  | «$tableObject_create_entry_action:case_1:iter:2» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))
  | «$tableObject_create_entry_action:case_1:iter:3» (input0 : (_root_.List _root_.Int)) : SpecTecCall (_root_.List typedExpressionIR)
  | «$tableObject_create_entry_action:case_1:iter:6» (input0 : (_root_.List (_root_.Option typedExpressionIR))) : SpecTecCall _root_.Unit
  | «$tableObject_create_entry_action:case_1:iter:7» (input0 : (_root_.List (_root_.Option typedExpressionIR))) : SpecTecCall (_root_.List typedExpressionIR)
  | «$tableObject_create_entry_action:case_2:iter:3» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List direction) × ((_root_.List id) × ((_root_.List parameterInitializerOptIR) × (_root_.List typeIR)))))
  | «$tableObject_create_entry_action:case_2:iter:4» (input0 : (_root_.List _root_.Int)) : SpecTecCall (_root_.List typedExpressionIR)
  | «$tableObject_create_entry_action:case_2:iter:7» (input0 : (_root_.List (_root_.Option typedExpressionIR))) : SpecTecCall _root_.Unit
  | «$tableObject_create_entry_action:case_2:iter:8» (input0 : (_root_.List (_root_.Option typedExpressionIR))) : SpecTecCall (_root_.List typedExpressionIR)
  | «$V1Model_meta_fields_of_index:case_1:pattern-iter:4» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List typeIR) × (_root_.List nameIR)))
  | «$V1Model_meta_fields_of_index:case_1:pattern-iter:7» (input0 : (_root_.List fieldTypeIR)) : SpecTecCall ((_root_.List annotationList) × ((_root_.List typeIR) × (_root_.List nameIR)))
  | «Call_eval:controlApplyMethodCallee-copyin-exit:iter:4» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : SpecTecCall (_root_.List (pair callTargetId callableDef))
  | «Call_eval:controlApplyMethodCallee-localDecl-exit:iter:4» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : SpecTecCall (_root_.List (pair callTargetId callableDef))
  | «Call_eval:controlApplyMethodCallee-controlBodyIR-exit:iter:4» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : SpecTecCall (_root_.List (pair callTargetId callableDef))
  | «Call_eval:controlApplyMethodCallee-cont:iter:4» (input0 : (_root_.List actionDef)) (input1 : (_root_.List callableId)) : SpecTecCall (_root_.List (pair callTargetId callableDef))
  | «$unflatten_argumentListNonEmpty» (input0 : (_root_.List argument)) : SpecTecCall argumentListNonEmpty
  | «$unflatten_argumentList» (input0 : (_root_.List argument)) : SpecTecCall argumentList
  | «Decl_ok:enumTypeDeclaration-non-serializable:iter:9» (input0 : enumTypeDefIR) (input1 : (_root_.List value)) : SpecTecCall (_root_.List varTypeIR)
  | «Decl_ok:enumTypeDeclaration-serializable:iter:7» (input0 : enumTypeDefIR) (input1 : (_root_.List value)) : SpecTecCall (_root_.List varTypeIR)
  | «$unflatten_expressionList» (input0 : (_root_.List expression)) : SpecTecCall expressionList
  | «$lift_nameIR_as_tableCustomName» (input0 : nameIR) : SpecTecCall tableCustomName
  | «$lift_constantInitializerOptIR_as_initializerOpt» (input0 : (_root_.Option constantInitializerIR)) : SpecTecCall initializerOpt
  | «$unflatten_nameList» (input0 : (_root_.List name)) : SpecTecCall nameList
  | «$unflatten_typeParameterList» (input0 : (_root_.List typeParameter)) : SpecTecCall typeParameterList
  | «$unflatten_typeParameterListOpt» (input0 : (_root_.List typeParameter)) : SpecTecCall typeParameterListOpt
  | «$unflatten_namedExpressionList» (input0 : (_root_.List namedExpression)) : SpecTecCall namedExpressionList
  | «$unflatten_recordElementExpression» (input0 : (_root_.List namedExpression)) : SpecTecCall recordElementExpression
  | «$unflatten_recordElementExpression_with_default» (input0 : (_root_.List namedExpression)) : SpecTecCall recordElementExpression
  | «$lift_nameListIR_as_nonTypeNameList:case_1:iter:0» (input0 : (_root_.List nameIR)) : SpecTecCall (_root_.List name)
  | «$lift_nameListIR_as_nonTypeNameList» (input0 : (_root_.List nameIR)) : SpecTecCall nameList
  | «$lift_nameIR_as_member» (input0 : nameIR) : SpecTecCall member
  | «$lift_namedValueIR» (input0 : namedValueIR) : SpecTecCall namedExpression
  | «$lift_namedValueListIR:case_1:iter:0» (input0 : (_root_.List namedValueIR)) : SpecTecCall (_root_.List namedExpression)
  | «$lift_namedValueListIR» (input0 : (_root_.List namedValueIR)) : SpecTecCall namedExpressionList
  | «$lift_errorAccessExpressionIR» (input0 : errorAccessExpressionIR) : SpecTecCall errorAccessExpression
  | «$lift_errorDeclarationIR» (input0 : errorDeclarationIR) : SpecTecCall errorDeclaration
  | «$lift_matchKindDeclarationIR» (input0 : matchKindDeclarationIR) : SpecTecCall matchKindDeclaration
  | «$unflatten_nonEmptyParameterList» (input0 : (_root_.List parameter)) : SpecTecCall nonEmptyParameterList
  | «$unflatten_parameterList» (input0 : (_root_.List parameter)) : SpecTecCall parameterList
  | «$unflatten_constructorParameterList» (input0 : (_root_.List constructorParameter)) : SpecTecCall constructorParameterListOpt
  | «$unflatten_parserStateList» (input0 : (_root_.List parserState)) : SpecTecCall parserStateList
  | «$unflatten_realTypeArgumentList» (input0 : (_root_.List realTypeArgument)) : SpecTecCall realTypeArgumentList
  | «$unflatten_simpleKeysetExpressionList» (input0 : (_root_.List simpleKeysetExpression)) : SpecTecCall simpleKeysetExpressionList
  | «TableType_ok:rule:iter:6» (input0 : tableMetadataEnumTypeIR) (input1 : (_root_.List value)) : SpecTecCall (_root_.List varTypeIR)
  | «$unflatten_typeArgumentList» (input0 : (_root_.List typeArgument)) : SpecTecCall typeArgumentList
  | «$lift_typeParameterIR» (input0 : typeParameterIR) : SpecTecCall typeParameter
  | «$lift_typeParameterListIR:case_1:iter:0» (input0 : (_root_.List typeParameterIR)) : SpecTecCall (_root_.List typeParameter)
  | «$lift_typeParameterListIR» (input0 : (_root_.List typeParameterIR)) : SpecTecCall typeParameterListOpt
  | «$lift_nameTypeIR» (input0 : nameTypeIR) : SpecTecCall namedType
  | «$optional_annotation_of_parameterIR''» (input0 : annotation) : SpecTecCall _root_.Bool
  | «$optional_annotation_of_parameterIR':case_1:iter:1» (input0 : (_root_.List annotation)) : SpecTecCall (_root_.List _root_.Bool)
  | «$name_annotation_opt» (input0 : annotation) : SpecTecCall (_root_.Option nameIR)
  | «$name_annotation:case_1:iter:1» (input0 : (_root_.List annotation)) : SpecTecCall (_root_.List (_root_.Option nameIR))
  | «$alias_to_original_lookup_map:case_1:iter:4» (input0 : (_root_.List annotation)) : SpecTecCall (_root_.List (_root_.Option nameIR))
  | «$alias_to_original_lookup_map:case_1:iter:3» (input0 : (_root_.List (_root_.List annotation))) : SpecTecCall (_root_.List (_root_.List (_root_.Option nameIR)))
  | «$assignop_as_binop» (input0 : assignop) : SpecTecCall (_root_.Option binop)
  | «$flatten_blockElementStatementList» (input0 : blockElementStatementList) : SpecTecCall (_root_.List blockElementStatement)
  | «Cast_expl_neq:listTypeIR:iter:3» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:tupleTypeIR:iter:3» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:arrayTypeIR:iter:3» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:headerStackTypeIR:iter:3» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:structTypeIR:iter:5» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:headerTypeIR_2:iter:5» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:tupleTypeIR_2:iter:4» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:arrayTypeIR_2:iter:3» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:headerStackTypeIR_2:iter:3» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:structTypeIR_2:iter:6» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:headerTypeIR_3:iter:6» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:structTypeIR_3:iter:21» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:headerTypeIR_4:iter:21» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:structTypeIR_4:iter:21» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_expl_neq:headerTypeIR_5:iter:21» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:listTypeIR:iter:3» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:tupleTypeIR:iter:3» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:arrayTypeIR:iter:3» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:headerStackTypeIR:iter:3» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:structTypeIR:iter:5» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:headerTypeIR_2:iter:5» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:sequenceTypeIR:iter:3» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:tupleTypeIR_2:iter:4» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:arrayTypeIR_2:iter:3» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:headerStackTypeIR_2:iter:3» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:structTypeIR_2:iter:6» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:headerTypeIR_3:iter:6» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:structTypeIR_3:iter:21» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:headerTypeIR_4:iter:21» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:structTypeIR_4:iter:21» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «Cast_impl_neq:headerTypeIR_5:iter:21» (input0 : (_root_.List castResult)) : SpecTecCall _root_.Unit
  | «$flatten_controlLocalDeclarationList» (input0 : controlLocalDeclarationList) : SpecTecCall (_root_.List controlLocalDeclaration)
  | «$join_ctk» (input0 : ctk) (input1 : ctk) : SpecTecCall ctk
  | «$joins_ctk» (input0 : (_root_.List ctk)) : SpecTecCall ctk
  | «$add_callableDef_overload_t» (input0 : cursor) (input1 : typingContext) (input2 : callableId) (input3 : callableTypeDefIR) : SpecTecCall typingContext
  | «$add_callableDef_non_overload_t» (input0 : cursor) (input1 : typingContext) (input2 : callableId) (input3 : callableTypeDefIR) : SpecTecCall typingContext
  | «$add_typeDef_i» (input0 : cursor) (input1 : instContext) (input2 : typeId) (input3 : typeDefIR) : SpecTecCall instContext
  | «$add_callableDef_overload_i» (input0 : cursor) (input1 : instContext) (input2 : callableId) (input3 : callableDef) : SpecTecCall instContext
  | «$add_callableDef_non_overload_i» (input0 : cursor) (input1 : instContext) (input2 : callableId) (input3 : callableDef) : SpecTecCall instContext
  | FuncDecl_inst (input0 : cursor) (input1 : instContext) (input2 : functionDeclarationIR) : SpecTecCall instContext
  | ActionDecl_inst (input0 : cursor) (input1 : instContext) (input2 : actionDeclarationIR) : SpecTecCall instContext
  | «$bound» (input0 : cursor) (input1 : typingContext) : SpecTecCall bound
  | «$add_typeDef_t» (input0 : cursor) (input1 : typingContext) (input2 : typeId) (input3 : typeDefIR) : SpecTecCall typingContext
  | «$add_typeDefs_t» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List typeId)) (input3 : (_root_.List typeDefIR)) : SpecTecCall typingContext
  | «$add_typeParameters_t» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List typeId)) : SpecTecCall typingContext
  | «$instantiable_extern» (input0 : cursor) (input1 : typingContext) (input2 : instctxt) : SpecTecCall _root_.Bool
  | «$instantiable_parser» (input0 : cursor) (input1 : typingContext) (input2 : instctxt) : SpecTecCall _root_.Bool
  | «$instantiable_control» (input0 : cursor) (input1 : typingContext) (input2 : instctxt) : SpecTecCall _root_.Bool
  | «$instantiable_package» (input0 : cursor) (input1 : typingContext) (input2 : instctxt) : SpecTecCall _root_.Bool
  | «$instantiable_table» (input0 : cursor) (input1 : typingContext) (input2 : instctxt) : SpecTecCall _root_.Bool
  | «$callable_action» (input0 : cursor) (input1 : typingContext) : SpecTecCall _root_.Bool
  | «$callable_externFunction» (input0 : cursor) (input1 : typingContext) (input2 : nameIR) : SpecTecCall _root_.Bool
  | «$callable_externMethod» (input0 : cursor) (input1 : typingContext) : SpecTecCall _root_.Bool
  | «$callable_parserApplyMethod» (input0 : cursor) (input1 : typingContext) : SpecTecCall _root_.Bool
  | «$callable_controlApplyMethod» (input0 : cursor) (input1 : typingContext) : SpecTecCall _root_.Bool
  | «$callable_tableApplyMethod» (input0 : cursor) (input1 : typingContext) : SpecTecCall _root_.Bool
  | «$inherit_i» (input0 : cursor) (input1 : instContext) : SpecTecCall instContext
  | «$add_var_i» (input0 : cursor) (input1 : instContext) (input2 : id) (input3 : value) : SpecTecCall instContext
  | «$add_vars_i» (input0 : cursor) (input1 : instContext) (input2 : (_root_.List id)) (input3 : (_root_.List value)) : SpecTecCall instContext
  | «$add_type_i» (input0 : cursor) (input1 : instContext) (input2 : typeId) (input3 : typeIR) : SpecTecCall instContext
  | «$add_types_i» (input0 : cursor) (input1 : instContext) (input2 : (_root_.List typeId)) (input3 : (_root_.List typeIR)) : SpecTecCall instContext
  | ConstDecl_inst (input0 : cursor) (input1 : instContext) (input2 : constantDeclarationIR) : SpecTecCall instContext
  | «$inherit_e» (input0 : cursor) (input1 : evalContext) : SpecTecCall evalContext
  | «$copy_e» (input0 : cursor) (input1 : evalContext) (input2 : evalContext) : SpecTecCall evalContext
  | «$find_type_e» (input0 : cursor) (input1 : evalContext) (input2 : nameIR) : SpecTecCall (_root_.Option typeIR)
  | «$directionless_trailing'» (input0 : _root_.Bool) (input1 : (_root_.List direction)) : SpecTecCall _root_.Bool
  | «$directionless_trailing» (input0 : (_root_.List direction)) : SpecTecCall _root_.Bool
  | «$split_dataplane_parameters» (input0 : (_root_.List parameterIR)) : SpecTecCall ((_root_.List parameterIR) × (_root_.List parameterIR))
  | «$flatten_externConstructorOrMethodPrototypeList» (input0 : externConstructorOrMethodPrototypeList) : SpecTecCall (_root_.List externConstructorOrMethodPrototype)
  | «$parameterListIR_of_externMethodDef» (input0 : externMethodDef) : SpecTecCall (_root_.List parameterIR)
  | «$type_of_externMethodPrototypeIR» (input0 : externMethodPrototypeIR) : SpecTecCall externMethodTypeDefIR
  | «Decl_ok:externObjectDeclaration:iter:7» (input0 : (_root_.List externMethodPrototypeIR)) : SpecTecCall (_root_.List externMethodTypeDefIR)
  | ExternMethod_inst (input0 : instContext) (input1 : externMethodPrototypeIR) : SpecTecCall instContext
  | ExternMethods_inst (input0 : instContext) (input1 : (_root_.List externMethodPrototypeIR)) : SpecTecCall instContext
  | «Decl_inst:non-constructor:iter:3» (input0 : (_root_.List externMethodPrototypeIR)) : SpecTecCall (_root_.List externMethodTypeDefIR)
  | «Decl_inst:constructor:iter:3» (input0 : (_root_.List externMethodPrototypeIR)) : SpecTecCall (_root_.List externMethodTypeDefIR)
  | «$callableId_of_externMethodPrototypeIR» (input0 : externMethodPrototypeIR) : SpecTecCall callableId
  | «Decl_inst:non-constructor:iter:1» (input0 : (_root_.List externMethodPrototypeIR)) : SpecTecCall (_root_.List callableId)
  | «Decl_inst:constructor:iter:1» (input0 : (_root_.List externMethodPrototypeIR)) : SpecTecCall (_root_.List callableId)
  | «$is_concrete_extern_object''» (input0 : externMethodTypeDefIR) : SpecTecCall _root_.Bool
  | «$is_concrete_extern_object':case_2:iter:3» (input0 : (_root_.List externMethodTypeDefIR)) : SpecTecCall _root_.Unit
  | «$parameterListIR_of_externMethodTypeDefIR» (input0 : externMethodTypeDefIR) : SpecTecCall (_root_.List parameterIR)
  | «$join_flow» (input0 : flow) (input1 : flow) : SpecTecCall flow
  | «$join_control_t» (input0 : typingContext) (input1 : typingContext) : SpecTecCall flow
  | «$resolve_constraint» (input0 : strictness) (input1 : constraint) : SpecTecCall inference
  | «$flatten_objectDeclarationList» (input0 : objectDeclarationList) : SpecTecCall (_root_.List objectDeclaration)
  | «$flatten_p4program» (input0 : p4program) : SpecTecCall (_root_.List declaration)
  | «$flatten_parserBlockElementStatementList» (input0 : parserBlockElementStatementList) : SpecTecCall (_root_.List parserBlockElementStatement)
  | «$flatten_parserLocalDeclarationList» (input0 : parserLocalDeclarationList) : SpecTecCall (_root_.List parserLocalDeclaration)
  | «$flatten_prefixedNameIR» (input0 : prefixedNameIR) : SpecTecCall nameIR
  | «$lift_prefixedNameIR_as_prefixedNonTypeName» (input0 : prefixedNameIR) : SpecTecCall prefixedNonTypeName
  | «$lift_prefixedNameIR_as_prefixedTypeName» (input0 : prefixedNameIR) : SpecTecCall prefixedTypeName
  | «$lift_referenceExpressionIR» (input0 : referenceExpressionIR) : SpecTecCall referenceExpression
  | «$find_var_t» (input0 : prefixedNameIR) (input1 : cursor) (input2 : typingContext) : SpecTecCall (_root_.Option varTypeIR)
  | «$find_var_value_t» (input0 : prefixedNameIR) (input1 : cursor) (input2 : typingContext) : SpecTecCall value
  | «$find_typeDef_t» (input0 : cursor) (input1 : typingContext) (input2 : prefixedNameIR) : SpecTecCall (_root_.Option typeDefIR)
  | «$find_callableDef_non_overloaded_t» (input0 : cursor) (input1 : typingContext) (input2 : prefixedNameIR) : SpecTecCall (_root_.Option (callableId × callableTypeDefIR))
  | «TableType_ok:rule:iter:3» (input0 : (_root_.List prefixedNameIR)) : SpecTecCall (_root_.List nameIR)
  | «$find_callableDef_non_overload_i» (input0 : cursor) (input1 : instContext) (input2 : prefixedNameIR) : SpecTecCall (_root_.Option (cursor × (callableId × callableDef)))
  | «$find_var_i» (input0 : prefixedNameIR) (input1 : cursor) (input2 : instContext) : SpecTecCall value
  | «$find_typeDef_i» (input0 : cursor) (input1 : instContext) (input2 : prefixedNameIR) : SpecTecCall (_root_.Option typeDefIR)
  | «$add_var_e» (input0 : cursor) (input1 : evalContext) (input2 : prefixedNameIR) (input3 : value) : SpecTecCall evalContext
  | «$add_vars_e» (input0 : cursor) (input1 : evalContext) (input2 : (_root_.List prefixedNameIR)) (input3 : (_root_.List value)) : SpecTecCall evalContext
  | «$update_var_e» (input0 : cursor) (input1 : evalContext) (input2 : prefixedNameIR) (input3 : value) : SpecTecCall evalContext
  | «$find_var_e» (input0 : prefixedNameIR) (input1 : cursor) (input2 : evalContext) : SpecTecCall value
  | «$find_typeDef_e» (input0 : cursor) (input1 : evalContext) (input2 : prefixedNameIR) : SpecTecCall (_root_.Option typeDefIR)
  | ConstDecl_eval (input0 : cursor) (input1 : evalContext) (input2 : constantDeclarationIR) : SpecTecCall evalContext
  | «$find_tableActionIR_qualified» (input0 : (_root_.List tableActionIR)) (input1 : nameIR) : SpecTecCall (_root_.Option (nameIR × tableActionIR))
  | «$find_tableActionIR_unqualified'» (input0 : (_root_.List tableActionIR)) (input1 : nameIR) : SpecTecCall (_root_.Option (nameIR × tableActionIR))
  | «$find_tableActionIR_unqualified» (input0 : (_root_.List tableActionIR)) (input1 : nameIR) : SpecTecCall (_root_.Option (nameIR × tableActionIR))
  | «$flatten_selectCaseList» (input0 : selectCaseList) : SpecTecCall (_root_.List selectCase)
  | «$switchLabelIR_of_switchCaseIR» (input0 : switchCaseIR) : SpecTecCall switchLabelIR
  | «Stmt_ok:table:iter:4» (input0 : (_root_.List switchCaseIR)) : SpecTecCall (_root_.List switchLabelIR)
  | «Stmt_ok:general:iter:3» (input0 : (_root_.List switchCaseIR)) : SpecTecCall (_root_.List switchLabelIR)
  | «$is_non_fallthrough_switchCaseIR» (input0 : switchCaseIR) : SpecTecCall _root_.Bool
  | «SwitchCases_table_eval:cons-fallthrough-match:iter:1» (input0 : (_root_.List switchCaseIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «SwitchCases_table_eval:cons-fallthrough-match-no-block:iter:1» (input0 : (_root_.List switchCaseIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «SwitchCases_general_eval:cons-fallthrough-match:iter:2» (input0 : (_root_.List switchCaseIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «SwitchCases_general_eval:cons-fallthrough-match-no-block:iter:2» (input0 : (_root_.List switchCaseIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$flatten_switchCaseList» (input0 : switchCaseList) : SpecTecCall (_root_.List switchCase)
  | «$flatten_tableActionList» (input0 : tableActionList) : SpecTecCall (_root_.List tableAction)
  | «$is_largest_priority_wins» (input0 : tableCustomPropertyIR) : SpecTecCall _root_.Bool
  | «$largest_priority_wins:case_1:iter:0» (input0 : (_root_.List tableCustomPropertyIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$largest_priority_wins:case_2:iter:0» (input0 : (_root_.List tableCustomPropertyIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$flatten_tableEntryList» (input0 : tableEntryList) : SpecTecCall (_root_.List tableEntry)
  | «$set_priorities_of_tableEntryListIR:case_2:iter:1» (input0 : (_root_.List tableEntryState)) : SpecTecCall _root_.Unit
  | «$join_tableEntryState» (input0 : tableEntryState) (input1 : tableEntryState) : SpecTecCall tableEntryState
  | «$flatten_tableKeyList» (input0 : tableKeyList) : SpecTecCall (_root_.List tableKey)
  | «$text_of_number_tableKeyValueInterface» (input0 : tableKeyValueInterface) : SpecTecCall (_root_.Option _root_.String)
  | «$is_tableDefaultActionProperty» (input0 : tableProperty) : SpecTecCall _root_.Bool
  | «Table_ok:zero-default-action:iter:8» (input0 : (_root_.List tableProperty)) : SpecTecCall (_root_.List _root_.Bool)
  | «Table_ok:one-default-action:iter:8» (input0 : (_root_.List tableProperty)) : SpecTecCall (_root_.List _root_.Bool)
  | «$is_tableLargestPriorityWinsProperty» (input0 : tableProperty) : SpecTecCall _root_.Bool
  | «Table_ok:zero-default-action:iter:12» (input0 : (_root_.List tableProperty)) : SpecTecCall (_root_.List _root_.Bool)
  | «Table_ok:one-default-action:iter:12» (input0 : (_root_.List tableProperty)) : SpecTecCall (_root_.List _root_.Bool)
  | «$is_tableActionsProperty» (input0 : tableProperty) : SpecTecCall _root_.Bool
  | «Table_ok:zero-default-action:iter:4» (input0 : (_root_.List tableProperty)) : SpecTecCall (_root_.List _root_.Bool)
  | «Table_ok:one-default-action:iter:4» (input0 : (_root_.List tableProperty)) : SpecTecCall (_root_.List _root_.Bool)
  | «$is_tableKeysProperty» (input0 : tableProperty) : SpecTecCall _root_.Bool
  | «Table_ok:zero-default-action:iter:0» (input0 : (_root_.List tableProperty)) : SpecTecCall (_root_.List _root_.Bool)
  | «Table_ok:one-default-action:iter:0» (input0 : (_root_.List tableProperty)) : SpecTecCall (_root_.List _root_.Bool)
  | «$flatten_tablePropertyList» (input0 : tablePropertyList) : SpecTecCall (_root_.List tableProperty)
  | «$flatten_typeFieldList» (input0 : typeFieldList) : SpecTecCall (_root_.List typeField)
  | «$lift_aliasTypeIR» (input0 : aliasTypeIR) : SpecTecCall type
  | «$flatten_annotationList» (input0 : annotationList) : SpecTecCall (_root_.List annotation)
  | «$optional_annotation_of_parameterIR'» (input0 : annotationList) : SpecTecCall _root_.Bool
  | «$optional_annotation_of_parameterIR» (input0 : parameterIR) : SpecTecCall _root_.Bool
  | «$is_optional_parameterIR» (input0 : parameterIR) : SpecTecCall _root_.Bool
  | «$match_overloaded_named:case_2:iter:5» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$match_overloaded_named:case_2:iter:14» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$match_overloaded_named» (V_T : Type) (input0 : (pair callTargetId V_T)) (input1 : namedCallTargetKey) (input2 : (V_T → (SpecTecCall parameterListIR))) : SpecTecCall callTargetMatch
  | «$match_overloaded_unnamed:case_1:iter:3» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$match_overloaded_unnamed:case_2:iter:3» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$match_overloaded_unnamed:case_2:iter:8» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «$match_overloaded_unnamed:case_3:iter:3» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$match_overloaded_unnamed:case_3:iter:10» (V_T : Type) (input0 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «$match_overloaded_unnamed» (V_T : Type) (input0 : (pair callTargetId V_T)) (input1 : unnamedCallTargetKey) (input2 : (V_T → (SpecTecCall parameterListIR))) : SpecTecCall callTargetMatch
  | «$find_overloadeds_named» (V : Type) (input0 : (map callableId V)) (input1 : namedCallTargetKey) (input2 : (V → (SpecTecCall parameterListIR))) : SpecTecCall (_root_.List (callResolution V))
  | «$find_overloadeds_unnamed» (V : Type) (input0 : (map callableId V)) (input1 : unnamedCallTargetKey) (input2 : (V → (SpecTecCall parameterListIR))) : SpecTecCall (_root_.List (callResolution V))
  | «$find_overloaded» (V_T : Type) (input0 : (map callTargetId V_T)) (input1 : callTargetKey) (input2 : (V_T → (SpecTecCall parameterListIR))) : SpecTecCall (_root_.Option (callResolution V_T))
  | «$name_annotation» (input0 : annotationList) : SpecTecCall (_root_.List nameIR)
  | «$name_annotation_default» (input0 : annotationList) (input1 : nameIR) : SpecTecCall nameIR
  | «$find_name_annotation_opt» (input0 : annotationList) : SpecTecCall (_root_.Option annotation)
  | «$add_annotationList» (input0 : annotationList) (input1 : (_root_.Option annotation)) : SpecTecCall annotationList
  | «CallableType_wf:actionTypeIR:iter:2» (input0 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «CallableType_wf:definedFunctionTypeIR:iter:2» (input0 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «CallableType_wf:abstract:iter:2» (input0 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «CallableType_wf:parserApplyMethodTypeIR:iter:2» (input0 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «CallableType_wf:controlApplyMethodTypeIR:iter:2» (input0 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «ConstructorType_wf:parserObjectTypeIR:iter:1» (input0 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «ConstructorType_wf:controlObjectTypeIR:iter:1» (input0 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «$alias_to_original_lookup_map:case_1:iter:1» (input0 : (_root_.List annotationList)) : SpecTecCall (_root_.List (_root_.List annotation))
  | «$alias_to_original_lookup_map» (input0 : (_root_.List parameterIR)) : SpecTecCall (map nameIR nameIR)
  | «$align_tableActionArgumentInterfaces» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List tableActionArgumentInterface)) : SpecTecCall (_root_.List _root_.Int)
  | «$field_list_annotation_index'» (input0 : annotation) : SpecTecCall (_root_.Option integerLiteral)
  | «$field_list_annotation_index:case_1:iter:1» (input0 : (_root_.List annotation)) : SpecTecCall (_root_.List (_root_.Option integerLiteral))
  | «$align_parameterListIR_given» (input0 : (map id parameterIR)) (input1 : (_root_.List parameterIR)) (input2 : (_root_.List argumentIR)) : SpecTecCall (_root_.List parameterIR)
  | «$align_parameterListIR» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List argumentIR)) (input2 : (_root_.List nameIR)) (input3 : (_root_.List nameIR)) : SpecTecCall callAlign
  | «$callTargetKey'» (input0 : argumentIR) : SpecTecCall (_root_.Option id)
  | «$callTargetKey:case_1:iter:0» (input0 : (_root_.List argumentIR)) : SpecTecCall (_root_.List (_root_.Option id))
  | «$callTargetKey» (input0 : nameIR) (input1 : argumentListIR) : SpecTecCall callTargetKey
  | «$find_constructorDef_overloaded_t» (input0 : typingContext) (input1 : prefixedNameIR) (input2 : (_root_.List argumentIR)) : SpecTecCall (_root_.Option (callResolution constructorTypeDefIR))
  | «$flatten_argumentList» (input0 : argumentList) : SpecTecCall (_root_.List argument)
  | «$lift_baseTypeIR» (input0 : baseTypeIR) : SpecTecCall baseType
  | «$signature_of_builtinMethodTypeIR» (input0 : builtinMethodTypeIR) : SpecTecCall ((_root_.List parameterIR) × typeIR)
  | TableAction_inst (input0 : instContext) (input1 : store) (input2 : tableActionIR) : SpecTecCall (store × tableActionIR)
  | TableActions_inst (input0 : instContext) (input1 : store) (input2 : (_root_.List tableActionIR)) : SpecTecCall (store × (_root_.List tableActionIR))
  | «Constructor_call:controlConstructorDef:iter:8» (input0 : (_root_.List callableDef)) : SpecTecCall _root_.Unit
  | «$merge_externMethodDefEnvs» (input0 : externMethodDefEnv) (input1 : callableDefEnv) : SpecTecCall externMethodDefEnv
  | «Constructor_call:externConstructorDef:iter:8» (input0 : (_root_.List callableDef)) : SpecTecCall _root_.Unit
  | «$subst_typeIR':case_15:iter:7» (input0 : (_root_.List callableTypeDefIR)) : SpecTecCall _root_.Unit
  | «$callableTypeIR_of_callableTypeDefIR» (input0 : callableTypeDefIR) : SpecTecCall callableTypeIR
  | «$typeParameterListIR_of_callableTypeDefIR» (input0 : callableTypeDefIR) : SpecTecCall ((_root_.List typeParameterIR) × (_root_.List typeParameterIR))
  | «$is_static_callableTypeIR» (input0 : callableTypeIR) : SpecTecCall ctk
  | «$is_static_assert_callableTypeIR» (input0 : callableTypeIR) : SpecTecCall _root_.Bool
  | «$flatten_constOpt» (input0 : constOpt) : SpecTecCall (_root_.Option const)
  | «$parameterListIR_of_constructorDef» (input0 : constructorDef) : SpecTecCall (_root_.List parameterIR)
  | «$find_constructorDef_i» (input0 : instContext) (input1 : prefixedNameIR) (input2 : (_root_.List argumentIR)) : SpecTecCall (_root_.Option (callResolution constructorDef))
  | «$find_constructorDef_e» (input0 : evalContext) (input1 : prefixedNameIR) (input2 : (_root_.List argumentIR)) : SpecTecCall (_root_.Option (callResolution constructorDef))
  | «$flatten_expressionList» (input0 : expressionList) : SpecTecCall (_root_.List expression)
  | «$is_externConstructorPrototype» (input0 : externConstructorOrMethodPrototype) : SpecTecCall _root_.Bool
  | «$is_externMethodPrototype» (input0 : externConstructorOrMethodPrototype) : SpecTecCall _root_.Bool
  | «$split_externConstructorOrMethodPrototypeList:case_1:iter:1» (input0 : (_root_.List externConstructorOrMethodPrototype)) : SpecTecCall (_root_.List _root_.Bool)
  | «$split_externConstructorOrMethodPrototypeList:case_1:iter:6» (input0 : (_root_.List externConstructorOrMethodPrototype)) : SpecTecCall (_root_.List _root_.Bool)
  | «$split_externConstructorOrMethodPrototypeList» (input0 : externConstructorOrMethodPrototypeList) : SpecTecCall ((_root_.List externConstructorPrototype) × (_root_.List externMethodPrototype))
  | «$flatten_forInitStatementList» (input0 : forInitStatementList) : SpecTecCall (_root_.List forInitStatement)
  | «$flatten_forUpdateStatementList» (input0 : forUpdateStatementList) : SpecTecCall (_root_.List forUpdateStatement)
  | «$parameterListIR_of_functionDef» (input0 : functionDef) : SpecTecCall (_root_.List parameterIR)
  | «$parameterListIR_of_functionTypeDefIR» (input0 : functionTypeDefIR) : SpecTecCall (_root_.List parameterIR)
  | «$width_of_integerTypeIR» (input0 : integerTypeIR) : SpecTecCall (_root_.Option _root_.Nat)
  | «$int_of_integerValue» (input0 : integerValue) : SpecTecCall _root_.Int
  | «$nat_of_integerValue» (input0 : integerValue) : SpecTecCall (_root_.Option _root_.Nat)
  | «$set_priorities_of_tableEntryListIR'» (input0 : tableContext) (input1 : _root_.Nat) (input2 : (_root_.List tableEntryIR)) : SpecTecCall (_root_.List tableEntryIR)
  | «$set_priorities_of_tableEntryListIR» (input0 : tableContext) (input1 : (_root_.List tableEntryState)) (input2 : tableEntryListIR) : SpecTecCall tableEntryListIR
  | «$get_tableEntryPriority» (input0 : (_root_.Option tableEntryPriorityIR)) : SpecTecCall (_root_.Option _root_.Nat)
  | «$flatten_keysetExpressionIR» (input0 : keysetExpressionIR) : SpecTecCall simpleKeysetExpressionListIR
  | «$find_local_return_type_t» (input0 : typingContext) : SpecTecCall (_root_.Option typeIR)
  | «$callable_definedFunction» (input0 : cursor) (input1 : typingContext) : SpecTecCall _root_.Bool
  | «$lvalue_as_expression» (input0 : lvalue) : SpecTecCall expression
  | «$typedLvalueIR_as_typedExpressionIR» (input0 : typedLvalueIR) : SpecTecCall (_root_.Option typedExpressionIR)
  | «$expression_as_lvalue» (input0 : expression) : SpecTecCall (_root_.Option lvalue)
  | «$expression_as_expressionNonBrace» (input0 : expression) : SpecTecCall expressionNonBrace
  | «$typedExpressionIR_as_typedLvalueIR» (input0 : typedExpressionIR) : SpecTecCall (_root_.Option typedLvalueIR)
  | «$subexpressions_of_typedExpressionIR» (input0 : typedExpressionIR) : SpecTecCall typedExpressionListIR
  | «$subexpressions_of_typedExpressionListIR» (input0 : typedExpressionListIR) : SpecTecCall typedExpressionListIR
  | «$subexpressions_of_typedExpressionListIR:case_1:iter:0» (input0 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List (_root_.List typedExpressionIR))
  | «$subexpressions_of_expressionIR» (input0 : expressionIR) : SpecTecCall typedExpressionListIR
  | «$subexpressions_of_argumentIR» (input0 : argumentIR) : SpecTecCall typedExpressionListIR
  | «$subexpressions_of_argumentListIR» (input0 : argumentListIR) : SpecTecCall typedExpressionListIR
  | «$subexpressions_of_argumentListIR:case_1:iter:0» (input0 : (_root_.List argumentIR)) : SpecTecCall (_root_.List (_root_.List typedExpressionIR))
  | «$expressionNonBrace_as_expression» (input0 : expressionNonBrace) : SpecTecCall expression
  | «$parameterListIR_of_methodDef» (input0 : methodDef) : SpecTecCall (_root_.List parameterIR)
  | «$parameterListIR_of_callableDef» (input0 : callableDef) : SpecTecCall (_root_.List parameterIR)
  | «$find_callableDef_overloaded_e» (input0 : cursor) (input1 : evalContext) (input2 : prefixedNameIR) (input3 : (_root_.List argumentIR)) : SpecTecCall (_root_.Option (callResolution (cursor × callableDef)))
  | «$parameterListIR_of_methodTypeDefIR» (input0 : methodTypeDefIR) : SpecTecCall (_root_.List parameterIR)
  | «$parameterListIR_of_callableTypeDefIR» (input0 : callableTypeDefIR) : SpecTecCall (_root_.List parameterIR)
  | «$find_callableDef_overloaded_t» (input0 : cursor) (input1 : typingContext) (input2 : prefixedNameIR) (input3 : (_root_.List argumentIR)) : SpecTecCall (_root_.Option (callResolution callableTypeDefIR))
  | «$flatten_nameList» (input0 : nameList) : SpecTecCall (_root_.List name)
  | «$flatten_namedExpressionList» (input0 : namedExpressionList) : SpecTecCall (_root_.List namedExpression)
  | «$find_objectState_e» (input0 : arch) (input1 : objectId) : SpecTecCall (_root_.Option objectState)
  | «$update_objectState_e» (input0 : arch) (input1 : objectId) (input2 : objectState) : SpecTecCall (_root_.Option arch)
  | «$V1Model_setup_hdr_argument» (input0 : arch) : SpecTecCall argumentIR
  | «$V1Model_setup_meta_argument» (input0 : arch) : SpecTecCall argumentIR
  | «$eBPF_setup_headers_argument» (input0 : arch) : SpecTecCall argumentIR
  | «$PSA_setup_normal_meta_argument» (input0 : arch) : SpecTecCall argumentIR
  | «$PSA_setup_clone_i2e_meta_argument» (input0 : arch) : SpecTecCall argumentIR
  | «$PSA_setup_clone_e2e_meta_argument» (input0 : arch) : SpecTecCall argumentIR
  | «$PSA_setup_resubmit_meta_argument» (input0 : arch) : SpecTecCall argumentIR
  | «$PSA_setup_recirculate_meta_argument» (input0 : arch) : SpecTecCall argumentIR
  | «$PSA_setup_ingress_hdr_argument» (input0 : arch) : SpecTecCall argumentIR
  | «$PSA_setup_ingress_user_meta_argument» (input0 : arch) : SpecTecCall argumentIR
  | «$PSA_setup_egress_hdr_argument» (input0 : arch) : SpecTecCall argumentIR
  | «$PSA_setup_egress_user_meta_argument» (input0 : arch) : SpecTecCall argumentIR
  | «Copy_in_default:rule:iter:3» (input0 : (_root_.List parameterInitializerIR)) : SpecTecCall _root_.Unit
  | Copy_in_default (input0 : parameterListIR) (input1 : cursor) (input2 : evalContext) : SpecTecCall evalContext
  | «$flatten_parameterList» (input0 : parameterList) : SpecTecCall (_root_.List parameter)
  | «$flatten_constructorParameterListOpt» (input0 : constructorParameterListOpt) : SpecTecCall (_root_.List constructorParameter)
  | «$callableId'» (input0 : parameterList) : SpecTecCall (_root_.List id)
  | «$callableId» (input0 : name) (input1 : parameterList) : SpecTecCall callableId
  | «$constructorId» (input0 : name) (input1 : constructorParameterListOpt) : SpecTecCall constructorId
  | «$callableId_of_externMethodPrototype» (input0 : externMethodPrototype) : SpecTecCall callableId
  | «$constructorId_of_externConstructorPrototype» (input0 : externConstructorPrototype) : SpecTecCall constructorId
  | «Decl_ok:externObjectDeclaration:iter:4» (input0 : (_root_.List externMethodPrototype)) : SpecTecCall (_root_.List callableId)
  | «Decl_ok:externObjectDeclaration:iter:14» (input0 : (_root_.List externConstructorPrototype)) : SpecTecCall (_root_.List constructorId)
  | «$flatten_parserStateList» (input0 : parserStateList) : SpecTecCall (_root_.List parserState)
  | «$prefixedNonTypeName» (input0 : prefixedNonTypeName) : SpecTecCall prefixedNameIR
  | «$prefixedTypeName» (input0 : prefixedTypeName) : SpecTecCall prefixedNameIR
  | «$flatten_realTypeArgumentList» (input0 : realTypeArgumentList) : SpecTecCall (_root_.List realTypeArgument)
  | «$is_singleton_list_expression» (input0 : expression) : SpecTecCall _root_.Bool
  | «$flatten_simpleKeysetExpressionList» (input0 : simpleKeysetExpressionList) : SpecTecCall (_root_.List simpleKeysetExpression)
  | SwitchLabel_table_ok (input0 : typingContext) (input1 : typeId) (input2 : switchLabel) : SpecTecCall switchLabelIR
  | «$match_switchLabelIR_table» (input0 : id) (input1 : switchLabelIR) : SpecTecCall _root_.Bool
  | SwitchCases_table_eval (input0 : id) (input1 : switchCaseListIR) : SpecTecCall (_root_.Option blockStatementIR)
  | «$insert_NoAction_tablePropertyIR» (input0 : tableContext) (input1 : (_root_.List tablePropertyIR)) : SpecTecCall (tableContext × (_root_.List tablePropertyIR))
  | «$init_table:case_1:iter:1» (input0 : (_root_.List tablePropertyIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$init_table:case_1:iter:10» (input0 : (_root_.List tablePropertyIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$init_table:case_1:iter:5» (input0 : (_root_.List tablePropertyIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$init_tableEntries:case_1:iter:0» (input0 : (_root_.List tablePropertyIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$init_tableEntries:case_2:iter:0» (input0 : (_root_.List tablePropertyIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$init_tableEntries» (input0 : tablePropertyListIR) : SpecTecCall tableEntriesPropertyIR
  | «$init_tableKeys:case_1:iter:0» (input0 : (_root_.List tablePropertyIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$init_tableKeys:case_2:iter:0» (input0 : (_root_.List tablePropertyIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$init_tableKeys» (input0 : tablePropertyListIR) : SpecTecCall tableKeysPropertyIR
  | «$init_table» (input0 : tablePropertyListIR) : SpecTecCall tableObjectProperty
  | «$flatten_typeArgumentList» (input0 : typeArgumentList) : SpecTecCall (_root_.List typeArgument)
  | «$typeIR_of_typeDefIR» (input0 : typeDefIR) : SpecTecCall typeIR
  | «$typeParameterListIR_of_typeDefIR» (input0 : typeDefIR) : SpecTecCall ((_root_.List typeParameterIR) × (_root_.List typeParameterIR))
  | «$is_monomorphic_typeDefIR» (input0 : typeDefIR) : SpecTecCall _root_.Bool
  | «$is_polymorphic_typeDefIR» (input0 : typeDefIR) : SpecTecCall _root_.Bool
  | «$typeId_of_typeDefIR» (input0 : typeDefIR) : SpecTecCall typeId
  | «$lift_typeDefIR_as_typeName» (input0 : typeDefIR) : SpecTecCall typeName
  | «$cast_array» (input0 : typeIR) (input1 : arrayValue) : SpecTecCall value
  | «$is_concrete_extern_object'» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$cast_header_stack» (input0 : typeIR) (input1 : headerStackValue) : SpecTecCall value
  | «$cast_header» (input0 : typeIR) (input1 : headerValue) : SpecTecCall value
  | «$cast_header_union» (input0 : typeIR) (input1 : headerUnionValue) : SpecTecCall value
  | «$cast_string» (input0 : typeIR) (input1 : stringValue) : SpecTecCall value
  | «$cast_struct» (input0 : typeIR) (input1 : structValue) : SpecTecCall value
  | «$unroll_typeIR» (input0 : typeIR) : SpecTecCall typeIR
  | «$unroll_aliasTypeIR» (input0 : typeIR) : SpecTecCall typeIR
  | «$free_typeIR» (input0 : typeIR) : SpecTecCall bound
  | «$free_typeIR:case_6:iter:1» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_9:iter:3» (input0 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_9:iter:6» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_10:iter:3» (input0 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_10:iter:6» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_11:iter:3» (input0 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_11:iter:6» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_14:iter:3» (input0 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_14:iter:6» (input0 : (_root_.List externMethodTypeDefIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_15:iter:1» (input0 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_15:iter:4» (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_16:iter:1» (input0 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_16:iter:4» (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_17:iter:1» (input0 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_17:iter:4» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_21:iter:1» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_22:iter:1» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_23:iter:3» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_typeIR:case_24:iter:3» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_parameterIR» (input0 : parameterIR) : SpecTecCall bound
  | «$free_callableTypeIR» (input0 : callableTypeIR) : SpecTecCall bound
  | «$free_callableTypeIR:case_1:iter:1» (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_callableTypeIR:case_2:iter:1» (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_callableTypeIR:case_3:iter:1» (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_callableTypeIR:case_5:iter:1» (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_callableTypeIR:case_6:iter:1» (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_callableTypeIR:case_7:iter:1» (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_callableTypeIR:case_8:iter:1» (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_callableTypeDefIR» (input0 : callableTypeDefIR) : SpecTecCall bound
  | «$free_typeDefIR» (input0 : typeDefIR) : SpecTecCall bound
  | «$free_parameterIRs:case_1:iter:0» (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$free_parameterIRs» (input0 : (_root_.List parameterIR)) : SpecTecCall bound
  | «$capture_avoiding_:case_1:iter:4» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$capture_avoiding_» (input0 : theta) (input1 : (_root_.List typeParameterIR)) (input2 : bound) : SpecTecCall (theta × (_root_.List typeParameterIR))
  | «$capture_avoiding:case_1:iter:4» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List (set _root_.String))
  | «$capture_avoiding» (input0 : theta) (input1 : (_root_.List typeId)) (input2 : (_root_.List typeId)) (input3 : bound) : SpecTecCall (theta × ((_root_.List typeId) × (_root_.List typeId)))
  | «$subst_typeIR» (input0 : theta) (input1 : typeIR) : SpecTecCall typeIR
  | «$subst_typeIR'» (input0 : theta) (input1 : typeIR) : SpecTecCall typeIR
  | «$subst_typeIR':case_7:iter:1» (input0 : theta) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List typeIR)
  | «$subst_typeIR':case_10:iter:3» (input0 : theta) (input1 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List typeArgumentIR)
  | «$subst_typeIR':case_10:iter:5» (input0 : theta) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List typeIR)
  | «$subst_typeIR':case_11:iter:3» (input0 : theta) (input1 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List typeArgumentIR)
  | «$subst_typeIR':case_11:iter:5» (input0 : theta) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List typeIR)
  | «$subst_typeIR':case_12:iter:3» (input0 : theta) (input1 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List typeArgumentIR)
  | «$subst_typeIR':case_12:iter:5» (input0 : theta) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List typeIR)
  | «$subst_typeIR':case_15:iter:3» (input0 : theta) (input1 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List typeArgumentIR)
  | «$subst_typeIR':case_15:iter:5» (input0 : theta) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecCall (_root_.List callableTypeDefIR)
  | «$subst_typeIR':case_16:iter:1» (input0 : theta) (input1 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List typeArgumentIR)
  | «$subst_typeIR':case_16:iter:3» (input0 : theta) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «$subst_typeIR':case_17:iter:1» (input0 : theta) (input1 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List typeArgumentIR)
  | «$subst_typeIR':case_17:iter:3» (input0 : theta) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «$subst_typeIR':case_18:iter:1» (input0 : theta) (input1 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List typeArgumentIR)
  | «$subst_typeIR':case_18:iter:3» (input0 : theta) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List typeIR)
  | «$subst_typeIR':case_22:iter:1» (input0 : theta) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List typeIR)
  | «$subst_typeIR':case_23:iter:1» (input0 : theta) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List typeIR)
  | «$subst_typeIR':case_24:iter:3» (input0 : theta) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List typeIR)
  | «$subst_typeIR':case_25:iter:3» (input0 : theta) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List typeIR)
  | «$subst_parameterIR» (input0 : theta) (input1 : parameterIR) : SpecTecCall parameterIR
  | «$subst_parameterIR'» (input0 : theta) (input1 : parameterIR) : SpecTecCall parameterIR
  | «$subst_callableTypeIR'» (input0 : theta) (input1 : callableTypeIR) : SpecTecCall callableTypeIR
  | «$subst_callableTypeIR':case_1:iter:1» (input0 : theta) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «$subst_callableTypeIR':case_2:iter:1» (input0 : theta) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «$subst_callableTypeIR':case_3:iter:1» (input0 : theta) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «$subst_callableTypeIR':case_5:iter:1» (input0 : theta) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «$subst_callableTypeIR':case_6:iter:1» (input0 : theta) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «$subst_callableTypeIR':case_7:iter:1» (input0 : theta) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «$subst_callableTypeIR':case_8:iter:1» (input0 : theta) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «$subst_callableTypeDefIR» (input0 : theta) (input1 : callableTypeDefIR) : SpecTecCall callableTypeDefIR
  | «$subst_callableTypeDefIR'» (input0 : theta) (input1 : callableTypeDefIR) : SpecTecCall callableTypeDefIR
  | «$subst_callableTypeDefIR':case_2:iter:3» (input0 : theta) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «$subst_callableTypeDefIR':case_3:iter:3» (input0 : theta) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «$subst_callableTypeDefIR':case_4:iter:3» (input0 : theta) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «$subst_callableTypeDefIR':case_5:iter:3» (input0 : theta) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «$subst_callableTypeIR» (input0 : theta) (input1 : callableTypeIR) : SpecTecCall callableTypeIR
  | «$subst_constructorTypeIR':case_1:iter:0» (input0 : theta) (input1 : (_root_.List constructorParameterIR)) : SpecTecCall (_root_.List constructorParameterIR)
  | «$subst_constructorTypeIR'» (input0 : theta) (input1 : constructorTypeIR) : SpecTecCall constructorTypeIR
  | «$subst_constructorTypeIR» (input0 : theta) (input1 : constructorTypeIR) : SpecTecCall constructorTypeIR
  | «$specialize_typeDefIR» (input0 : typeDefIR) (input1 : (_root_.List typeIR)) : SpecTecCall typeIR
  | «$specialize_callableTypeDefIR» (input0 : callableTypeDefIR) (input1 : (_root_.List typeIR)) : SpecTecCall (callableTypeIR × (_root_.List typeId))
  | «$specialize_constructorTypeDefIR» (input0 : constructorTypeDefIR) (input1 : (_root_.List typeIR)) : SpecTecCall (constructorTypeIR × (_root_.List typeId))
  | Type_alpha (input0 : typeIR) (input1 : typeIR) : SpecTecCall _root_.Unit
  | «Type_alpha:tupleTypeIR:iter:2» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Type_alpha:structTypeIR:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeArgumentIR)) : SpecTecCall _root_.Unit
  | «Type_alpha:headerTypeIR:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeArgumentIR)) : SpecTecCall _root_.Unit
  | «Type_alpha:headerUnionTypeIR:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeArgumentIR)) : SpecTecCall _root_.Unit
  | «Type_alpha:externObjectTypeIR:iter:2» (input0 : (_root_.List typeArgumentIR)) (input1 : (_root_.List typeArgumentIR)) : SpecTecCall _root_.Unit
  | «Type_alpha:parserObjectTypeIR:iter:2» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «Type_alpha:controlObjectTypeIR:iter:2» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «Type_alpha:packageObjectTypeIR:iter:2» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Type_alpha:non-default:iter:2» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Type_alpha:default:iter:2» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Type_alpha:non-default_2:iter:8» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Type_alpha:default_2:iter:8» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | ParameterType_alpha (input0 : parameterIR) (input1 : parameterIR) : SpecTecCall _root_.Unit
  | «ExternMethodType_alpha:non-abstract:iter:0» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «ExternMethodType_alpha:abstract:iter:0» (input0 : (_root_.List parameterIR)) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | ExternMethodType_alpha (input0 : externMethodTypeIR) (input1 : externMethodTypeIR) : SpecTecCall _root_.Unit
  | ExternMethodTypeDef_alpha (input0 : externMethodTypeDefIR) (input1 : externMethodTypeDefIR) : SpecTecCall _root_.Unit
  | «$add_var_t» (input0 : cursor) (input1 : typingContext) (input2 : id) (input3 : varTypeIR) : SpecTecCall typingContext
  | «$add_vars_t» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List id)) (input3 : (_root_.List varTypeIR)) : SpecTecCall typingContext
  | «$add_parameter_t» (input0 : cursor) (input1 : typingContext) (input2 : parameterIR) : SpecTecCall typingContext
  | «$add_parameters_t» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List parameterIR)) : SpecTecCall typingContext
  | «$add_constructorParameter_t» (input0 : typingContext) (input1 : parameterIR) : SpecTecCall typingContext
  | «$add_constructorParameters_t» (input0 : typingContext) (input1 : (_root_.List parameterIR)) : SpecTecCall typingContext
  | «$update_mode_tbl» (input0 : tableContext) (input1 : (_root_.List tableKeyIR)) : SpecTecCall tableContext
  | Type_wf (input0 : bound) (input1 : typeIR) : SpecTecCall _root_.Unit
  | «Type_wf:tupleTypeIR:iter:3» (input0 : bound) (input1 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Type_wf:structTypeIR:iter:6» (input0 : bound) (input1 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Type_wf:headerTypeIR:iter:6» (input0 : bound) (input1 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Type_wf:headerUnionTypeIR:iter:6» (input0 : bound) (input1 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Type_wf:externObjectTypeIR:iter:3» (input0 : bound) (input1 : (_root_.List externMethodTypeDefIR)) : SpecTecCall _root_.Unit
  | «Type_wf:parserObjectTypeIR:iter:1» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «Type_wf:controlObjectTypeIR:iter:1» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «Type_wf:packageObjectTypeIR:iter:1» (input0 : bound) (input1 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Type_wf:non-default:iter:1» (input0 : bound) (input1 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Type_wf:default:iter:1» (input0 : bound) (input1 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Type_wf:non-default_2:iter:4» (input0 : bound) (input1 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | «Type_wf:default_2:iter:4» (input0 : bound) (input1 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | ParameterType_wf (input0 : bound) (input1 : parameterIR) : SpecTecCall _root_.Unit
  | ReturnType_wf (input0 : bound) (input1 : typeIR) : SpecTecCall _root_.Unit
  | CallableType_wf (input0 : bound) (input1 : callableTypeIR) : SpecTecCall _root_.Unit
  | «CallableType_wf:actionTypeIR:iter:1» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «CallableType_wf:definedFunctionTypeIR:iter:1» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «CallableType_wf:externFunctionTypeIR:iter:1» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «CallableType_wf:non-abstract:iter:1» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «CallableType_wf:abstract:iter:1» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «CallableType_wf:parserApplyMethodTypeIR:iter:1» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «CallableType_wf:controlApplyMethodTypeIR:iter:1» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | CallableTypeDef_wf (input0 : bound) (input1 : callableTypeDefIR) : SpecTecCall _root_.Unit
  | TypeDef_wf (input0 : bound) (input1 : typeDefIR) : SpecTecCall _root_.Unit
  | ConstructorParameterType_wf (input0 : bound) (input1 : parameterIR) : SpecTecCall _root_.Unit
  | «ConstructorType_wf:externObjectTypeIR:iter:0» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «ConstructorType_wf:parserObjectTypeIR:iter:0» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «ConstructorType_wf:controlObjectTypeIR:iter:0» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | «ConstructorType_wf:packageObjectTypeIR:iter:0» (input0 : bound) (input1 : (_root_.List parameterIR)) : SpecTecCall _root_.Unit
  | ConstructorType_wf (input0 : bound) (input1 : constructorTypeIR) : SpecTecCall _root_.Unit
  | ConstructorTypeDef_wf (input0 : bound) (input1 : constructorTypeDefIR) : SpecTecCall _root_.Unit
  | Cast_impl (input0 : typeIR) (input1 : typeIR) : SpecTecCall castResult
  | Cast_impl_neq (input0 : typeIR) (input1 : typeIR) : SpecTecCall castResult
  | «Cast_impl_neq:listTypeIR:iter:2» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_impl_neq:tupleTypeIR:iter:2» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_impl_neq:arrayTypeIR:iter:2» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_impl_neq:headerStackTypeIR:iter:2» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_impl_neq:structTypeIR:iter:4» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_impl_neq:headerTypeIR_2:iter:4» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_impl_neq:sequenceTypeIR:iter:2» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_impl_neq:tupleTypeIR_2:iter:3» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_impl_neq:arrayTypeIR_2:iter:2» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_impl_neq:headerStackTypeIR_2:iter:2» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_impl_neq:structTypeIR_2:iter:5» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_impl_neq:headerTypeIR_3:iter:5» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_impl_neq:structTypeIR_3:iter:20» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_impl_neq:headerTypeIR_4:iter:20» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_impl_neq:structTypeIR_4:iter:20» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_impl_neq:headerTypeIR_5:iter:20» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | Cast_expl (input0 : typeIR) (input1 : typeIR) : SpecTecCall castResult
  | Cast_expl_neq (input0 : typeIR) (input1 : typeIR) : SpecTecCall castResult
  | «Cast_expl_neq:listTypeIR:iter:2» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_expl_neq:tupleTypeIR:iter:2» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_expl_neq:arrayTypeIR:iter:2» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_expl_neq:headerStackTypeIR:iter:2» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_expl_neq:structTypeIR:iter:4» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_expl_neq:headerTypeIR_2:iter:4» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_expl_neq:tupleTypeIR_2:iter:3» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_expl_neq:arrayTypeIR_2:iter:2» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_expl_neq:headerStackTypeIR_2:iter:2» (input0 : typeIR) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_expl_neq:structTypeIR_2:iter:5» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_expl_neq:headerTypeIR_3:iter:5» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_expl_neq:structTypeIR_3:iter:20» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_expl_neq:headerTypeIR_4:iter:20» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_expl_neq:structTypeIR_4:iter:20» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «Cast_expl_neq:headerTypeIR_5:iter:20» (input0 : (_root_.List typeIR)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List castResult)
  | «ParserSelect_ok:rule:iter:6» (input0 : typingContext) (input1 : (_root_.List typeIR)) : SpecTecCall _root_.Unit
  | TableType_ok (input0 : typingContext) (input1 : tableContext) (input2 : name) : SpecTecCall (typingContext × typeIR)
  | CallableType_ok (input0 : cursor) (input1 : typingContext) (input2 : callableTargetIR) (input3 : typeArgumentListIR) (input4 : (_root_.List argumentIR)) : SpecTecCall (callableTypeIR × ((_root_.List typeId) × ((_root_.List id) × (_root_.List id))))
  | «Call_ok:definedFunctionTypeIR:iter:3» (input0 : inference) (input1 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List typeArgumentIR)
  | «Call_ok:definedFunctionTypeIR:iter:5» (input0 : inference) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «Call_ok:externFunctionTypeIR:iter:3» (input0 : inference) (input1 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List typeArgumentIR)
  | «Call_ok:externFunctionTypeIR:iter:5» (input0 : inference) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «Call_ok:non-abstract:iter:3» (input0 : inference) (input1 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List typeArgumentIR)
  | «Call_ok:non-abstract:iter:5» (input0 : inference) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «Call_ok:abstract:iter:3» (input0 : inference) (input1 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List typeArgumentIR)
  | «Call_ok:abstract:iter:5» (input0 : inference) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «Inst_ok:package:iter:2» (input0 : inference) (input1 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List typeArgumentIR)
  | «Inst_ok:package:iter:4» (input0 : inference) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «Inst_ok:non-package:iter:2» (input0 : inference) (input1 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List typeArgumentIR)
  | «Inst_ok:non-package:iter:4» (input0 : inference) (input1 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameterIR)
  | «$reduce_serenum» (input0 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | «ParserSelect_ok:rule:iter:2» (input0 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List typedExpressionIR)
  | «$reduce_serenum_unary» (input0 : typedExpressionIR) (input1 : (typeIR → (SpecTecCall _root_.Bool))) : SpecTecCall (_root_.Option typedExpressionIR)
  | «$reduce_serenum_binary» (input0 : typedExpressionIR) (input1 : typedExpressionIR) (input2 : (typeIR → typeIR → (SpecTecCall _root_.Bool))) : SpecTecCall (_root_.Option (typedExpressionIR × typedExpressionIR))
  | «$cast_unary» (input0 : typedExpressionIR) (input1 : typeIR) : SpecTecCall (_root_.Option typedExpressionIR)
  | «$cast_binary» (input0 : typedExpressionIR) (input1 : typedExpressionIR) : SpecTecCall (_root_.Option (typedExpressionIR × typedExpressionIR))
  | «$result_concat» (input0 : typeIR) (input1 : typeIR) : SpecTecCall typeIR
  | «$is_valid_bitslice» (input0 : typeIR) (input1 : _root_.Nat) (input2 : _root_.Nat) : SpecTecCall _root_.Bool
  | «$is_concrete_extern_object» (input0 : typeIR) : SpecTecCall _root_.Bool
  | «$subst_externMethodTypeDefEnv» (input0 : externMethodTypeDefEnv) (input1 : externMethodTypeDefEnv) : SpecTecCall externMethodTypeDefEnv
  | «$is_table_application» (input0 : typedExpressionIR) : SpecTecCall _root_.Bool
  | «Call_action_partial_ok:rule:iter:2» (input0 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «Call_action_default_ok:rule:iter:2» (input0 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List _root_.Bool)
  | «$resolve_inference'» (input0 : typeIR) : SpecTecCall typeIR
  | «$resolve_inference:case_1:iter:2» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List typeIR)
  | «$resolve_inference» (input0 : inference) : SpecTecCall inference
  | «$merge_constraint'» (input0 : constraint) (input1 : constraint) (input2 : (_root_.List typeId)) (input3 : constraint) : SpecTecCall constraint
  | «$merge_constraint» (input0 : constraint) (input1 : constraint) : SpecTecCall constraint
  | «$merge_constraints» (input0 : constraint) (input1 : (_root_.List constraint)) : SpecTecCall constraint
  | «$gen_constraint» (input0 : constraint) (input1 : (_root_.List typeIR)) (input2 : (_root_.List typeIR)) : SpecTecCall constraint
  | «$gen_constraint:case_1:iter:0» (input0 : constraint) (input1 : (_root_.List typeIR)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List constraint)
  | «$gen_constraint_pair» (input0 : constraint) (input1 : typeIR) (input2 : typeIR) : SpecTecCall constraint
  | «$infer_pair» (input0 : constraint) (input1 : parameterIR) (input2 : argumentIR) : SpecTecCall constraint
  | «$infer:case_2:iter:6» (input0 : constraint) (input1 : (_root_.List argumentIR)) (input2 : (_root_.List parameterIR)) : SpecTecCall (_root_.List constraint)
  | «$infer» (input0 : (_root_.List typeId)) (input1 : (_root_.List parameterIR)) (input2 : (_root_.List parameterIR)) (input3 : (_root_.List argumentIR)) : SpecTecCall inference
  | «$resolve_type_alias» (input0 : typeIR) : SpecTecCall (nameIR × (_root_.List typeIR))
  | ConstructorType_ok (input0 : cursor) (input1 : typingContext) (input2 : constructorTargetIR) (input3 : (_root_.List argumentIR)) : SpecTecCall (constructorTypeIR × ((_root_.List typeId) × ((_root_.List id) × (_root_.List id))))
  | «$instantiable» (input0 : cursor) (input1 : typingContext) (input2 : instctxt) (input3 : typeIR) : SpecTecCall _root_.Bool
  | «$subst_type_i» (input0 : cursor) (input1 : instContext) (input2 : typeIR) : SpecTecCall typeIR
  | Constructor_inst (input0 : cursor) (input1 : instContext) (input2 : prefixedNameIR) (input3 : typeArgumentListIR) (input4 : argumentListIR) : SpecTecCall (constructorDef × (typeArgumentListIR × ((_root_.List id) × (_root_.List id))))
  | «$subst_type_e» (input0 : cursor) (input1 : evalContext) (input2 : typeIR) : SpecTecCall typeIR
  | «$V1Model_setup_packet_in_argument» (input0 : evalContext) : SpecTecCall argumentIR
  | «$V1Model_setup_packet_out_argument» (input0 : evalContext) : SpecTecCall argumentIR
  | «$V1Model_setup_standard_metadata_argument» (input0 : evalContext) : SpecTecCall argumentIR
  | «$V1Model_setup_main_callee» (input0 : evalContext) (input1 : arch) : SpecTecCall typedExpressionIR
  | «$V1Model_setup_parser_callee» (input0 : evalContext) (input1 : arch) (input2 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | «$V1Model_setup_verify_callee» (input0 : evalContext) (input1 : arch) (input2 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | «$V1Model_setup_ingress_callee» (input0 : evalContext) (input1 : arch) (input2 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | «$V1Model_setup_egress_callee» (input0 : evalContext) (input1 : arch) (input2 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | «$V1Model_setup_check_callee» (input0 : evalContext) (input1 : arch) (input2 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | «$V1Model_setup_deparse_callee» (input0 : evalContext) (input1 : arch) (input2 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | «$eBPF_setup_packet_in_argument» (input0 : evalContext) : SpecTecCall argumentIR
  | «$eBPF_setup_main_callee» (input0 : evalContext) (input1 : arch) : SpecTecCall typedExpressionIR
  | «$eBPF_setup_parse_callee» (input0 : evalContext) (input1 : arch) (input2 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | «$eBPF_setup_filter_callee» (input0 : evalContext) (input1 : arch) (input2 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | «$PSA_setup_main_callee» (input0 : evalContext) (input1 : arch) : SpecTecCall typedExpressionIR
  | «$PSA_setup_ingress_packet_in_argument» (input0 : evalContext) : SpecTecCall argumentIR
  | «$PSA_setup_ingress_packet_out_argument» (input0 : evalContext) : SpecTecCall argumentIR
  | «$PSA_setup_ingress_parser_input_metadata_argument» (input0 : evalContext) : SpecTecCall argumentIR
  | «$PSA_setup_ingress_input_metadata_argument» (input0 : evalContext) : SpecTecCall argumentIR
  | «$PSA_setup_ingress_output_metadata_argument» (input0 : evalContext) : SpecTecCall argumentIR
  | «$PSA_setup_ingress_pipeline_callee» (input0 : evalContext) (input1 : arch) (input2 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | «$PSA_setup_ingress_parser_callee» (input0 : evalContext) (input1 : arch) (input2 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | «$PSA_setup_ingress_callee» (input0 : evalContext) (input1 : arch) (input2 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | «$PSA_setup_ingress_deparser_callee» (input0 : evalContext) (input1 : arch) (input2 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | «$PSA_setup_egress_packet_in_argument» (input0 : evalContext) : SpecTecCall argumentIR
  | «$PSA_setup_egress_packet_out_argument» (input0 : evalContext) : SpecTecCall argumentIR
  | «$PSA_setup_egress_parser_input_metadata_argument» (input0 : evalContext) : SpecTecCall argumentIR
  | «$PSA_setup_egress_input_metadata_argument» (input0 : evalContext) : SpecTecCall argumentIR
  | «$PSA_setup_egress_output_metadata_argument» (input0 : evalContext) : SpecTecCall argumentIR
  | «$PSA_setup_egress_deparser_input_metadata_argument» (input0 : evalContext) : SpecTecCall argumentIR
  | «$PSA_setup_egress_pipeline_callee» (input0 : evalContext) (input1 : arch) (input2 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | «$PSA_setup_egress_parser_callee» (input0 : evalContext) (input1 : arch) (input2 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | «$PSA_setup_egress_callee» (input0 : evalContext) (input1 : arch) (input2 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | «$PSA_setup_egress_deparser_callee» (input0 : evalContext) (input1 : arch) (input2 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | «$sizeof_minSizeInBits'» (input0 : typeIR) : SpecTecCall _root_.Nat
  | «$sizeof_minSizeInBits':case_8:iter:1» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Nat)
  | «$sizeof_minSizeInBits':case_11:iter:3» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Nat)
  | «$sizeof_minSizeInBits':case_12:iter:3» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Nat)
  | «$sizeof_minSizeInBits':case_13:iter:3» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Nat)
  | «$sizeof_minSizeInBits» (input0 : typeIR) : SpecTecCall value
  | «$sizeof_minSizeInBytes» (input0 : typeIR) : SpecTecCall value
  | «$sizeof_maxSizeInBits'» (input0 : typeIR) : SpecTecCall _root_.Nat
  | «$sizeof_maxSizeInBits':case_8:iter:1» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Nat)
  | «$sizeof_maxSizeInBits':case_11:iter:3» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Nat)
  | «$sizeof_maxSizeInBits':case_12:iter:3» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Nat)
  | «$sizeof_maxSizeInBits':case_13:iter:3» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List _root_.Nat)
  | «$sizeof_maxSizeInBits» (input0 : typeIR) : SpecTecCall value
  | «$sizeof_maxSizeInBytes» (input0 : typeIR) : SpecTecCall value
  | «$sizeof» (input0 : typeIR) (input1 : id) : SpecTecCall value
  | «$lift_typeIR» (input0 : typeIR) : SpecTecCall type
  | «$lift_typeArgumentListIR» (input0 : (_root_.List typeArgumentIR)) : SpecTecCall typeArgumentList
  | «$lift_typeArgumentListIR:case_1:iter:0» (input0 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List typeArgument)
  | «$lift_typeArgumentIR» (input0 : typeArgumentIR) : SpecTecCall typeArgument
  | «$lift_dataTypeIR» (input0 : dataTypeIR) : SpecTecCall type
  | «$lift_typeArgumentIR_as_realTypeArgument» (input0 : typeArgumentIR) : SpecTecCall realTypeArgument
  | «$lift_typeIR_as_typeOrVoid» (input0 : typeIR) : SpecTecCall typeOrVoid
  | «$lift_parameterIR» (input0 : parameterIR) : SpecTecCall parameter
  | «$lift_parameterListIR:case_1:iter:0» (input0 : (_root_.List parameterIR)) : SpecTecCall (_root_.List parameter)
  | «$lift_parameterListIR» (input0 : (_root_.List parameterIR)) : SpecTecCall parameterList
  | «$lift_constructorParameterIR» (input0 : constructorParameterIR) : SpecTecCall constructorParameter
  | «$lift_constructorParameterListIR:case_1:iter:0» (input0 : (_root_.List constructorParameterIR)) : SpecTecCall (_root_.List constructorParameter)
  | «$lift_constructorParameterListIR» (input0 : (_root_.List constructorParameterIR)) : SpecTecCall constructorParameterListOpt
  | «$lift_typeArgumentListIR_as_realTypeArgumentList:case_1:iter:0» (input0 : (_root_.List typeArgumentIR)) : SpecTecCall (_root_.List realTypeArgument)
  | «$lift_typeArgumentListIR_as_realTypeArgumentList» (input0 : (_root_.List typeArgumentIR)) : SpecTecCall realTypeArgumentList
  | «$lift_typedExpressionIR» (input0 : typedExpressionIR) : SpecTecCall expression
  | «$lift_namedExpressionIR» (input0 : namedExpressionIR) : SpecTecCall namedExpression
  | «$lift_typedExpressionListIR» (input0 : (_root_.List typedExpressionIR)) : SpecTecCall expressionList
  | «$lift_typedExpressionListIR:case_1:iter:0» (input0 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List expression)
  | «$lift_unaryExpressionIR» (input0 : unaryExpressionIR) : SpecTecCall unaryExpression
  | «$lift_binaryExpressionIR» (input0 : binaryExpressionIR) : SpecTecCall binaryExpression
  | «$lift_ternaryExpressionIR» (input0 : ternaryExpressionIR) : SpecTecCall ternaryExpression
  | «$lift_castExpressionIR» (input0 : castExpressionIR) : SpecTecCall expression
  | «$lift_dataExpressionIR» (input0 : dataExpressionIR) : SpecTecCall dataExpression
  | «$lift_dataExpressionIR:case_3:iter:1» (input0 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List expression)
  | «$lift_dataExpressionIR:case_4:iter:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecCall (_root_.List namedExpression)
  | «$lift_dataExpressionIR:case_5:iter:1» (input0 : (_root_.List namedExpressionIR)) : SpecTecCall (_root_.List namedExpression)
  | «$lift_memberAccessBaseIR» (input0 : memberAccessBaseIR) : SpecTecCall memberAccessBase
  | «$lift_memberAccessExpressionIR» (input0 : memberAccessExpressionIR) : SpecTecCall memberAccessExpression
  | «$lift_indexAccessExpressionIR» (input0 : indexAccessExpressionIR) : SpecTecCall indexAccessExpression
  | «$lift_sliceAccessExpressionIR» (input0 : sliceAccessExpressionIR) : SpecTecCall sliceAccessExpression
  | «$lift_accessExpressionIR» (input0 : accessExpressionIR) : SpecTecCall accessExpression
  | «$lift_argumentListIR» (input0 : (_root_.List argumentIR)) : SpecTecCall argumentList
  | «$lift_argumentListIR:case_1:iter:0» (input0 : (_root_.List argumentIR)) : SpecTecCall (_root_.List argument)
  | «$lift_callableTargetIR_as_expression» (input0 : callableTargetIR) : SpecTecCall expression
  | «$lift_callExpressionIR» (input0 : callExpressionIR) : SpecTecCall callExpression
  | «$lift_parenthesizedExpressionIR» (input0 : parenthesizedExpressionIR) : SpecTecCall parenthesizedExpression
  | «$lift_expressionIR» (input0 : expressionIR) : SpecTecCall expression
  | «$lift_argumentIR» (input0 : argumentIR) : SpecTecCall argument
  | «$lift_initializerIR» (input0 : initializerIR) : SpecTecCall initializer
  | «$lift_initializerOptIR» (input0 : (_root_.Option initializerIR)) : SpecTecCall initializerOpt
  | «$lift_namedExpressionListIR:case_1:iter:0» (input0 : (_root_.List namedExpressionIR)) : SpecTecCall (_root_.List namedExpression)
  | «$lift_namedExpressionListIR» (input0 : (_root_.List namedExpressionIR)) : SpecTecCall namedExpressionList
  | «$lift_simpleKeysetExpressionIR» (input0 : simpleKeysetExpressionIR) : SpecTecCall simpleKeysetExpression
  | «$lift_simpleKeysetExpressionListIR:case_1:iter:0» (input0 : (_root_.List simpleKeysetExpressionIR)) : SpecTecCall (_root_.List simpleKeysetExpression)
  | «$lift_simpleKeysetExpressionListIR» (input0 : (_root_.List simpleKeysetExpressionIR)) : SpecTecCall simpleKeysetExpressionList
  | «$lift_tupleKeysetExpressionIR» (input0 : tupleKeysetExpressionIR) : SpecTecCall tupleKeysetExpression
  | «$lift_keysetExpressionIR» (input0 : keysetExpressionIR) : SpecTecCall keysetExpression
  | «$lift_typedLvalueIR» (input0 : typedLvalueIR) : SpecTecCall lvalue
  | «$lift_assignmentStatementIR» (input0 : assignmentStatementIR) : SpecTecCall assignmentStatement
  | «$lift_callableTargetIR_as_lvalue» (input0 : callableTargetIR) : SpecTecCall lvalue
  | «$lift_callStatementIR» (input0 : callStatementIR) : SpecTecCall callStatement
  | «$lift_directApplicationStatementIR» (input0 : directApplicationStatementIR) : SpecTecCall directApplicationStatement
  | «$lift_returnStatementIR» (input0 : returnStatementIR) : SpecTecCall returnStatement
  | «$lift_constantDeclarationIR» (input0 : constantDeclarationIR) : SpecTecCall constantDeclaration
  | «$lift_variableDeclarationIR» (input0 : variableDeclarationIR) : SpecTecCall variableDeclaration
  | «$lift_switchLabelIR» (input0 : switchLabelIR) : SpecTecCall switchLabel
  | «$lift_statementIR» (input0 : statementIR) : SpecTecCall statement
  | «$lift_blockElementStatementIR» (input0 : blockElementStatementIR) : SpecTecCall blockElementStatement
  | «$lift_blockStatementIR» (input0 : blockStatementIR) : SpecTecCall blockStatement
  | «$lift_blockStatementIR:case_1:iter:0» (input0 : (_root_.List blockElementStatementIR)) : SpecTecCall (_root_.List blockElementStatement)
  | «$lift_conditionalStatementIR» (input0 : conditionalStatementIR) : SpecTecCall conditionalStatement
  | «$lift_switchCaseIR» (input0 : switchCaseIR) : SpecTecCall switchCase
  | «$lift_switchCaseListIR» (input0 : (_root_.List switchCaseIR)) : SpecTecCall switchCaseList
  | «$lift_switchCaseListIR:case_1:iter:0» (input0 : (_root_.List switchCaseIR)) : SpecTecCall (_root_.List switchCase)
  | «$lift_switchStatementIR» (input0 : switchStatementIR) : SpecTecCall switchStatement
  | «$lift_blockElementStatementListIR:case_1:iter:0» (input0 : (_root_.List blockElementStatementIR)) : SpecTecCall (_root_.List blockElementStatement)
  | «$lift_blockElementStatementListIR» (input0 : (_root_.List blockElementStatementIR)) : SpecTecCall blockElementStatementList
  | «$lift_functionPrototypeIR» (input0 : functionPrototypeIR) : SpecTecCall functionPrototype
  | «$lift_functionDeclarationIR» (input0 : functionDeclarationIR) : SpecTecCall functionDeclaration
  | «$lift_actionDeclarationIR» (input0 : actionDeclarationIR) : SpecTecCall actionDeclaration
  | «$lift_objectDeclarationIR» (input0 : objectDeclarationIR) : SpecTecCall objectDeclaration
  | «$lift_objectDeclarationListIR» (input0 : (_root_.List objectDeclarationIR)) : SpecTecCall objectDeclarationList
  | «$lift_objectDeclarationListIR:case_1:iter:0» (input0 : (_root_.List objectDeclarationIR)) : SpecTecCall (_root_.List objectDeclaration)
  | «$lift_instantiationIR» (input0 : instantiationIR) : SpecTecCall instantiation
  | «$lift_enumTypeDeclarationIR» (input0 : enumTypeDeclarationIR) : SpecTecCall enumTypeDeclaration
  | «$lift_typeFieldIR» (input0 : typeFieldIR) : SpecTecCall typeField
  | «$lift_typeFieldListIR:case_1:iter:0» (input0 : (_root_.List typeFieldIR)) : SpecTecCall (_root_.List typeField)
  | «$lift_typeFieldListIR» (input0 : (_root_.List typeFieldIR)) : SpecTecCall typeFieldList
  | «$lift_structTypeDeclarationIR» (input0 : structTypeDeclarationIR) : SpecTecCall structTypeDeclaration
  | «$lift_headerTypeDeclarationIR» (input0 : headerTypeDeclarationIR) : SpecTecCall headerTypeDeclaration
  | «$lift_headerUnionTypeDeclarationIR» (input0 : headerUnionTypeDeclarationIR) : SpecTecCall headerUnionTypeDeclaration
  | «$lift_derivedTypeDeclarationIR» (input0 : derivedTypeDeclarationIR) : SpecTecCall derivedTypeDeclaration
  | «$lift_externFunctionDeclarationIR» (input0 : externFunctionDeclarationIR) : SpecTecCall externFunctionDeclaration
  | «$lift_externConstructorPrototypeIR» (input0 : externConstructorPrototypeIR) : SpecTecCall externConstructorPrototype
  | «$lift_externMethodPrototypeIR» (input0 : externMethodPrototypeIR) : SpecTecCall externMethodPrototype
  | «$lift_externObjectDeclarationIR:case_1:iter:2» (input0 : (_root_.List externConstructorPrototypeIR)) : SpecTecCall (_root_.List externConstructorPrototype)
  | «$lift_externObjectDeclarationIR:case_1:iter:4» (input0 : (_root_.List externMethodPrototypeIR)) : SpecTecCall (_root_.List externMethodPrototype)
  | «$lift_externObjectDeclarationIR» (input0 : externObjectDeclarationIR) : SpecTecCall externObjectDeclaration
  | «$lift_externDeclarationIR» (input0 : externDeclarationIR) : SpecTecCall externDeclaration
  | «$lift_selectCaseIR» (input0 : selectCaseIR) : SpecTecCall selectCase
  | «$lift_selectCaseListIR:case_1:iter:0» (input0 : (_root_.List selectCaseIR)) : SpecTecCall (_root_.List selectCase)
  | «$lift_selectCaseListIR» (input0 : (_root_.List selectCaseIR)) : SpecTecCall selectCaseList
  | «$lift_selectExpressionIR» (input0 : selectExpressionIR) : SpecTecCall selectExpression
  | «$lift_stateExpressionIR» (input0 : stateExpressionIR) : SpecTecCall stateExpression
  | «$lift_transitionStatementIR» (input0 : transitionStatementIR) : SpecTecCall transitionStatement
  | «$lift_typeIR_as_valueSetType» (input0 : typeIR) : SpecTecCall valueSetType
  | «$lift_valueSetDeclarationIR» (input0 : valueSetDeclarationIR) : SpecTecCall valueSetDeclaration
  | «$lift_parserTypeDeclarationIR» (input0 : parserTypeDeclarationIR) : SpecTecCall parserTypeDeclaration
  | «$lift_parserStatementIR» (input0 : parserStatementIR) : SpecTecCall parserStatement
  | «$lift_parserBlockElementStatementIR» (input0 : parserBlockElementStatementIR) : SpecTecCall parserBlockElementStatement
  | «$lift_parserBlockElementStatementListIR» (input0 : (_root_.List parserBlockElementStatementIR)) : SpecTecCall parserBlockElementStatementList
  | «$lift_parserBlockElementStatementListIR:case_1:iter:0» (input0 : (_root_.List parserBlockElementStatementIR)) : SpecTecCall (_root_.List parserBlockElementStatement)
  | «$lift_parserBlockStatementIR» (input0 : parserBlockStatementIR) : SpecTecCall parserBlockStatement
  | «$lift_parserConditionalStatementIR» (input0 : parserConditionalStatementIR) : SpecTecCall parserConditionalStatement
  | «$lift_parserStateIR» (input0 : parserStateIR) : SpecTecCall parserState
  | «$lift_parserStateListIR:case_1:iter:0» (input0 : (_root_.List parserStateIR)) : SpecTecCall (_root_.List parserState)
  | «$lift_parserStateListIR» (input0 : (_root_.List parserStateIR)) : SpecTecCall parserStateList
  | «$lift_parserLocalDeclarationIR» (input0 : parserLocalDeclarationIR) : SpecTecCall parserLocalDeclaration
  | «$lift_parserLocalDeclarationListIR:case_1:iter:0» (input0 : (_root_.List parserLocalDeclarationIR)) : SpecTecCall (_root_.List parserLocalDeclaration)
  | «$lift_parserLocalDeclarationListIR» (input0 : (_root_.List parserLocalDeclarationIR)) : SpecTecCall parserLocalDeclarationList
  | «$lift_parserDeclarationIR» (input0 : parserDeclarationIR) : SpecTecCall parserDeclaration
  | «$lift_tableKeyIR» (input0 : tableKeyIR) : SpecTecCall tableKey
  | «$lift_tableKeyListIR:case_1:iter:0» (input0 : (_root_.List tableKeyIR)) : SpecTecCall (_root_.List tableKey)
  | «$lift_tableKeyListIR» (input0 : (_root_.List tableKeyIR)) : SpecTecCall tableKeyList
  | «$lift_tableActionReferenceIR» (input0 : tableActionReferenceIR) : SpecTecCall tableActionReference
  | «$lift_tableActionReferenceIR_as_expression» (input0 : tableActionReferenceIR) : SpecTecCall expression
  | «$lift_tableActionIR» (input0 : tableActionIR) : SpecTecCall tableAction
  | «$lift_tableActionListIR:case_1:iter:0» (input0 : (_root_.List tableActionIR)) : SpecTecCall (_root_.List tableAction)
  | «$lift_tableActionListIR» (input0 : (_root_.List tableActionIR)) : SpecTecCall tableActionList
  | «$lift_tableEntryIR» (input0 : tableEntryIR) : SpecTecCall tableEntry
  | «$lift_tableEntryListIR:case_1:iter:0» (input0 : (_root_.List tableEntryIR)) : SpecTecCall (_root_.List tableEntry)
  | «$lift_tableEntryListIR» (input0 : (_root_.List tableEntryIR)) : SpecTecCall tableEntryList
  | «$lift_tableCustomPropertyIR» (input0 : tableCustomPropertyIR) : SpecTecCall tableProperty
  | «$lift_tableKeysPropertyIR» (input0 : tableKeysPropertyIR) : SpecTecCall tableProperty
  | «$lift_tableActionsPropertyIR» (input0 : tableActionsPropertyIR) : SpecTecCall tableProperty
  | «$lift_tableDefaultActionPropertyIR» (input0 : tableDefaultActionPropertyIR) : SpecTecCall tableProperty
  | «$lift_tableEntriesPropertyIR» (input0 : tableEntriesPropertyIR) : SpecTecCall tableProperty
  | «$lift_tablePropertyIR» (input0 : tablePropertyIR) : SpecTecCall tableProperty
  | «$lift_tablePropertyListIR:case_1:iter:0» (input0 : (_root_.List tablePropertyIR)) : SpecTecCall (_root_.List tableProperty)
  | «$lift_tablePropertyListIR» (input0 : (_root_.List tablePropertyIR)) : SpecTecCall tablePropertyList
  | «$lift_tableDeclarationIR» (input0 : tableDeclarationIR) : SpecTecCall tableDeclaration
  | «$lift_controlTypeDeclarationIR» (input0 : controlTypeDeclarationIR) : SpecTecCall controlTypeDeclaration
  | «$lift_controlBodyIR» (input0 : controlBodyIR) : SpecTecCall controlBody
  | «$lift_controlLocalDeclarationIR» (input0 : controlLocalDeclarationIR) : SpecTecCall controlLocalDeclaration
  | «$lift_controlLocalDeclarationListIR:case_1:iter:0» (input0 : (_root_.List controlLocalDeclarationIR)) : SpecTecCall (_root_.List controlLocalDeclaration)
  | «$lift_controlLocalDeclarationListIR» (input0 : (_root_.List controlLocalDeclarationIR)) : SpecTecCall controlLocalDeclarationList
  | «$lift_controlDeclarationIR» (input0 : controlDeclarationIR) : SpecTecCall controlDeclaration
  | «$lift_packageTypeDeclarationIR» (input0 : packageTypeDeclarationIR) : SpecTecCall packageTypeDeclaration
  | «$flatten_typeParameterList» (input0 : typeParameterList) : SpecTecCall (_root_.List typeParameter)
  | «$flatten_typeParameterListOpt» (input0 : typeParameterListOpt) : SpecTecCall (_root_.List typeParameter)
  | TypeParameterListOpt_ok (input0 : cursor) (input1 : typingContext) (input2 : typeParameterListOpt) : SpecTecCall (typingContext × (_root_.List typeId))
  | «$lift_typedefIR» (input0 : typedefIR) : SpecTecCall typedef
  | «$lift_typedefDeclarationIR» (input0 : typedefDeclarationIR) : SpecTecCall typedefDeclaration
  | «$lift_typeDeclarationIR» (input0 : typeDeclarationIR) : SpecTecCall typeDeclaration
  | «$lift_declarationIR» (input0 : declarationIR) : SpecTecCall declaration
  | «$lift_p4programIR:case_1:iter:0» (input0 : (_root_.List declarationIR)) : SpecTecCall (_root_.List declaration)
  | «$lift_p4programIR» (input0 : p4programIR) : SpecTecCall p4program
  | «$un_lnot» (input0 : value) : SpecTecCall value
  | «$largest_priority_wins» (input0 : tableObjectProperty) : SpecTecCall _root_.Bool
  | «$select_action» (input0 : tableObjectProperty) (input1 : (_root_.List tableMatch)) : SpecTecCall tableActionReferenceIR
  | «$cast_control_plane:case_3:iter:4» (input0 : (_root_.List value)) : SpecTecCall (_root_.List _root_.Bool)
  | «$cast_control_plane» (input0 : evalContext) (input1 : typedExpressionIR) (input2 : typeIR) : SpecTecCall (_root_.Option typedExpressionIR)
  | «$tableObject_create_entry_key» (input0 : evalContext) (input1 : (nameIR × (nameIR × typeIR))) (input2 : tableKeysetInterface) : SpecTecCall simpleKeysetExpressionIR
  | «$tableObject_create_entry_keys» (input0 : evalContext) (input1 : (_root_.List (nameIR × (nameIR × typeIR)))) (input2 : tableKeysetInterface) : SpecTecCall (_root_.List simpleKeysetExpressionIR)
  | «$tableObject_create_entry_keyset» (input0 : evalContext) (input1 : tableKeysPropertyIR) (input2 : tableKeysetInterface) : SpecTecCall keysetExpressionIR
  | «$tableObject_create_entry_action:case_1:iter:4» (input0 : evalContext) (input1 : (_root_.List typeIR)) (input2 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List (_root_.Option typedExpressionIR))
  | «$tableObject_create_entry_action:case_2:iter:5» (input0 : evalContext) (input1 : (_root_.List typeIR)) (input2 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List (_root_.Option typedExpressionIR))
  | «$tableObject_create_entry_action» (input0 : evalContext) (input1 : tableActionsPropertyIR) (input2 : tableActionInterface) : SpecTecCall tableActionReferenceIR
  | «$tableObject_add_entry» (input0 : evalContext) (input1 : tableObject) (input2 : tableEntryPriorityInterface) (input3 : tableKeysetInterface) (input4 : tableActionInterface) : SpecTecCall (_root_.Option tableObject)
  | «$tableObject_add_default_action» (input0 : evalContext) (input1 : tableObject) (input2 : tableActionInterface) : SpecTecCall tableObject
  | «$update_headerUnion» (input0 : (_root_.List fieldValue)) (input1 : nameIR) : SpecTecCall (_root_.List fieldValue)
  | «$isValid_header» (input0 : value) : SpecTecCall _root_.Bool
  | «$invalidate_value» (input0 : value) : SpecTecCall value
  | «$invalidate_headerUnion» (input0 : headerUnionValue) : SpecTecCall headerUnionValue
  | «$invalidate_headerUnion:case_1:iter:2» (input0 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «Call_eval:cont:iter:5» (input0 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «Call_eval:cont-overflow:iter:5» (input0 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «Call_eval:cont_2:iter:5» (input0 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «Call_eval:cont-overflow_2:iter:5» (input0 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «Call_eval:builtinIsValidMethodCallee-header-union:iter:3» (input0 : (_root_.List value)) : SpecTecCall (_root_.List _root_.Bool)
  | «$un_bnot» (input0 : value) : SpecTecCall value
  | «$un_plus» (input0 : value) : SpecTecCall value
  | «$un_minus» (input0 : value) : SpecTecCall value
  | «$un_op» (input0 : unop) (input1 : value) : SpecTecCall value
  | «$bin_plus» (input0 : value) (input1 : value) : SpecTecCall value
  | «$bin_satplus» (input0 : value) (input1 : value) : SpecTecCall value
  | «$bin_minus» (input0 : value) (input1 : value) : SpecTecCall value
  | «$bin_satminus» (input0 : value) (input1 : value) : SpecTecCall value
  | «$bin_mul» (input0 : value) (input1 : value) : SpecTecCall value
  | «$bin_div» (input0 : value) (input1 : value) : SpecTecCall value
  | «$bin_mod» (input0 : value) (input1 : value) : SpecTecCall value
  | «$bin_shl» (input0 : value) (input1 : value) : SpecTecCall value
  | «$bin_shr» (input0 : value) (input1 : value) : SpecTecCall value
  | «$bin_le» (input0 : value) (input1 : value) : SpecTecCall _root_.Bool
  | «$bin_ge» (input0 : value) (input1 : value) : SpecTecCall _root_.Bool
  | «$bin_lt» (input0 : value) (input1 : value) : SpecTecCall _root_.Bool
  | «$bin_gt» (input0 : value) (input1 : value) : SpecTecCall _root_.Bool
  | «$bin_band» (input0 : value) (input1 : value) : SpecTecCall value
  | «$bin_bxor» (input0 : value) (input1 : value) : SpecTecCall value
  | «$bin_bor» (input0 : value) (input1 : value) : SpecTecCall value
  | «$tableEntry_lpm_prefix'» (input0 : value) (input1 : _root_.Nat) : SpecTecCall _root_.Nat
  | «$tableEntry_lpm_prefix» (input0 : value) : SpecTecCall _root_.Nat
  | «$bitacc_range_op» (input0 : value) (input1 : value) (input2 : value) : SpecTecCall value
  | «$bitacc_offset_op» (input0 : value) (input1 : value) (input2 : value) : SpecTecCall value
  | «$bitacc_range_replace_op» (input0 : value) (input1 : value) (input2 : value) (input3 : value) : SpecTecCall value
  | «$bitacc_offset_replace_op» (input0 : value) (input1 : value) (input2 : value) (input3 : value) : SpecTecCall value
  | «$bin_concat» (input0 : value) (input1 : value) : SpecTecCall value
  | «$write_value_from_bits'» (input0 : value) (input1 : _root_.Nat) (input2 : (_root_.List _root_.Bool)) : SpecTecCall (value × (_root_.List _root_.Bool))
  | «$write_values_from_bits'» (input0 : (_root_.List value)) (input1 : _root_.Nat) (input2 : (_root_.List _root_.Bool)) : SpecTecCall ((_root_.List value) × (_root_.List _root_.Bool))
  | «$write_value_fields_from_bits'» (input0 : (_root_.List fieldValue)) (input1 : _root_.Nat) (input2 : (_root_.List _root_.Bool)) : SpecTecCall ((_root_.List fieldValue) × (_root_.List _root_.Bool))
  | «$write_value_field_from_bits'» (input0 : fieldValue) (input1 : _root_.Nat) (input2 : (_root_.List _root_.Bool)) : SpecTecCall (fieldValue × (_root_.List _root_.Bool))
  | «$write_value_from_bits» (input0 : value) (input1 : _root_.Nat) (input2 : (_root_.List _root_.Bool)) : SpecTecCall value
  | «$write_bits_from_value» (input0 : value) : SpecTecCall (_root_.List _root_.Bool)
  | «$write_bits_from_value:case_5:iter:1» (input0 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.List _root_.Bool))
  | «$write_bits_from_value:case_6:iter:1» (input0 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.List _root_.Bool))
  | «$write_bits_from_value:case_7:iter:3» (input0 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.List _root_.Bool))
  | «$write_bits_from_value:case_8:iter:3» (input0 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.List _root_.Bool))
  | «$write_bits_from_value:case_10:iter:3» (input0 : (_root_.List value)) : SpecTecCall (_root_.List (_root_.List _root_.Bool))
  | Lvalue_read (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : storageReference) : SpecTecCall value
  | Lvalue_write (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : storageReference) (input4 : value) : SpecTecCall evalContext
  | Copy_out_argument (input0 : arch) (input1 : cursor) (input2 : evalContext) (input3 : parameterIR) (input4 : cursor) (input5 : evalContext) (input6 : (_root_.Option storageReference)) : SpecTecCall evalContext
  | Copy_out_inner (input0 : arch) (input1 : cursor) (input2 : evalContext) (input3 : parameterListIR) (input4 : cursor) (input5 : evalContext) (input6 : (_root_.List (_root_.Option storageReference))) : SpecTecCall evalContext
  | Copy_out (input0 : cursor) (input1 : arch) (input2 : cursor) (input3 : evalContext) (input4 : parameterListIR) (input5 : cursor) (input6 : evalContext) (input7 : (_root_.List (_root_.Option storageReference))) : SpecTecCall evalContext
  | V1Model_copy_meta_fields (input0 : evalContext) (input1 : evalContext) (input2 : arch) (input3 : (_root_.List nameIR)) : SpecTecCall evalContext
  | PSA_ingress_init_parser_input_metadata (input0 : evalContext) (input1 : arch) (input2 : _root_.Int) (input3 : _root_.String) : SpecTecCall evalContext
  | PSA_ingress_init_input_metadata (input0 : evalContext) (input1 : arch) (input2 : _root_.Int) (input3 : _root_.String) : SpecTecCall evalContext
  | PSA_ingress_init_output_metadata (input0 : evalContext) (input1 : arch) : SpecTecCall evalContext
  | PSA_ingress_init_metadata (input0 : evalContext) (input1 : arch) (input2 : _root_.Int) (input3 : _root_.String) : SpecTecCall evalContext
  | PSA_egress_init_parser_input_metadata (input0 : evalContext) (input1 : arch) (input2 : _root_.Int) (input3 : _root_.String) : SpecTecCall evalContext
  | PSA_egress_init_input_metadata (input0 : evalContext) (input1 : arch) (input2 : _root_.Int) (input3 : _root_.String) (input4 : _root_.Int) (input5 : _root_.Int) : SpecTecCall evalContext
  | PSA_egress_init_output_metadata (input0 : evalContext) (input1 : arch) : SpecTecCall evalContext
  | PSA_egress_init_deparser_input_metadata (input0 : evalContext) (input1 : arch) (input2 : _root_.Int) : SpecTecCall evalContext
  | PSA_egress_init_metadata (input0 : evalContext) (input1 : arch) (input2 : _root_.Int) (input3 : _root_.String) (input4 : _root_.Int) (input5 : _root_.Int) : SpecTecCall evalContext
  | «$bin_eq» (input0 : value) (input1 : value) : SpecTecCall _root_.Bool
  | «$bin_eq:case_9:iter:2» (input0 : (_root_.List value)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List _root_.Bool)
  | «$bin_eq:case_10:iter:2» (input0 : (_root_.List value)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List _root_.Bool)
  | «$bin_eq:case_11:iter:2» (input0 : (_root_.List value)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List _root_.Bool)
  | «$bin_eq:case_12:iter:2» (input0 : (_root_.List value)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List _root_.Bool)
  | «$bin_eq:case_13:iter:2» (input0 : (_root_.List value)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List _root_.Bool)
  | «$bin_eq:case_14:iter:4» (input0 : (_root_.List value)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List _root_.Bool)
  | «$bin_eq:case_15:iter:4» (input0 : (_root_.List value)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List _root_.Bool)
  | «$bin_eq:case_16:iter:4» (input0 : (_root_.List value)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List _root_.Bool)
  | «$bin_ne» (input0 : value) (input1 : value) : SpecTecCall _root_.Bool
  | «$bin_op» (input0 : binop) (input1 : value) (input2 : value) : SpecTecCall value
  | «$cast_op» (input0 : typeIR) (input1 : value) : SpecTecCall value
  | «$default» (input0 : typeIR) : SpecTecCall value
  | «$default:case_10:iter:1» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List value)
  | «$default:case_13:iter:3» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldValue)
  | «$default:case_14:iter:3» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldValue)
  | «$default:case_15:iter:3» (input0 : (_root_.List id)) (input1 : (_root_.List typeIR)) : SpecTecCall (_root_.List fieldValue)
  | «$cast_to_enum» (input0 : enumTypeIR) (input1 : value) : SpecTecCall value
  | «$cast_to_enum'» (input0 : typeId) (input1 : typeIR) (input2 : (_root_.List valueFieldIR)) (input3 : value) : SpecTecCall value
  | «$cast_bool» (input0 : typeIR) (input1 : boolValue) : SpecTecCall value
  | «$cast_int» (input0 : typeIR) (input1 : integerValue) : SpecTecCall value
  | «$cast_error» (input0 : typeIR) (input1 : errorValue) : SpecTecCall value
  | «$cast_list» (input0 : typeIR) (input1 : listValue) : SpecTecCall value
  | «$cast_list:case_1:iter:1» (input0 : typeIR) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_tuple» (input0 : typeIR) (input1 : tupleValue) : SpecTecCall value
  | «$cast_tuple:case_1:iter:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_enum» (input0 : typeIR) (input1 : enumValue) : SpecTecCall value
  | «$cast_sequence» (input0 : typeIR) (input1 : sequenceValue) : SpecTecCall value
  | «$cast_sequence:case_2:iter:1» (input0 : typeIR) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_sequence:case_3:iter:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_sequence:case_4:iter:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_sequence:case_5:iter:1» (input0 : typeIR) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_sequence:case_6:iter:1» (input0 : typeIR) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_sequence:case_7:iter:3» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_sequence:case_8:iter:3» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_sequence:case_9:iter:1» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_sequence:case_10:iter:2» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_sequence:case_10:iter:4» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List value)
  | «$cast_sequence:case_11:iter:1» (input0 : typeIR) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_sequence:case_12:iter:1» (input0 : typeIR) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_sequence:case_13:iter:4» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_sequence:case_13:iter:6» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List value)
  | «$cast_sequence:case_14:iter:4» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_sequence:case_14:iter:6» (input0 : (_root_.List typeIR)) : SpecTecCall (_root_.List value)
  | «$cast_record» (input0 : typeIR) (input1 : recordValue) : SpecTecCall value
  | «$cast_record:case_1:iter:11» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_record:case_2:iter:11» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_record:case_3:iter:11» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_record:case_4:iter:11» (input0 : (_root_.List typeIR)) (input1 : (_root_.List value)) : SpecTecCall (_root_.List value)
  | «$cast_record:case_5:iter:5» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) (input2 : (_root_.List id)) (input3 : (_root_.List typeIR)) : SpecTecCall (_root_.List value)
  | «$cast_record:case_6:iter:5» (input0 : (_root_.List nameIR)) (input1 : (_root_.List value)) (input2 : (_root_.List id)) (input3 : (_root_.List typeIR)) : SpecTecCall (_root_.List value)
  | «$cast_record_field» (input0 : typeIR) (input1 : id) (input2 : (set (pair id value))) : SpecTecCall value
  | «$cast_default» (input0 : typeIR) (input1 : defaultValue) : SpecTecCall value
  | «$cast_invalid_header» (input0 : typeIR) : SpecTecCall value
  | «$cast_set» (input0 : typeIR) (input1 : setValue) : SpecTecCall value
  | Expr_eval_lctk (input0 : cursor) (input1 : typingContext) (input2 : typedExpressionIR) : SpecTecCall value
  | «Expr_eval_lctk:non-default:iter:1» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List value)
  | «Expr_eval_lctk:default:iter:1» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List value)
  | «Expr_eval_lctk:non-default_2:iter:3» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List value)
  | «Expr_eval_lctk:default_2:iter:3» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List typedExpressionIR)) : SpecTecCall (_root_.List value)
  | «Expr_eval_lctk:static_assert:iter:7» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List argumentIR)) : SpecTecCall (_root_.List value)
  | Argument_eval_lctk (input0 : cursor) (input1 : typingContext) (input2 : argumentIR) : SpecTecCall value
  | Type_ok (input0 : cursor) (input1 : typingContext) (input2 : typeOrVoid) : SpecTecCall (typeIR × (_root_.List typeId))
  | TypeArgument_ok (input0 : cursor) (input1 : typingContext) (input2 : typeArgument) : SpecTecCall (typeArgumentIR × (_root_.List typeId))
  | TypeArguments_ok (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List typeArgument)) : SpecTecCall (typeArgumentListIR × (_root_.List typeId))
  | TypeArgumentList_ok (input0 : cursor) (input1 : typingContext) (input2 : typeArgumentList) : SpecTecCall (typeArgumentListIR × (_root_.List typeId))
  | Expr_ok (input0 : cursor) (input1 : typingContext) (input2 : expression) : SpecTecCall typedExpressionIR
  | «Expr_ok:non-default:iter:3» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List expression)) : SpecTecCall (_root_.List typedExpressionIR)
  | «Expr_ok:default:iter:4» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List expression)) : SpecTecCall (_root_.List typedExpressionIR)
  | «Expr_ok:multiple-non-default:iter:8» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List expression)) : SpecTecCall (_root_.List typedExpressionIR)
  | «Expr_ok:multiple-default:iter:8» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List expression)) : SpecTecCall (_root_.List typedExpressionIR)
  | Argument_ok (input0 : cursor) (input1 : typingContext) (input2 : argument) : SpecTecCall argumentIR
  | ArgumentList_ok (input0 : cursor) (input1 : typingContext) (input2 : argumentList) : SpecTecCall argumentListIR
  | «ArgumentList_ok:rule:iter:1» (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List argument)) : SpecTecCall (_root_.List argumentIR)
  | Lvalue_ok (input0 : cursor) (input1 : typingContext) (input2 : lvalue) : SpecTecCall typedLvalueIR
  | Call_convention_expr_ok (input0 : cursor) (input1 : typingContext) (input2 : actctxt) (input3 : parameterIR) (input4 : typedExpressionIR) : SpecTecCall typedExpressionIR
  | Call_convention_arg_ok (input0 : cursor) (input1 : typingContext) (input2 : actctxt) (input3 : parameterIR) (input4 : argumentIR) : SpecTecCall argumentIR
  | Call_convention_ok (input0 : cursor) (input1 : typingContext) (input2 : actctxt) (input3 : (_root_.List parameterIR)) (input4 : argumentListIR) : SpecTecCall argumentListIR
  | CallableTarget_ok (input0 : cursor) (input1 : typingContext) (input2 : callableTarget) : SpecTecCall callableTargetIR
  | Call_ok (input0 : cursor) (input1 : typingContext) (input2 : callableTypeIR) (input3 : typeArgumentListIR) (input4 : (_root_.List typeId)) (input5 : argumentListIR) (input6 : (_root_.List id)) (input7 : (_root_.List id)) : SpecTecCall (typeIR × (typeArgumentListIR × argumentListIR))
  | Inst_ok (input0 : cursor) (input1 : typingContext) (input2 : instctxt) (input3 : constructorTypeIR) (input4 : typeArgumentListIR) (input5 : (_root_.List typeId)) (input6 : argumentListIR) (input7 : (_root_.List id)) (input8 : (_root_.List id)) : SpecTecCall (typeIR × (typeArgumentListIR × argumentListIR))
  | Parameter_ok (input0 : cursor) (input1 : typingContext) (input2 : parameter) : SpecTecCall (parameterIR × (_root_.List typeId))
  | «ParserSelect_ok:rule:iter:1» (input0 : typingContext) (input1 : (_root_.List expression)) : SpecTecCall (_root_.List typedExpressionIR)
  | TableKey_ok (input0 : typingContext) (input1 : tableContext) (input2 : tableKey) : SpecTecCall (tableContext × tableKeyIR)
  | TableKeys_ok (input0 : typingContext) (input1 : tableContext) (input2 : (_root_.List tableKey)) : SpecTecCall (tableContext × tableKeyListIR)
  | Call_action_partial_ok (input0 : typingContext) (input1 : (_root_.List parameterIR)) (input2 : argumentListIR) : SpecTecCall ((_root_.List parameterIR) × ((_root_.List parameterIR) × argumentListIR))
  | TableAction_ok (input0 : typingContext) (input1 : tableContext) (input2 : tableAction) : SpecTecCall (tableContext × tableActionIR)
  | TableActions_ok (input0 : typingContext) (input1 : tableContext) (input2 : (_root_.List tableAction)) : SpecTecCall (tableContext × tableActionListIR)
  | Call_action_default_ok (input0 : typingContext) (input1 : (_root_.List parameterIR)) (input2 : argumentListIR) : SpecTecCall ((_root_.List parameterIR) × ((_root_.List parameterIR) × argumentListIR))
  | TableDefaultAction_ok (input0 : typingContext) (input1 : tableContext) (input2 : initializer) : SpecTecCall tableActionReferenceIR
  | TableEntry_action_ok (input0 : typingContext) (input1 : tableContext) (input2 : tableActionReference) : SpecTecCall tableActionReferenceIR
  | TableEntry_priority_ok (input0 : typingContext) (input1 : tableEntryPriority) : SpecTecCall tableEntryPriorityIR
  | VarDecl_ok (input0 : cursor) (input1 : typingContext) (input2 : variableDeclaration) : SpecTecCall (typingContext × variableDeclarationIR)
  | ConstDecl_ok (input0 : cursor) (input1 : typingContext) (input2 : constantDeclaration) : SpecTecCall (typingContext × constantDeclarationIR)
  | «Decl_ok:structTypeDeclaration:iter:4» (input0 : typingContext) (input1 : (_root_.List type)) : SpecTecCall ((_root_.List typeIR) × (_root_.List (_root_.List typeId)))
  | «Decl_ok:headerTypeDeclaration:iter:4» (input0 : typingContext) (input1 : (_root_.List type)) : SpecTecCall ((_root_.List typeIR) × (_root_.List (_root_.List typeId)))
  | «Decl_ok:headerUnionTypeDeclaration:iter:4» (input0 : typingContext) (input1 : (_root_.List type)) : SpecTecCall ((_root_.List typeIR) × (_root_.List (_root_.List typeId)))
  | CallableTarget_lvalue_ok (input0 : cursor) (input1 : typingContext) (input2 : lvalue) : SpecTecCall callableTargetIR
  | Parameters_ok (input0 : cursor) (input1 : typingContext) (input2 : (_root_.List parameter)) : SpecTecCall (parameterListIR × (_root_.List typeId))
  | ParameterList_ok (input0 : cursor) (input1 : typingContext) (input2 : parameterList) : SpecTecCall (typingContext × (parameterListIR × (_root_.List typeId)))
  | ConstructorParameterListOpt_ok (input0 : typingContext) (input1 : constructorParameterListOpt) : SpecTecCall (typingContext × (constructorParameterListIR × (_root_.List typeId)))
  | ExternMethod_ok (input0 : typingContext) (input1 : typeId) (input2 : externMethodPrototype) : SpecTecCall externMethodPrototypeIR
  | ExternConstructor_ok (input0 : typingContext) (input1 : typeId) (input2 : externConstructorPrototype) : SpecTecCall externConstructorPrototypeIR
  | «Decl_ok:externObjectDeclaration:iter:3» (input0 : typingContext) (input1 : nameIR) (input2 : (_root_.List externMethodPrototype)) : SpecTecCall (_root_.List externMethodPrototypeIR)
  | «Decl_ok:externObjectDeclaration:iter:13» (input0 : typingContext) (input1 : nameIR) (input2 : (_root_.List externConstructorPrototype)) : SpecTecCall (_root_.List externConstructorPrototypeIR)
  | ForCollectionExpr_ok (input0 : typingContext) (input1 : typeIR) (input2 : forCollectionExpression) : SpecTecCall forCollectionExpressionIR
  | SwitchLabel_general_ok (input0 : typingContext) (input1 : typeIR) (input2 : switchLabel) : SpecTecCall switchLabelIR
  | Stmt_ok (input0 : cursor) (input1 : typingContext) (input2 : statement) : SpecTecCall (typingContext × statementIR)
  | BlockElementStmt_ok (input0 : typingContext) (input1 : blockElementStatement) : SpecTecCall (typingContext × blockElementStatementIR)
  | BlockElementStmtList_ok (input0 : typingContext) (input1 : blockElementStatementList) : SpecTecCall (typingContext × (_root_.List blockElementStatementIR))
  | Block_ok (input0 : typingContext) (input1 : blockStatement) : SpecTecCall (typingContext × blockStatementIR)
  | ForUpdateStmt_ok (input0 : typingContext) (input1 : forUpdateStatement) : SpecTecCall forUpdateStatementIR
  | ForUpdateStmtList_ok (input0 : typingContext) (input1 : forUpdateStatementList) : SpecTecCall (_root_.List forUpdateStatementIR)
  | «ForUpdateStmtList_ok:rule:iter:1» (input0 : typingContext) (input1 : (_root_.List forUpdateStatement)) : SpecTecCall (_root_.List forUpdateStatementIR)
  | ForInitStmt_ok (input0 : typingContext) (input1 : forInitStatement) : SpecTecCall (typingContext × forInitStatementIR)
  | ForInitStmts_ok (input0 : typingContext) (input1 : (_root_.List forInitStatement)) : SpecTecCall (typingContext × (_root_.List forInitStatementIR))
  | ForInitStmtList_ok (input0 : typingContext) (input1 : forInitStatementList) : SpecTecCall (typingContext × (_root_.List forInitStatementIR))
  | SwitchCase_table_ok (input0 : typingContext) (input1 : typeId) (input2 : switchCase) : SpecTecCall (typingContext × switchCaseIR)
  | SwitchCases_table_ok (input0 : typingContext) (input1 : typeId) (input2 : (_root_.List switchCase)) : SpecTecCall (typingContext × switchCaseListIR)
  | SwitchCaseList_table_ok (input0 : typingContext) (input1 : typeId) (input2 : switchCaseList) : SpecTecCall (typingContext × switchCaseListIR)
  | Switch_table_ok (input0 : typingContext) (input1 : id) (input2 : switchCaseList) : SpecTecCall (typingContext × (_root_.List switchCaseIR))
  | SwitchCase_general_ok (input0 : typingContext) (input1 : typeIR) (input2 : switchCase) : SpecTecCall (typingContext × switchCaseIR)
  | SwitchCases_general_ok (input0 : typingContext) (input1 : typeIR) (input2 : (_root_.List switchCase)) : SpecTecCall (typingContext × switchCaseListIR)
  | SwitchCaseList_general_ok (input0 : typingContext) (input1 : typeIR) (input2 : switchCaseList) : SpecTecCall (typingContext × switchCaseListIR)
  | Switch_general_ok (input0 : typingContext) (input1 : typedExpressionIR) (input2 : switchCaseList) : SpecTecCall (typingContext × (_root_.List switchCaseIR))
  | BlockElementStmts_ok (input0 : typingContext) (input1 : (_root_.List blockElementStatement)) : SpecTecCall (typingContext × (_root_.List blockElementStatementIR))
  | ParserStmt_ok (input0 : typingContext) (input1 : parserStatement) : SpecTecCall (typingContext × parserStatementIR)
  | ParserBlockElementStmt_ok (input0 : typingContext) (input1 : parserBlockElementStatement) : SpecTecCall (typingContext × parserBlockElementStatementIR)
  | ParserBlockElementStmtList_ok (input0 : typingContext) (input1 : parserBlockElementStatementList) : SpecTecCall (typingContext × (_root_.List parserBlockElementStatementIR))
  | ParserBlock_ok (input0 : typingContext) (input1 : parserBlockStatement) : SpecTecCall (typingContext × parserBlockStatementIR)
  | ParserBlockElementStmts_ok (input0 : typingContext) (input1 : (_root_.List parserBlockElementStatement)) : SpecTecCall (typingContext × (_root_.List parserBlockElementStatementIR))
  | FuncDecl_ok (input0 : cursor) (input1 : typingContext) (input2 : functionDeclaration) : SpecTecCall (typingContext × functionDeclarationIR)
  | ActionDecl_ok (input0 : cursor) (input1 : typingContext) (input2 : actionDeclaration) : SpecTecCall (typingContext × actionDeclarationIR)
  | InstDecl_non_objectInitializer_ok (input0 : cursor) (input1 : typingContext) (input2 : annotationList) (input3 : prefixedTypeName) (input4 : typeArgumentList) (input5 : argumentList) (input6 : name) : SpecTecCall (typingContext × instantiationIR)
  | InstDecl_ok (input0 : cursor) (input1 : typingContext) (input2 : instantiation) : SpecTecCall (typingContext × instantiationIR)
  | ObjectDecl_ok (input0 : cursor) (input1 : typingContext) (input2 : typeFrame) (input3 : externMethodTypeDefEnv) (input4 : objectDeclaration) : SpecTecCall (typeFrame × (externMethodTypeDefEnv × objectDeclarationIR))
  | ObjectDecls_ok (input0 : cursor) (input1 : typingContext) (input2 : typeFrame) (input3 : externMethodTypeDefEnv) (input4 : (_root_.List objectDeclaration)) : SpecTecCall (typeFrame × (externMethodTypeDefEnv × objectDeclarationListIR))
  | ObjectDeclList_ok (input0 : cursor) (input1 : typingContext) (input2 : objectDeclarationList) : SpecTecCall (typeFrame × (externMethodTypeDefEnv × objectDeclarationListIR))
  | InstDecl_objectInitializer_ok (input0 : cursor) (input1 : typingContext) (input2 : annotationList) (input3 : prefixedTypeName) (input4 : typeArgumentList) (input5 : argumentList) (input6 : name) (input7 : objectDeclarationList) : SpecTecCall (typingContext × instantiationIR)
  | ParserLocalDecl_ok (input0 : typingContext) (input1 : parserLocalDeclaration) : SpecTecCall (typingContext × parserLocalDeclarationIR)
  | Enum_serializable_field_ok (input0 : typingContext) (input1 : nameIR) (input2 : typeIR) (input3 : namedExpression) : SpecTecCall (typingContext × namedValueIR)
  | Enum_serializable_fields_ok (input0 : typingContext) (input1 : nameIR) (input2 : typeIR) (input3 : (_root_.List namedExpression)) : SpecTecCall (typingContext × (_root_.List namedValueIR))
  | Enum_serializable_fieldList_ok (input0 : typingContext) (input1 : nameIR) (input2 : typeIR) (input3 : namedExpressionList) : SpecTecCall (typingContext × (_root_.List namedValueIR))
  | SelectCase_keyset_simple_ok (input0 : typingContext) (input1 : typeIR) (input2 : simpleKeysetExpression) : SpecTecCall simpleKeysetExpressionIR
  | «SelectCase_keyset_ok:list:iter:2» (input0 : typingContext) (input1 : (_root_.List simpleKeysetExpression)) (input2 : (_root_.List typeIR)) : SpecTecCall (_root_.List simpleKeysetExpressionIR)
  | SelectCase_keyset_ok (input0 : typingContext) (input1 : (_root_.List typeIR)) (input2 : keysetExpression) : SpecTecCall keysetExpressionIR
  | SelectCase_ok (input0 : typingContext) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) (input3 : selectCase) : SpecTecCall selectCaseIR
  | «ParserSelect_ok:rule:iter:9» (input0 : typingContext) (input1 : (_root_.List nameIR)) (input2 : (_root_.List typeIR)) (input3 : (_root_.List selectCase)) : SpecTecCall (_root_.List selectCaseIR)
  | ParserSelect_ok (input0 : typingContext) (input1 : (_root_.List nameIR)) (input2 : selectExpression) : SpecTecCall selectExpressionIR
  | ParserTransition_ok (input0 : typingContext) (input1 : (_root_.List nameIR)) (input2 : transitionStatement) : SpecTecCall transitionStatementIR
  | ParserState_ok (input0 : typingContext) (input1 : (_root_.List nameIR)) (input2 : parserState) : SpecTecCall parserStateIR
  | «ParserStateList_ok:rule:iter:5» (input0 : typingContext) (input1 : (_root_.List nameIR)) (input2 : (_root_.List parserState)) : SpecTecCall (_root_.List parserStateIR)
  | ParserStateList_ok (input0 : typingContext) (input1 : parserStateList) : SpecTecCall (_root_.List parserStateIR)
  | ParserLocalDecls_ok (input0 : typingContext) (input1 : (_root_.List parserLocalDeclaration)) : SpecTecCall (typingContext × (_root_.List parserLocalDeclarationIR))
  | ParserLocalDeclList_ok (input0 : typingContext) (input1 : parserLocalDeclarationList) : SpecTecCall (typingContext × (_root_.List parserLocalDeclarationIR))
  | TableEntry_keyset_simple_ok (input0 : typingContext) (input1 : tableContext) (input2 : matchKey) (input3 : simpleKeysetExpression) : SpecTecCall (tableEntryState × simpleKeysetExpressionIR)
  | TableEntry_keysets_simple_ok (input0 : typingContext) (input1 : tableContext) (input2 : tableEntryState) (input3 : (_root_.List matchKey)) (input4 : (_root_.List simpleKeysetExpression)) : SpecTecCall (tableEntryState × (_root_.List simpleKeysetExpressionIR))
  | TableEntry_keyset_ok (input0 : typingContext) (input1 : tableContext) (input2 : keysetExpression) : SpecTecCall (tableEntryState × keysetExpressionIR)
  | TableEntry_ok (input0 : typingContext) (input1 : tableContext) (input2 : tableEntry) : SpecTecCall (tableEntryState × tableEntryIR)
  | «TableProperty_ok:entries:iter:2» (input0 : typingContext) (input1 : tableContext) (input2 : (_root_.List tableEntry)) : SpecTecCall ((_root_.List tableEntryState) × (_root_.List tableEntryIR))
  | TableProperty_ok (input0 : typingContext) (input1 : tableContext) (input2 : tableProperty) : SpecTecCall (tableContext × tablePropertyIR)
  | TableProperties_ok (input0 : typingContext) (input1 : tableContext) (input2 : (_root_.List tableProperty)) : SpecTecCall (tableContext × tablePropertyListIR)
  | Table_ok (input0 : typingContext) (input1 : (_root_.List tableProperty)) : SpecTecCall (tableContext × tablePropertyListIR)
  | ControlLocalDecl_ok (input0 : typingContext) (input1 : controlLocalDeclaration) : SpecTecCall (typingContext × controlLocalDeclarationIR)
  | ControlLocalDecls_ok (input0 : typingContext) (input1 : (_root_.List controlLocalDeclaration)) : SpecTecCall (typingContext × (_root_.List controlLocalDeclarationIR))
  | ControlLocalDeclList_ok (input0 : typingContext) (input1 : controlLocalDeclarationList) : SpecTecCall (typingContext × (_root_.List controlLocalDeclarationIR))
  | Decl_ok (input0 : typingContext) (input1 : declaration) : SpecTecCall (typingContext × declarationIR)
  | Decls_ok (input0 : typingContext) (input1 : (_root_.List declaration)) : SpecTecCall (typingContext × (_root_.List declarationIR))
  | Program_ok (input0 : p4program) : SpecTecCall p4programIR
  | Expr_inst (input0 : cursor) (input1 : instContext) (input2 : store) (input3 : typedExpressionIR) : SpecTecCall (store × value)
  | Exprs_inst (input0 : cursor) (input1 : instContext) (input2 : store) (input3 : (_root_.List typedExpressionIR)) : SpecTecCall (store × (_root_.List value))
  | Argument_inst (input0 : cursor) (input1 : instContext) (input2 : store) (input3 : argumentIR) : SpecTecCall (store × value)
  | DirectApplicationStmt_inst (input0 : cursor) (input1 : instContext) (input2 : store) (input3 : directApplicationStatementIR) : SpecTecCall (store × (constantDeclarationIR × callStatementIR))
  | Stmt_inst (input0 : cursor) (input1 : instContext) (input2 : store) (input3 : statementIR) : SpecTecCall (instContext × (store × statementIR))
  | BlockElementStmt_inst (input0 : instContext) (input1 : store) (input2 : blockElementStatementIR) : SpecTecCall (instContext × (store × blockElementStatementIR))
  | BlockElementStmtList_inst (input0 : instContext) (input1 : store) (input2 : blockElementStatementListIR) : SpecTecCall (instContext × (store × (_root_.List blockElementStatementIR)))
  | Block_inst (input0 : instContext) (input1 : store) (input2 : blockStatementIR) : SpecTecCall (instContext × (store × blockStatementIR))
  | ParserStmt_inst (input0 : instContext) (input1 : store) (input2 : parserStatementIR) : SpecTecCall (instContext × (store × parserStatementIR))
  | ParserBlockElementStmt_inst (input0 : instContext) (input1 : store) (input2 : parserBlockElementStatementIR) : SpecTecCall (instContext × (store × parserBlockElementStatementIR))
  | ParserBlockElementStmtList_inst (input0 : instContext) (input1 : store) (input2 : parserBlockElementStatementListIR) : SpecTecCall (instContext × (store × (_root_.List parserBlockElementStatementIR)))
  | ParserBlock_inst (input0 : instContext) (input1 : store) (input2 : parserBlockStatementIR) : SpecTecCall (instContext × (store × parserBlockStatementIR))
  | ParserState_inst (input0 : instContext) (input1 : store) (input2 : parserStateIR) : SpecTecCall (instContext × store)
  | ParserStates_inst (input0 : instContext) (input1 : store) (input2 : (_root_.List parserStateIR)) : SpecTecCall (instContext × store)
  | ParserLocalDecl_inst (input0 : instContext) (input1 : store) (input2 : parserLocalDeclarationIR) : SpecTecCall (instContext × (store × parserLocalDeclarationIR))
  | ParserLocalDecls_inst (input0 : instContext) (input1 : store) (input2 : (_root_.List parserLocalDeclarationIR)) : SpecTecCall (instContext × (store × (_root_.List parserLocalDeclarationIR)))
  | TableProperty_inst (input0 : instContext) (input1 : store) (input2 : tablePropertyIR) : SpecTecCall (store × tablePropertyIR)
  | TableProperties_inst (input0 : instContext) (input1 : store) (input2 : (_root_.List tablePropertyIR)) : SpecTecCall (store × (_root_.List tablePropertyIR))
  | ControlLocalDecl_inst (input0 : instContext) (input1 : store) (input2 : controlLocalDeclarationIR) : SpecTecCall (instContext × (store × (_root_.Option controlLocalDeclarationIR)))
  | ControlLocalDecls_inst (input0 : instContext) (input1 : store) (input2 : (_root_.List controlLocalDeclarationIR)) : SpecTecCall (instContext × (store × (_root_.List controlLocalDeclarationIR)))
  | InstDecl_inst (input0 : cursor) (input1 : instContext) (input2 : store) (input3 : instantiationIR) : SpecTecCall (instContext × (store × constantDeclarationIR))
  | Copy_in_arg_inst (input0 : store) (input1 : cursor) (input2 : instContext) (input3 : argumentIR) (input4 : cursor) (input5 : instContext) (input6 : id) : SpecTecCall (store × instContext)
  | Copy_in_inst (input0 : store) (input1 : cursor) (input2 : instContext) (input3 : (_root_.List argumentIR)) (input4 : cursor) (input5 : instContext) (input6 : (_root_.List id)) : SpecTecCall (store × instContext)
  | Copy_in_arg_inst_default (input0 : store) (input1 : cursor) (input2 : instContext) (input3 : cursor) (input4 : instContext) (input5 : parameterIR) : SpecTecCall (store × instContext)
  | Copy_in_inst_default (input0 : store) (input1 : cursor) (input2 : instContext) (input3 : cursor) (input4 : instContext) (input5 : (_root_.List parameterIR)) : SpecTecCall (store × instContext)
  | Constructor_call (input0 : cursor) (input1 : instContext) (input2 : store) (input3 : constructorDef) (input4 : typeArgumentListIR) (input5 : argumentListIR) (input6 : (_root_.List id)) (input7 : (_root_.List id)) : SpecTecCall (store × object)
  | SwitchCase_inst (input0 : cursor) (input1 : instContext) (input2 : store) (input3 : switchCaseIR) : SpecTecCall (store × switchCaseIR)
  | SwitchCases_inst (input0 : cursor) (input1 : instContext) (input2 : store) (input3 : (_root_.List switchCaseIR)) : SpecTecCall (store × (_root_.List switchCaseIR))
  | ObjectDecl_inst (input0 : instContext) (input1 : store) (input2 : objectDeclarationIR) : SpecTecCall (instContext × store)
  | ObjectDecls_inst (input0 : instContext) (input1 : store) (input2 : objectDeclarationListIR) : SpecTecCall (instContext × store)
  | Decl_inst (input0 : instContext) (input1 : store) (input2 : declarationIR) : SpecTecCall (instContext × store)
  | Decls_inst (input0 : instContext) (input1 : store) (input2 : (_root_.List declarationIR)) : SpecTecCall (instContext × store)
  | Program_inst (input0 : p4program) : SpecTecCall (globalInstLayer × store)
  | «$match_keyset:case_3:iter:0» (input0 : value) (input1 : (_root_.List value)) : SpecTecCall (_root_.List _root_.Bool)
  | «$match_keyset» (input0 : setValue) (input1 : value) : SpecTecCall _root_.Bool
  | «$match_keysets» (input0 : (_root_.List setValue)) (input1 : (_root_.List value)) : SpecTecCall _root_.Bool
  | «$values_of_setValue» (input0 : setTypeIR) (input1 : setValue) : SpecTecCall (_root_.List value)
  | «$match_switchLabelIR_general» (input0 : value) (input1 : value) : SpecTecCall _root_.Bool
  | Expr_eval (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : typedExpressionIR) : SpecTecCall (evalContext × (arch × expressionResult))
  | Exprs_eval (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : (_root_.List typedExpressionIR)) : SpecTecCall (evalContext × (arch × expressionListResult))
  | Eval_keyset (input0 : evalContext) (input1 : arch) (input2 : keysetExpressionIR) : SpecTecCall (evalContext × (arch × keysetExpressionResult))
  | Argument_eval (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : argumentIR) : SpecTecCall (evalContext × (arch × expressionResult))
  | Argument_eval_lvalue (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : argumentIR) : SpecTecCall (evalContext × (arch × storageReferenceResult))
  | Lvalue_eval (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : typedLvalueIR) : SpecTecCall (evalContext × (arch × storageReferenceResult))
  | Stmt_eval (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : statementIR) : SpecTecCall (evalContext × (arch × statementResult))
  | BlockElementStmt_eval (input0 : evalContext) (input1 : arch) (input2 : blockElementStatementIR) : SpecTecCall (evalContext × (arch × statementResult))
  | BlockElementStmtList_eval (input0 : evalContext) (input1 : arch) (input2 : blockElementStatementListIR) : SpecTecCall (evalContext × (arch × statementResult))
  | Block_eval (input0 : evalContext) (input1 : arch) (input2 : blockStatementIR) : SpecTecCall (evalContext × (arch × statementResult))
  | ParserStmt_eval (input0 : evalContext) (input1 : arch) (input2 : parserStatementIR) : SpecTecCall (evalContext × (arch × parserStatementResult))
  | ParserBlockElementStmt_eval (input0 : evalContext) (input1 : arch) (input2 : parserBlockElementStatementIR) : SpecTecCall (evalContext × (arch × parserStatementResult))
  | ParserBlockElementStmtList_eval (input0 : evalContext) (input1 : arch) (input2 : parserBlockElementStatementListIR) : SpecTecCall (evalContext × (arch × parserStatementResult))
  | ParserBlock_eval (input0 : evalContext) (input1 : arch) (input2 : parserBlockStatementIR) : SpecTecCall (evalContext × (arch × parserStatementResult))
  | ParserSelect_eval (input0 : evalContext) (input1 : arch) (input2 : selectExpressionIR) : SpecTecCall (evalContext × (arch × transitionResult))
  | ParserTransition_eval (input0 : evalContext) (input1 : arch) (input2 : transitionStatementIR) : SpecTecCall (evalContext × (arch × transitionResult))
  | ParserState_eval (input0 : evalContext) (input1 : arch) (input2 : parserStateIR) : SpecTecCall (evalContext × (arch × transitionResult))
  | ParserState_trans (input0 : evalContext) (input1 : arch) (input2 : nameIR) : SpecTecCall (evalContext × (arch × transitionResult))
  | ParserLocalDecl_eval (input0 : evalContext) (input1 : arch) (input2 : parserLocalDeclarationIR) : SpecTecCall (evalContext × (arch × parserDeclarationResult))
  | ParserLocalDecls_eval (input0 : evalContext) (input1 : arch) (input2 : (_root_.List parserLocalDeclarationIR)) : SpecTecCall (evalContext × (arch × parserDeclarationResult))
  | Table_eval (input0 : evalContext) (input1 : arch) (input2 : typeId) (input3 : tableObjectProperty) : SpecTecCall (evalContext × (arch × tableResult))
  | ControlBody_eval (input0 : evalContext) (input1 : arch) (input2 : controlBodyIR) : SpecTecCall (evalContext × (arch × controlBodyResult))
  | ControlLocalDecl_eval (input0 : evalContext) (input1 : arch) (input2 : controlLocalDeclarationIR) : SpecTecCall (evalContext × (arch × controlLocalDeclarationResult))
  | ControlLocalDecls_eval (input0 : evalContext) (input1 : arch) (input2 : (_root_.List controlLocalDeclarationIR)) : SpecTecCall (evalContext × (arch × controlLocalDeclarationResult))
  | VarDecl_eval (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : variableDeclarationIR) : SpecTecCall (evalContext × (arch × declarationResult))
  | Callee_eval (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : callableTargetIR) (input4 : argumentListIR) : SpecTecCall (evalContext × (arch × calleeResult))
  | Copy_in_arg (input0 : arch) (input1 : cursor) (input2 : evalContext) (input3 : parameterIR) (input4 : cursor) (input5 : evalContext) (input6 : argumentIR) : SpecTecCall (arch × (evalContext × (evalContext × copyInArgumentResult)))
  | Copy_in (input0 : cursor) (input1 : arch) (input2 : cursor) (input3 : evalContext) (input4 : parameterListIR) (input5 : cursor) (input6 : evalContext) (input7 : argumentListIR) : SpecTecCall (arch × (evalContext × (evalContext × copyInResult)))
  | Call_eval (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : callee) (input4 : typeArgumentListIR) (input5 : argumentListIR) : SpecTecCall (evalContext × (arch × callResult))
  | Eval_keyset_simple (input0 : evalContext) (input1 : arch) (input2 : simpleKeysetExpressionIR) : SpecTecCall (evalContext × (arch × simpleKeysetExpressionResult))
  | Eval_keysets_simple (input0 : evalContext) (input1 : arch) (input2 : simpleKeysetExpressionListIR) : SpecTecCall (evalContext × (arch × keysetExpressionResult))
  | ForUpdateStmt_eval (input0 : evalContext) (input1 : arch) (input2 : forUpdateStatementIR) : SpecTecCall (evalContext × (arch × statementResult))
  | ForUpdateStmts_eval (input0 : evalContext) (input1 : arch) (input2 : forUpdateStatementListIR) : SpecTecCall (evalContext × (arch × statementResult))
  | ForInitStmt_eval (input0 : evalContext) (input1 : arch) (input2 : forInitStatementIR) : SpecTecCall (evalContext × (arch × statementResult))
  | ForInitStmts_eval (input0 : evalContext) (input1 : arch) (input2 : forInitStatementListIR) : SpecTecCall (evalContext × (arch × statementResult))
  | ForThreeClauseStmt_eval (input0 : evalContext) (input1 : arch) (input2 : typedExpressionIR) (input3 : statementIR) (input4 : forUpdateStatementListIR) : SpecTecCall (evalContext × (arch × statementResult))
  | ForCollectionExpr_eval (input0 : evalContext) (input1 : arch) (input2 : forCollectionExpressionIR) : SpecTecCall (evalContext × (arch × expressionListResult))
  | ForInStmt_eval (input0 : evalContext) (input1 : arch) (input2 : nameIR) (input3 : (_root_.List value)) (input4 : statementIR) : SpecTecCall (evalContext × (arch × statementResult))
  | Switch_table_eval (input0 : evalContext) (input1 : arch) (input2 : id) (input3 : (_root_.List switchCaseIR)) : SpecTecCall (evalContext × (arch × statementResult))
  | Switch_general_eval (input0 : evalContext) (input1 : arch) (input2 : value) (input3 : (_root_.List switchCaseIR)) : SpecTecCall (evalContext × (arch × statementResult))
  | SwitchLabel_general_eval (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : switchLabelIR) : SpecTecCall (evalContext × (arch × expressionResult))
  | SwitchCases_general_eval (input0 : cursor) (input1 : evalContext) (input2 : arch) (input3 : value) (input4 : switchCaseListIR) : SpecTecCall (evalContext × (arch × (_root_.Option blockStatementIR)))
  | SelectCase_match (input0 : evalContext) (input1 : arch) (input2 : (_root_.List value)) (input3 : selectCaseIR) : SpecTecCall (evalContext × (arch × selectCaseMatchResult))
  | SelectCases_match (input0 : evalContext) (input1 : arch) (input2 : (_root_.List value)) (input3 : selectCaseListIR) : SpecTecCall (evalContext × (arch × selectCaseMatchResult))
  | TableKey_eval (input0 : evalContext) (input1 : arch) (input2 : tableKeyIR) : SpecTecCall (evalContext × (arch × tableKeyResult))
  | TableKeys_eval (input0 : evalContext) (input1 : arch) (input2 : tableKeyListIR) : SpecTecCall (evalContext × (arch × tableKeysResult))
  | TableMatch_eval (input0 : evalContext) (input1 : arch) (input2 : (_root_.List tableKeyValue)) (input3 : tableEntryIR) : SpecTecCall (evalContext × (arch × tableMatchResult))
  | TableMatches_eval (input0 : evalContext) (input1 : arch) (input2 : (_root_.List tableKeyValue)) (input3 : tableEntryListIR) : SpecTecCall (evalContext × (arch × tableMatchesResult))
  | ActionBody_eval (input0 : evalContext) (input1 : arch) (input2 : blockStatementIR) : SpecTecCall (evalContext × (arch × actionResult))
  | DefinedFunctionBody_eval (input0 : evalContext) (input1 : arch) (input2 : blockStatementIR) : SpecTecCall (evalContext × (arch × definedFunctionResult))
  | Var_init (input0 : evalContext) (input1 : typeIR) (input2 : nameIR) : SpecTecCall evalContext
  | Extern_init (input0 : evalContext) (input1 : arch) (input2 : nameIR) (input3 : nameIR) : SpecTecCall arch
  | Program_init (input0 : p4program) : SpecTecCall (evalContext × store)
  | V1Model_init (input0 : p4program) : SpecTecCall (evalContext × arch)
  | V1Model_init_packet_in (input0 : evalContext) (input1 : arch) (input2 : objectState) : SpecTecCall (evalContext × arch)
  | V1Model_init_packet_out (input0 : evalContext) (input1 : arch) (input2 : objectState) : SpecTecCall (evalContext × arch)
  | V1Model_init_globals (input0 : evalContext) (input1 : arch) (input2 : _root_.Int) : SpecTecCall evalContext
  | V1Model_parser (input0 : evalContext) (input1 : arch) : SpecTecCall (evalContext × (arch × transitionResult))
  | V1Model_verify (input0 : evalContext) (input1 : arch) : SpecTecCall (evalContext × (arch × callResult))
  | V1Model_ingress (input0 : evalContext) (input1 : arch) : SpecTecCall (evalContext × (arch × callResult))
  | V1Model_egress (input0 : evalContext) (input1 : arch) : SpecTecCall (evalContext × (arch × callResult))
  | V1Model_check (input0 : evalContext) (input1 : arch) : SpecTecCall (evalContext × (arch × callResult))
  | V1Model_deparse (input0 : evalContext) (input1 : arch) : SpecTecCall (evalContext × (arch × callResult))
  | «$field_list_annotation_index» (input0 : annotationList) : SpecTecCall (_root_.Option integerLiteral)
  | «$field_has_field_list_index» (input0 : fieldTypeIR) (input1 : integerLiteral) : SpecTecCall _root_.Bool
  | «$fields_with_field_list_index» (input0 : (_root_.List fieldTypeIR)) (input1 : integerLiteral) : SpecTecCall (_root_.List fieldTypeIR)
  | «$V1Model_meta_fields_of_index» (input0 : arch) (input1 : integerLiteral) : SpecTecCall (_root_.List nameIR)
  | V1Model_setup_preserved_meta_fields (input0 : evalContext) (input1 : arch) (input2 : integerLiteral) : SpecTecCall evalContext
  | EBPF_init (input0 : p4program) : SpecTecCall (evalContext × arch)
  | EBPF_init_packet_in (input0 : evalContext) (input1 : arch) (input2 : objectState) : SpecTecCall (evalContext × arch)
  | EBPF_init_globals (input0 : evalContext) (input1 : arch) : SpecTecCall evalContext
  | EBPF_parse (input0 : evalContext) (input1 : arch) : SpecTecCall (evalContext × (arch × transitionResult))
  | EBPF_filter (input0 : evalContext) (input1 : arch) : SpecTecCall (evalContext × (arch × callResult))
  | PSA_init (input0 : p4program) : SpecTecCall (evalContext × arch)
  | PSA_ingress_init_packet_in (input0 : evalContext) (input1 : arch) (input2 : objectState) : SpecTecCall (evalContext × arch)
  | PSA_ingress_init_packet_out (input0 : evalContext) (input1 : arch) (input2 : objectState) : SpecTecCall (evalContext × arch)
  | PSA_ingress_init_globals (input0 : evalContext) (input1 : arch) (input2 : _root_.Int) : SpecTecCall evalContext
  | PSA_ingress_parser (input0 : evalContext) (input1 : arch) : SpecTecCall (evalContext × (arch × transitionResult))
  | PSA_ingress (input0 : evalContext) (input1 : arch) : SpecTecCall (evalContext × (arch × callResult))
  | PSA_ingress_deparser (input0 : evalContext) (input1 : arch) : SpecTecCall (evalContext × (arch × callResult))
  | PSA_egress_init_packet_in (input0 : evalContext) (input1 : arch) (input2 : objectState) : SpecTecCall (evalContext × arch)
  | PSA_egress_init_packet_out (input0 : evalContext) (input1 : arch) (input2 : objectState) : SpecTecCall (evalContext × arch)
  | PSA_egress_init_globals (input0 : evalContext) (input1 : arch) (input2 : _root_.Int) : SpecTecCall evalContext
  | PSA_egress_parser (input0 : evalContext) (input1 : arch) : SpecTecCall (evalContext × (arch × transitionResult))
  | PSA_egress (input0 : evalContext) (input1 : arch) : SpecTecCall (evalContext × (arch × callResult))
  | PSA_egress_deparser (input0 : evalContext) (input1 : arch) : SpecTecCall (evalContext × (arch × callResult))


abbrev SpecTecRequest := Sigma SpecTecCall


noncomputable def «$ite:clause:0» (X : Type) (input0 : _root_.Bool) (input1 : X) (input2 : X) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let b : _root_.Bool := input0; (let X_t : X := input1; (let X_f : X := input2; (.bind (.guard (true = b)) (fun (_ : Unit) => (.pure ((X_t : X))))))))


noncomputable def «$ite:clause:1» (X : Type) (input0 : _root_.Bool) (input1 : X) (input2 : X) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let b : _root_.Bool := input0; (let X_t : X := input1; (let X_f : X := input2; (.bind (.guard (false = b)) (fun (_ : Unit) => (.pure ((X_f : X))))))))


noncomputable def «$ite_clauses» (X : Type) (input0 : _root_.Bool) (input1 : X) (input2 : X) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$ite:clause:0» X input0 input1 input2), fun (_ : _root_.Unit) => («$ite:clause:1» X input0 input1 input2)]


noncomputable def «$max_nat:clause:0» (input0 : (_root_.List _root_.Nat)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let head : _root_.Nat := «exec:2»; (let tail : (_root_.List _root_.Nat) := «exec:1»; (.pure (((_root_.List.foldl (_root_.Nat.max) head tail) : _root_.Nat))))) | [] => .unmatch)


noncomputable def «$max_nat_clauses» (input0 : (_root_.List _root_.Nat)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$max_nat:clause:0»  input0)]


noncomputable def «$min_nat:clause:0» (input0 : (_root_.List _root_.Nat)) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (match input0 with | «exec:2» :: «exec:1» => (let head : _root_.Nat := «exec:2»; (let tail : (_root_.List _root_.Nat) := «exec:1»; (.pure (((_root_.List.foldl (_root_.Nat.min) head tail) : _root_.Nat))))) | [] => .unmatch)


noncomputable def «$min_nat_clauses» (input0 : (_root_.List _root_.Nat)) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$min_nat:clause:0»  input0)]


noncomputable def «$text_to_int:clause:0» (input0 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let input : _root_.String := input0; (match («$text_to_int:parse» input) with | some «exec:1» => (let result : _root_.Int := «exec:1»; (.pure ((result : _root_.Int)))) | none => .unmatch))


noncomputable def «$text_to_int_clauses» (input0 : _root_.String) : List (SpecTecExecution.Clause.{1, 0} SpecTecRequest _root_.Unit) :=
  [fun (_ : _root_.Unit) => («$text_to_int:clause:0»  input0), fun (_ : _root_.Unit) => .abort "builtin $text_to_int failed"]


noncomputable def «$split_text:clause:0» (input0 : _root_.String) (input1 : _root_.String) : SpecTecExecution.Plan.{1} SpecTecRequest :=
  (let t : _root_.String := input0; (let separator : _root_.String := input1; (.bind (.guard ((1 : _root_.Nat) = (_root_.String.utf8ByteSize separator))) (fun (_ : Unit) => (let parts : (_root_.List _root_.String) := (_root_.String.splitOn t separator); (.pure ((parts : (_root_.List _root_.String)))))))))

end SpecTec
