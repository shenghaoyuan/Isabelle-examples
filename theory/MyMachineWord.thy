theory MyMachineWord
  imports
    Main
    "Word_Lib.Signed_Words"
begin

definition s4_abs_plus_one :: "4 sword \<Rightarrow> 4 sword" where
"s4_abs_plus_one v = (
  if v \<ge> 0 then
    v+1
  else
    (0 - v)+1
)"

(** 4 sword is [-8,7] *)

value "s4_abs_plus_one 3"
(** 
"4"
  :: "4 signed word"  *)

value "sint (-9:: 4 sword)"
value "sint (s4_abs_plus_one 7)"
value "sint (s4_abs_plus_one 8)"
(** 
"4"
  :: "4 signed word"  *)


type_synonym u4 = "4 word"
type_synonym s4 = "4 sword"
type_synonym u8 = "8 word"
type_synonym s8 = "8 sword"
type_synonym s16 = "16 sword"
type_synonym u16 = "16 word"
type_synonym s32 = "32 sword"
type_synonym u32 = "32 word"
type_synonym s64 = "64 sword"
type_synonym u64 = "64 word"
type_synonym s128 = "128 sword"
type_synonym u128 = "128 word"

(** definition s4_abs_plus_one :: "s4 \<Rightarrow> s4" where *)
end