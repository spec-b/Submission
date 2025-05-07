// Lean compiler output
// Module: LeanCond.PrintNum
// Imports: Init Lean.Elab.Print
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__2;
lean_object* l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static lean_object* l_command_x23printNum_______closed__6;
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_command_x23printNum_______closed__2;
static lean_object* l_command_x23printNum_______closed__5;
lean_object* l_Lean_Expr_bvar___override(lean_object*);
static lean_object* l_command_x23printNum_______closed__8;
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_command_x23printNum_______closed__11;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_command_x23printNum_______closed__13;
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_command_x23printNum____;
static lean_object* l_command_x23printNum_______closed__10;
static lean_object* l_command_x23printNum_______closed__3;
static lean_object* l_command_x23printNum_______closed__15;
static lean_object* l_command_x23printNum_______closed__9;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_command_x23printNum_______closed__4;
static lean_object* l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_command_x23printNum_______closed__1;
LEAN_EXPORT lean_object* l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_command_x23printNum_______closed__12;
static lean_object* l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__8;
static lean_object* l_command_x23printNum_______closed__14;
lean_object* l_Lean_TSyntax_getNat(lean_object*);
static lean_object* l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__9;
static lean_object* l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__10;
static lean_object* l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__3;
static lean_object* l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__5;
static lean_object* l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__7;
static lean_object* l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__6;
static lean_object* l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__4;
static lean_object* l_command_x23printNum_______closed__7;
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* _init_l_command_x23printNum_______closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("command#printNum__", 18);
return x_1;
}
}
static lean_object* _init_l_command_x23printNum_______closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_command_x23printNum_______closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_command_x23printNum_______closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("andthen", 7);
return x_1;
}
}
static lean_object* _init_l_command_x23printNum_______closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_command_x23printNum_______closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_command_x23printNum_______closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#printNum ", 10);
return x_1;
}
}
static lean_object* _init_l_command_x23printNum_______closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_command_x23printNum_______closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_command_x23printNum_______closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ident", 5);
return x_1;
}
}
static lean_object* _init_l_command_x23printNum_______closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_command_x23printNum_______closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_command_x23printNum_______closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_command_x23printNum_______closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_command_x23printNum_______closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_command_x23printNum_______closed__4;
x_2 = l_command_x23printNum_______closed__6;
x_3 = l_command_x23printNum_______closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_command_x23printNum_______closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("num", 3);
return x_1;
}
}
static lean_object* _init_l_command_x23printNum_______closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_command_x23printNum_______closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_command_x23printNum_______closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_command_x23printNum_______closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_command_x23printNum_______closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_command_x23printNum_______closed__4;
x_2 = l_command_x23printNum_______closed__10;
x_3 = l_command_x23printNum_______closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_command_x23printNum_______closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_command_x23printNum_______closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_command_x23printNum_______closed__14;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_command_x23printNum____() {
_start:
{
lean_object* x_1; 
x_1 = l_command_x23printNum_______closed__15;
return x_1;
}
}
static lean_object* _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("no such declaration ", 20);
return x_1;
}
}
static lean_object* _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" : ", 3);
return x_1;
}
}
static lean_object* _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" :=\n", 4);
return x_1;
}
}
static lean_object* _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__9;
x_2 = l_Lean_MessageData_ofExpr(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_command_x23printNum_______closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = l_Lean_Syntax_getId(x_9);
lean_dec(x_9);
x_13 = l_Lean_TSyntax_getNat(x_11);
lean_dec(x_11);
x_14 = l_Lean_Name_num___override(x_12, x_13);
x_15 = lean_st_ref_get(x_3, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_14);
x_19 = lean_environment_find(x_18, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = l_Lean_MessageData_ofName(x_14);
x_21 = l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__2;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__4;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_24, x_2, x_3, x_17);
lean_dec(x_3);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
x_27 = l_Lean_MessageData_ofName(x_14);
x_28 = l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__4;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__6;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_ConstantInfo_type(x_26);
x_33 = l_Lean_MessageData_ofExpr(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__8;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_ConstantInfo_value_x3f(x_26);
lean_dec(x_26);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_38 = l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__10;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_28);
x_41 = 0;
x_42 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_40, x_41, x_2, x_3, x_17);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
lean_dec(x_37);
x_44 = l_Lean_MessageData_ofExpr(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_28);
x_47 = 0;
x_48 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_46, x_47, x_2, x_3, x_17);
return x_48;
}
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Print(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanCond_PrintNum(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Print(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_command_x23printNum_______closed__1 = _init_l_command_x23printNum_______closed__1();
lean_mark_persistent(l_command_x23printNum_______closed__1);
l_command_x23printNum_______closed__2 = _init_l_command_x23printNum_______closed__2();
lean_mark_persistent(l_command_x23printNum_______closed__2);
l_command_x23printNum_______closed__3 = _init_l_command_x23printNum_______closed__3();
lean_mark_persistent(l_command_x23printNum_______closed__3);
l_command_x23printNum_______closed__4 = _init_l_command_x23printNum_______closed__4();
lean_mark_persistent(l_command_x23printNum_______closed__4);
l_command_x23printNum_______closed__5 = _init_l_command_x23printNum_______closed__5();
lean_mark_persistent(l_command_x23printNum_______closed__5);
l_command_x23printNum_______closed__6 = _init_l_command_x23printNum_______closed__6();
lean_mark_persistent(l_command_x23printNum_______closed__6);
l_command_x23printNum_______closed__7 = _init_l_command_x23printNum_______closed__7();
lean_mark_persistent(l_command_x23printNum_______closed__7);
l_command_x23printNum_______closed__8 = _init_l_command_x23printNum_______closed__8();
lean_mark_persistent(l_command_x23printNum_______closed__8);
l_command_x23printNum_______closed__9 = _init_l_command_x23printNum_______closed__9();
lean_mark_persistent(l_command_x23printNum_______closed__9);
l_command_x23printNum_______closed__10 = _init_l_command_x23printNum_______closed__10();
lean_mark_persistent(l_command_x23printNum_______closed__10);
l_command_x23printNum_______closed__11 = _init_l_command_x23printNum_______closed__11();
lean_mark_persistent(l_command_x23printNum_______closed__11);
l_command_x23printNum_______closed__12 = _init_l_command_x23printNum_______closed__12();
lean_mark_persistent(l_command_x23printNum_______closed__12);
l_command_x23printNum_______closed__13 = _init_l_command_x23printNum_______closed__13();
lean_mark_persistent(l_command_x23printNum_______closed__13);
l_command_x23printNum_______closed__14 = _init_l_command_x23printNum_______closed__14();
lean_mark_persistent(l_command_x23printNum_______closed__14);
l_command_x23printNum_______closed__15 = _init_l_command_x23printNum_______closed__15();
lean_mark_persistent(l_command_x23printNum_______closed__15);
l_command_x23printNum____ = _init_l_command_x23printNum____();
lean_mark_persistent(l_command_x23printNum____);
l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__1 = _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__1();
lean_mark_persistent(l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__1);
l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__2 = _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__2();
lean_mark_persistent(l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__2);
l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__3 = _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__3();
lean_mark_persistent(l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__3);
l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__4 = _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__4();
lean_mark_persistent(l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__4);
l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__5 = _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__5();
lean_mark_persistent(l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__5);
l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__6 = _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__6();
lean_mark_persistent(l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__6);
l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__7 = _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__7();
lean_mark_persistent(l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__7);
l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__8 = _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__8();
lean_mark_persistent(l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__8);
l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__9 = _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__9();
lean_mark_persistent(l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__9);
l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__10 = _init_l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__10();
lean_mark_persistent(l___aux__LeanCond__PrintNum______elabRules__command_x23printNum______1___closed__10);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
