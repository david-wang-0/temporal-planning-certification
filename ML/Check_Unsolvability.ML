
structure Uint : sig
  val shiftl : Word.word -> Int.int -> Word.word
  val shiftr : Word.word -> Int.int -> Word.word
  val shiftr_signed : Word.word -> Int.int -> Word.word
  val test_bit : Word.word -> Int.int -> bool
end = struct

fun shiftl x n =
  Word.<< (x, Word.fromLargeInt (Int.toLarge n))

fun shiftr x n =
  Word.>> (x, Word.fromLargeInt (Int.toLarge n))

fun shiftr_signed x n =
  Word.~>> (x, Word.fromLargeInt (Int.toLarge n))

fun test_bit x n =
  Word.andb (x, Word.<< (0wx1, Word.fromLargeInt (Int.toLarge n))) <> Word.fromInt 0

end; (* struct Uint *)




structure Timing : sig
  val start_timer: unit -> unit
  val save_time: string -> unit
  val get_timings: unit -> (string * Time.time) list
  val set_cpu: bool -> unit
end = struct

  open Timer;

  val is_cpu = Unsynchronized.ref false;
  fun set_cpu b = is_cpu := b;

  val cpu_timer: cpu_timer option Unsynchronized.ref = Unsynchronized.ref NONE;
  val real_timer: real_timer option Unsynchronized.ref = Unsynchronized.ref NONE;

  val timings = Unsynchronized.ref [];
  fun start_timer () = (
    if !is_cpu then
      cpu_timer := SOME (startCPUTimer ())
    else
      real_timer := SOME (startRealTimer ()));
  fun get_elapsed () = (
    if !is_cpu then
      #usr (!cpu_timer |> the |> checkCPUTimer)
    else
      (!real_timer |> the |> checkRealTimer));
  fun save_time s = (timings := ((s, get_elapsed ()) :: !timings));
  fun get_timings () = !timings;
end


(* Test that words can handle numbers between 0 and 31 *)
val _ = if 5 <= Word.wordSize then () else raise (Fail ("wordSize less than 5"));

structure Uint32 : sig
  val shiftl : Word32.word -> Int.int -> Word32.word
  val shiftr : Word32.word -> Int.int -> Word32.word
  val shiftr_signed : Word32.word -> Int.int -> Word32.word
  val test_bit : Word32.word -> Int.int -> bool
end = struct

fun shiftl x n =
  Word32.<< (x, Word.fromLargeInt (Int.toLarge n))

fun shiftr x n =
  Word32.>> (x, Word.fromLargeInt (Int.toLarge n))

fun shiftr_signed x n =
  Word32.~>> (x, Word.fromLargeInt (Int.toLarge n))

fun test_bit x n =
  Word32.andb (x, Word32.<< (0wx1, Word.fromLargeInt (Int.toLarge n))) <> Word32.fromInt 0

end; (* struct Uint32 *)


structure Integer: sig
  val div_mod: int -> int -> int * int
end = struct
  fun div_mod i j = (i div j, i mod j)
end







structure Tracing : sig
  val count_up : unit -> unit
  val get_count : unit -> int
end = struct
  val counter = Unsynchronized.ref 0;
  fun count_up () = (counter := !counter + 1);
  fun get_count () = !counter;
end



fun imp_for_inner i u c f s =
  let
    fun imp_for1 i u f s =
      if Int.<= (u, i) then (fn () => s)
      else if c s () then imp_for1 (i + 1) u f (f i s ())
      else (fn () => s)
  in imp_for1 i u f s end;

fun imp_fora_inner i u f s =
  let
    fun imp_for1 i u f s =
      if Int.<= (u, i) then (fn () => s)
      else imp_for1 (i + 1) u f (f i s ())
  in imp_for1 i u f s end;





   fun array_blit src si dst di len = (
      src=dst andalso raise Fail ("array_blit: Same arrays");
      ArraySlice.copy {
        di = Int.toInt di,
        src = ArraySlice.slice (src,Int.toInt si,SOME (Int.toInt len)),
        dst = dst})

    fun array_nth_oo v a i () = Array.sub(a,Int.toInt i) handle Subscript => v | Overflow => v
    fun array_upd_oo f i x a () = 
      (Array.update(a,Int.toInt i,x); a) handle Subscript => f () | Overflow => f ()





structure Str_Literal : sig
  type int = Int.int
  val literal_of_asciis : int list -> string
  val asciis_of_literal : string -> int list
end = struct

open Int;

fun map f [] = []
  | map f (x :: xs) = f x :: map f xs; (* deliberate clone not relying on List._ structure *)

fun check_ascii k =
  if 0 <= k andalso k < 128
  then k
  else raise Fail "Non-ASCII character in literal";

val char_of_ascii = Char.chr o toInt o (fn k => k mod 128);

val ascii_of_char = check_ascii o fromInt o Char.ord;

val literal_of_asciis = String.implode o map char_of_ascii;

val asciis_of_literal = map ascii_of_char o String.explode;

end;





structure Converter : sig
  datatype inta = Int_of_integer of int
  val integer_of_int : inta -> int
  type num
  type nat
  val integer_of_nat : nat -> int
  val nat_of_integer : int -> nat
  type char
  type rat
  type color
  type ('a, 'b) rbt
  datatype 'a dBMEntry = Le of 'a | Lt of 'a | INF
  datatype 'a act = In of 'a | Out of 'a | Sil of 'a
  val explode : string -> char list
  datatype 'a formula = Atom of 'a | Bot | Not of 'a formula |
    And of 'a formula * 'a formula | Or of 'a formula * 'a formula |
    Imp of 'a formula * 'a formula
  type json
  datatype func = Func of string
  datatype 'a primitive_numeric_expression = PNE of func * 'a list
  datatype 'a numeric_expression = ConstantExpr of rat | DurationExpr |
    AddExpr of 'a numeric_expression * 'a numeric_expression |
    SubExpr of 'a numeric_expression * 'a numeric_expression |
    MulExpr of 'a numeric_expression * 'a numeric_expression |
    DivExpr of 'a numeric_expression * 'a numeric_expression |
    SinExpr of 'a numeric_expression | CosExpr of 'a numeric_expression |
    ExpExpr of 'a numeric_expression | PiExpr |
    FunctionExpr of 'a primitive_numeric_expression
  datatype predicate = Pred of string
  datatype 'a atom = PredAtm of predicate * 'a list | EqAtm of 'a * 'a |
    NumericEqAtm of 'a numeric_expression * 'a numeric_expression |
    NumericLessAtm of 'a numeric_expression * 'a numeric_expression |
    NumericLEAtm of 'a numeric_expression * 'a numeric_expression |
    NumericGreaterAtm of 'a numeric_expression * 'a numeric_expression |
    NumericGEAtm of 'a numeric_expression * 'a numeric_expression
  datatype variable = Vara of string
  datatype object = Obj of string
  datatype term = VAR of variable | CONST of object
  datatype typea = Either of string list
  datatype ('a, 'b) bexp = True | Nota of ('a, 'b) bexp |
    Anda of ('a, 'b) bexp * ('a, 'b) bexp | Ora of ('a, 'b) bexp * ('a, 'b) bexp
    | Imply of ('a, 'b) bexp * ('a, 'b) bexp |
    Eqa of ('a, 'b) exp * ('a, 'b) exp | Lea of ('a, 'b) exp * ('a, 'b) exp |
    Ltb of ('a, 'b) exp * ('a, 'b) exp | Ge of ('a, 'b) exp * ('a, 'b) exp |
    Gta of ('a, 'b) exp * ('a, 'b) exp
  and ('a, 'b) exp = Const of 'b | Var of 'a |
    If_then_else of ('a, 'b) bexp * ('a, 'b) exp * ('a, 'b) exp |
    Binop of ('b -> 'b -> 'b) * ('a, 'b) exp * ('a, 'b) exp |
    Unop of ('b -> 'b) * ('a, 'b) exp
  datatype numeric_effect_op = Assign | ScaleUp | ScaleDown | Increase |
    Decrease
  datatype 'a numeric_effect =
    NumericEffect of
      numeric_effect_op * 'a primitive_numeric_expression *
        'a numeric_expression
  datatype 'a ast_effect =
    Effect of
      'a atom formula list * 'a atom formula list * 'a numeric_effect list
  datatype ('a, 'b) acconstraint = LTa of 'a * 'b | LEa of 'a * 'b |
    EQa of 'a * 'b | GTa of 'a * 'b | GEa of 'a * 'b
  datatype duration_op = EQ | LEQ | GEQ
  datatype 'a duration_constraint =
    DurationConstraint of duration_op * 'a numeric_expression
  datatype temporal_annotation = At_Start | Over_All | At_End
  datatype ast_temporal_durative_action_body =
    DurativeActionBody of
      (temporal_annotation * term duration_constraint) list *
        (temporal_annotation * term atom formula) list *
        (temporal_annotation * term ast_effect) list
  datatype ast_simple_action_body =
    SimpleActionBody of term atom formula * term ast_effect
  datatype ast_action_head = ActionHead of string * (variable * typea) list
  datatype ast_temporal_action_schema =
    SimpleActionSchemaa of ast_action_head * ast_simple_action_body |
    DurativeActionSchema of ast_action_head * ast_temporal_durative_action_body
  datatype ('a, 'b) sum = Inl of 'a | Inr of 'b
  type time
  datatype 'a result = Result of 'a | Error of string list
  datatype predicate_decl = PredDecl of predicate * typea list
  datatype function_decl = FuncDecl of func * typea list
  datatype 'a ast_domain =
    Domain of
      (string * string) list * predicate_decl list * function_decl list *
        (object * typea) list * 'a list
  type 'a len_list
  datatype 'a ast_problem =
    Problem of
      'a ast_domain * (object * typea) list * object atom formula list *
        object atom formula
  datatype continuous_effect_op = ContinuousIncrease | ContinuousDecrease
  datatype 'a ast_continuous_effect =
    ContinuousEffect of
      continuous_effect_op * 'a primitive_numeric_expression *
        'a numeric_expression
  type resulta
  datatype ('a, 'b, 'c, 'd) sexp = Truea | Notb of ('a, 'b, 'c, 'd) sexp |
    Andb of ('a, 'b, 'c, 'd) sexp * ('a, 'b, 'c, 'd) sexp |
    Orb of ('a, 'b, 'c, 'd) sexp * ('a, 'b, 'c, 'd) sexp |
    Implya of ('a, 'b, 'c, 'd) sexp * ('a, 'b, 'c, 'd) sexp | Eqb of 'c * 'd |
    Leb of 'c * 'd | Ltc of 'c * 'd | Gea of 'c * 'd | Gtb of 'c * 'd |
    Loc of 'a * 'b
  datatype mode = Impl1 | Impl2 | Impl3 | Buechi | Debug
  datatype ('a, 'b, 'c, 'd) formulaa = EX of ('a, 'b, 'c, 'd) sexp |
    EG of ('a, 'b, 'c, 'd) sexp | AX of ('a, 'b, 'c, 'd) sexp |
    AG of ('a, 'b, 'c, 'd) sexp |
    Leadsto of ('a, 'b, 'c, 'd) sexp * ('a, 'b, 'c, 'd) sexp
  datatype 'a state_space =
    Reachable_Set of (('a list * inta list) * (inta dBMEntry list) list) list |
    Buechi_Set of (('a list * inta list) * (inta dBMEntry list * nat) list) list
  val fract : inta -> inta -> rat
  val of_int : inta -> rat
  val bigOr : 'a formula list -> 'a formula
  val implode : char list -> string
  val bigAnd : 'a formula list -> 'a formula
  val map_numeric_expression :
    ('a -> 'b) -> 'a numeric_expression -> 'b numeric_expression
  val map_atom : ('a -> 'b) -> 'a atom -> 'b atom
  val predicate : 'a atom -> predicate
  val rbt_to_list : ('a, 'b) rbt -> 'a list
  val map_numeric_effect : ('a -> 'b) -> 'a numeric_effect -> 'b numeric_effect
  val rat_of_digits_pair : nat list * nat list -> rat
  val check_and_make_network_opt :
    ast_temporal_action_schema ast_problem ->
      (string list *
        (string list *
          ((nat -> nat -> string) *
            ((string -> nat) *
              (string list *
                ((nat list *
                   (nat list *
                     ((nat *
                        ((string, inta) bexp *
                          ((string, inta) acconstraint list *
                            (string act *
                              ((string * (string, inta) exp) list *
                                (string list * nat)))))) list *
                       (nat * (string, inta) acconstraint list) list))) list *
                  ((string * (inta * inta)) list *
                    ((nat, nat, string, inta) formulaa *
                      (nat list * (string * inta) list))))))))) option
  val parse_convert_run : bool -> string -> (unit -> string result)
  val check_and_cert_pddl_problem_no_return :
    ast_temporal_action_schema ast_problem ->
      mode ->
        nat ->
          (string list *
             (string list *
               ((nat -> nat -> string) *
                 ((string -> nat) *
                   (string list *
                     ((nat list *
                        (nat list *
                          ((nat *
                             ((string, inta) bexp *
                               ((string, inta) acconstraint list *
                                 (string act *
                                   ((string * (string, inta) exp) list *
                                     (string list * nat)))))) list *
                            (nat *
                              (string, inta) acconstraint list) list))) list *
                       ((string * (inta * inta)) list *
                         ((nat, nat, string, inta) formulaa *
                           (nat list * (string * inta) list)))))))) ->
            (((string -> nat) *
               ((string -> nat) *
                 ((nat -> nat -> nat) *
                   ((nat -> string) *
                     ((nat -> string) * (nat -> nat -> nat)))))) *
              inta state_space) option) ->
            bool -> (unit -> unit)
  val parse_convert_check :
    mode ->
      nat ->
        bool -> string -> string -> inta state_space -> bool -> (unit -> unit)
end = struct

datatype inta = Int_of_integer of int;

fun integer_of_int (Int_of_integer k) = k;

fun equal_inta k l = integer_of_int k = integer_of_int l;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_int = {equal = equal_inta} : inta equal;

datatype typerepa = Typerep of string * typerepa list;

datatype 'a itself = Type;

fun typerep_inta t = Typerep ("Int.int", []);

type 'a typerep = {typerep : 'a itself -> typerepa};
val typerep = #typerep : 'a typerep -> 'a itself -> typerepa;

type 'a countable = {};

type 'a heap = {countable_heap : 'a countable, typerep_heap : 'a typerep};
val countable_heap = #countable_heap : 'a heap -> 'a countable;
val typerep_heap = #typerep_heap : 'a heap -> 'a typerep;

val countable_int = {} : inta countable;

val typerep_int = {typerep = typerep_inta} : inta typerep;

val heap_int = {countable_heap = countable_int, typerep_heap = typerep_int} :
  inta heap;

fun uminus_inta k = Int_of_integer (~ (integer_of_int k));

val zero_inta : inta = Int_of_integer (0 : Int.int);

fun apsnd f (x, y) = (x, f y);

datatype num = One | Bit0 of num | Bit1 of num;

fun divmod_integer k l =
  (if k = (0 : Int.int) then ((0 : Int.int), (0 : Int.int))
    else (if (0 : Int.int) < l
           then (if (0 : Int.int) < k then Integer.div_mod (abs k) (abs l)
                  else let
                         val (r, s) = Integer.div_mod (abs k) (abs l);
                       in
                         (if s = (0 : Int.int) then (~ r, (0 : Int.int))
                           else (~ r - (1 : Int.int), l - s))
                       end)
           else (if l = (0 : Int.int) then ((0 : Int.int), k)
                  else apsnd (fn a => ~ a)
                         (if k < (0 : Int.int)
                           then Integer.div_mod (abs k) (abs l)
                           else let
                                  val (r, s) = Integer.div_mod (abs k) (abs l);
                                in
                                  (if s = (0 : Int.int)
                                    then (~ r, (0 : Int.int))
                                    else (~ r - (1 : Int.int), ~ l - s))
                                end))));

fun snd (x1, x2) = x2;

fun modulo_integer k l = snd (divmod_integer k l);

datatype nat = Nat of int;

fun integer_of_nat (Nat x) = x;

fun modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

fun fst (x1, x2) = x1;

fun divide_integer k l = fst (divmod_integer k l);

fun divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

fun equal_nata m n = integer_of_nat m = integer_of_nat n;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => a <= b), less = (fn a => fn b => a < b)} :
  int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : Int.int) k);

val zero_nata : nat = Nat (0 : Int.int);

val one_nata : nat = Nat (1 : Int.int);

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

fun string_of_digit n =
  (if equal_nata n zero_nata
    then [Chara (false, false, false, false, true, true, false, false)]
    else (if equal_nata n one_nata
           then [Chara (true, false, false, false, true, true, false, false)]
           else (if equal_nata n (nat_of_integer (2 : Int.int))
                  then [Chara (false, true, false, false, true, true, false,
                                false)]
                  else (if equal_nata n (nat_of_integer (3 : Int.int))
                         then [Chara (true, true, false, false, true, true,
                                       false, false)]
                         else (if equal_nata n (nat_of_integer (4 : Int.int))
                                then [Chara
(false, false, true, false, true, true, false, false)]
                                else (if equal_nata n
   (nat_of_integer (5 : Int.int))
                                       then [Chara
       (true, false, true, false, true, true, false, false)]
                                       else (if equal_nata n
          (nat_of_integer (6 : Int.int))
      then [Chara (false, true, true, false, true, true, false, false)]
      else (if equal_nata n (nat_of_integer (7 : Int.int))
             then [Chara (true, true, true, false, true, true, false, false)]
             else (if equal_nata n (nat_of_integer (8 : Int.int))
                    then [Chara (false, false, false, true, true, true, false,
                                  false)]
                    else [Chara (true, false, false, true, true, true, false,
                                  false)])))))))));

fun less_nat m n = integer_of_nat m < integer_of_nat n;

fun shows_string x = (fn a => x @ a);

fun showsp_nat p n =
  (if less_nat n (nat_of_integer (10 : Int.int))
    then shows_string (string_of_digit n)
    else showsp_nat p (divide_nat n (nat_of_integer (10 : Int.int))) o
           shows_string
             (string_of_digit
               (modulo_nat n (nat_of_integer (10 : Int.int)))));

fun less_int k l = integer_of_int k < integer_of_int l;

fun nat x = (nat_of_integer o integer_of_int) x;

fun showsp_int p i =
  (if less_int i zero_inta
    then shows_string
           [Chara (true, false, true, true, false, true, false, false)] o
           showsp_nat p (nat (uminus_inta i))
    else showsp_nat p (nat i));

fun shows_prec_int x = showsp_int x;

fun shows_sep s sep [] = shows_string []
  | shows_sep s sep [x] = s x
  | shows_sep s sep (x :: v :: va) = s x o sep o shows_sep s sep (v :: va);

fun null [] = true
  | null (x :: xs) = false;

fun shows_list_gen showsx e l s r xs =
  (if null xs then shows_string e
    else shows_string l o shows_sep showsx (shows_string s) xs o
           shows_string r);

fun showsp_list s p xs =
  shows_list_gen (s zero_nata)
    [Chara (true, true, false, true, true, false, true, false),
      Chara (true, false, true, true, true, false, true, false)]
    [Chara (true, true, false, true, true, false, true, false)]
    [Chara (false, false, true, true, false, true, false, false),
      Chara (false, false, false, false, false, true, false, false)]
    [Chara (true, false, true, true, true, false, true, false)] xs;

fun shows_list_int x = showsp_list shows_prec_int zero_nata x;

type 'a show =
  {shows_prec : nat -> 'a -> char list -> char list,
    shows_list : 'a list -> char list -> char list};
val shows_prec = #shows_prec : 'a show -> nat -> 'a -> char list -> char list;
val shows_list = #shows_list : 'a show -> 'a list -> char list -> char list;

val show_int = {shows_prec = shows_prec_int, shows_list = shows_list_int} :
  inta show;

val one_inta : inta = Int_of_integer (1 : Int.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_int = {one = one_inta} : inta one;

fun plus_inta k l = Int_of_integer (integer_of_int k + integer_of_int l);

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_int = {plus = plus_inta} : inta plus;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_int = {zero = zero_inta} : inta zero;

fun times_inta k l = Int_of_integer (integer_of_int k * integer_of_int l);

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val times_int = {times = times_inta} : inta times;

val power_int = {one_power = one_int, times_power = times_int} : inta power;

fun minus_inta k l = Int_of_integer (integer_of_int k - integer_of_int l);

type 'a minus = {minusa : 'a -> 'a -> 'a};
val minusa = #minusa : 'a minus -> 'a -> 'a -> 'a;

val minus_int = {minusa = minus_inta} : inta minus;

fun less_eq_int k l = integer_of_int k <= integer_of_int l;

fun min_int x y = (if less_eq_int x y then x else y);

fun inf_inta x = min_int x;

type 'a inf = {inf : 'a -> 'a -> 'a};
val inf = #inf : 'a inf -> 'a -> 'a -> 'a;

val inf_int = {inf = inf_inta} : inta inf;

val ord_int = {less_eq = less_eq_int, less = less_int} : inta ord;

fun sup_inta x = max ord_int x;

type 'a sup = {sup : 'a -> 'a -> 'a};
val sup = #sup : 'a sup -> 'a -> 'a -> 'a;

val sup_int = {sup = sup_inta} : inta sup;

type 'a uminus = {uminus : 'a -> 'a};
val uminus = #uminus : 'a uminus -> 'a -> 'a;

val uminus_int = {uminus = uminus_inta} : inta uminus;

datatype ordera = Eq | Lta | Gt;

fun eq A_ a b = equal A_ a b;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

fun comparator_of (A1_, A2_) x y =
  (if less ((ord_preorder o preorder_order o order_linorder) A2_) x y then Lta
    else (if eq A1_ x y then Eq else Gt));

val preorder_int = {ord_preorder = ord_int} : inta preorder;

val order_int = {preorder_order = preorder_int} : inta order;

val linorder_int = {order_linorder = order_int} : inta linorder;

fun compare_inta x = comparator_of (equal_int, linorder_int) x;

type 'a compare = {compare : 'a -> 'a -> ordera};
val compare = #compare : 'a compare -> 'a -> 'a -> ordera;

val compare_int = {compare = compare_inta} : inta compare;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};
val semigroup_add_cancel_semigroup_add = #semigroup_add_cancel_semigroup_add :
  'a cancel_semigroup_add -> 'a semigroup_add;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a group_add =
  {cancel_semigroup_add_group_add : 'a cancel_semigroup_add,
    minus_group_add : 'a minus, monoid_add_group_add : 'a monoid_add,
    uminus_group_add : 'a uminus};
val cancel_semigroup_add_group_add = #cancel_semigroup_add_group_add :
  'a group_add -> 'a cancel_semigroup_add;
val minus_group_add = #minus_group_add : 'a group_add -> 'a minus;
val monoid_add_group_add = #monoid_add_group_add :
  'a group_add -> 'a monoid_add;
val uminus_group_add = #uminus_group_add : 'a group_add -> 'a uminus;

val semigroup_add_int = {plus_semigroup_add = plus_int} : inta semigroup_add;

val cancel_semigroup_add_int =
  {semigroup_add_cancel_semigroup_add = semigroup_add_int} :
  inta cancel_semigroup_add;

val monoid_add_int =
  {semigroup_add_monoid_add = semigroup_add_int, zero_monoid_add = zero_int} :
  inta monoid_add;

val group_add_int =
  {cancel_semigroup_add_group_add = cancel_semigroup_add_int,
    minus_group_add = minus_int, monoid_add_group_add = monoid_add_int,
    uminus_group_add = uminus_int}
  : inta group_add;

type 'a semilattice_sup =
  {sup_semilattice_sup : 'a sup, order_semilattice_sup : 'a order};
val sup_semilattice_sup = #sup_semilattice_sup : 'a semilattice_sup -> 'a sup;
val order_semilattice_sup = #order_semilattice_sup :
  'a semilattice_sup -> 'a order;

type 'a semilattice_inf =
  {inf_semilattice_inf : 'a inf, order_semilattice_inf : 'a order};
val inf_semilattice_inf = #inf_semilattice_inf : 'a semilattice_inf -> 'a inf;
val order_semilattice_inf = #order_semilattice_inf :
  'a semilattice_inf -> 'a order;

type 'a lattice =
  {semilattice_inf_lattice : 'a semilattice_inf,
    semilattice_sup_lattice : 'a semilattice_sup};
val semilattice_inf_lattice = #semilattice_inf_lattice :
  'a lattice -> 'a semilattice_inf;
val semilattice_sup_lattice = #semilattice_sup_lattice :
  'a lattice -> 'a semilattice_sup;

val semilattice_sup_int =
  {sup_semilattice_sup = sup_int, order_semilattice_sup = order_int} :
  inta semilattice_sup;

val semilattice_inf_int =
  {inf_semilattice_inf = inf_int, order_semilattice_inf = order_int} :
  inta semilattice_inf;

val lattice_int =
  {semilattice_inf_lattice = semilattice_inf_int,
    semilattice_sup_lattice = semilattice_sup_int}
  : inta lattice;

val ceq_inta : (inta -> inta -> bool) option = SOME equal_inta;

type 'a ceq = {ceq : ('a -> 'a -> bool) option};
val ceq = #ceq : 'a ceq -> ('a -> 'a -> bool) option;

val ceq_int = {ceq = ceq_inta} : inta ceq;

fun def_hashmap_size_int x = (fn _ => nat_of_integer (16 : Int.int)) x;

type 'a hashable =
  {hashcode : 'a -> Word32.word, def_hashmap_size : 'a itself -> nat};
val hashcode = #hashcode : 'a hashable -> 'a -> Word32.word;
val def_hashmap_size = #def_hashmap_size : 'a hashable -> 'a itself -> nat;

fun uint32_of_int i = Word32.fromLargeInt (Int.toLarge (integer_of_int i));

fun hashcode_int i = uint32_of_int i;

val hashable_int =
  {hashcode = hashcode_int, def_hashmap_size = def_hashmap_size_int} :
  inta hashable;

datatype ('a, 'b) phantom = Phantom of 'b;

datatype set_impla = Set_Choose | Set_Collect | Set_DList | Set_RBT |
  Set_Monada;

val set_impl_inta : (inta, set_impla) phantom = Phantom Set_RBT;

type 'a set_impl = {set_impl : ('a, set_impla) phantom};
val set_impl = #set_impl : 'a set_impl -> ('a, set_impla) phantom;

val set_impl_int = {set_impl = set_impl_inta} : inta set_impl;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add,
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add,
    minus_cancel_ab_semigroup_add : 'a minus};
val ab_semigroup_add_cancel_ab_semigroup_add =
  #ab_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a ab_semigroup_add;
val cancel_semigroup_add_cancel_ab_semigroup_add =
  #cancel_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a cancel_semigroup_add;
val minus_cancel_ab_semigroup_add = #minus_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a minus;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add,
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};
val cancel_ab_semigroup_add_cancel_comm_monoid_add =
  #cancel_ab_semigroup_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a cancel_ab_semigroup_add;
val comm_monoid_add_cancel_comm_monoid_add =
  #comm_monoid_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a comm_monoid_add;

type 'a ab_group_add =
  {cancel_comm_monoid_add_ab_group_add : 'a cancel_comm_monoid_add,
    group_add_ab_group_add : 'a group_add};
val cancel_comm_monoid_add_ab_group_add = #cancel_comm_monoid_add_ab_group_add :
  'a ab_group_add -> 'a cancel_comm_monoid_add;
val group_add_ab_group_add = #group_add_ab_group_add :
  'a ab_group_add -> 'a group_add;

val ab_semigroup_add_int = {semigroup_add_ab_semigroup_add = semigroup_add_int}
  : inta ab_semigroup_add;

val cancel_ab_semigroup_add_int =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int,
    minus_cancel_ab_semigroup_add = minus_int}
  : inta cancel_ab_semigroup_add;

val comm_monoid_add_int =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int,
    monoid_add_comm_monoid_add = monoid_add_int}
  : inta comm_monoid_add;

val cancel_comm_monoid_add_int =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_int,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
  : inta cancel_comm_monoid_add;

val ab_group_add_int =
  {cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_int,
    group_add_ab_group_add = group_add_int}
  : inta ab_group_add;

val cEnum_int :
  (inta list * (((inta -> bool) -> bool) * ((inta -> bool) -> bool))) option
  = NONE;

type 'a cenum =
  {cEnum :
     ('a list * ((('a -> bool) -> bool) * (('a -> bool) -> bool))) option};
val cEnum = #cEnum :
  'a cenum ->
    ('a list * ((('a -> bool) -> bool) * (('a -> bool) -> bool))) option;

val cenum_int = {cEnum = cEnum_int} : inta cenum;

val finite_UNIV_inta : (inta, bool) phantom = Phantom false;

type 'a finite_UNIV = {finite_UNIV : ('a, bool) phantom};
val finite_UNIV = #finite_UNIV : 'a finite_UNIV -> ('a, bool) phantom;

val finite_UNIV_int = {finite_UNIV = finite_UNIV_inta} : inta finite_UNIV;

val ccompare_inta : (inta -> inta -> ordera) option = SOME compare_inta;

type 'a ccompare = {ccompare : ('a -> 'a -> ordera) option};
val ccompare = #ccompare : 'a ccompare -> ('a -> 'a -> ordera) option;

val ccompare_int = {ccompare = ccompare_inta} : inta ccompare;

type 'a ordered_ab_semigroup_add =
  {ab_semigroup_add_ordered_ab_semigroup_add : 'a ab_semigroup_add,
    order_ordered_ab_semigroup_add : 'a order};
val ab_semigroup_add_ordered_ab_semigroup_add =
  #ab_semigroup_add_ordered_ab_semigroup_add :
  'a ordered_ab_semigroup_add -> 'a ab_semigroup_add;
val order_ordered_ab_semigroup_add = #order_ordered_ab_semigroup_add :
  'a ordered_ab_semigroup_add -> 'a order;

type 'a strict_ordered_ab_semigroup_add =
  {ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add :
     'a ordered_ab_semigroup_add};
val ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add =
  #ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add :
  'a strict_ordered_ab_semigroup_add -> 'a ordered_ab_semigroup_add;

type 'a ordered_cancel_ab_semigroup_add =
  {cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
     'a cancel_ab_semigroup_add,
    strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
      'a strict_ordered_ab_semigroup_add};
val cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
  #cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
  'a ordered_cancel_ab_semigroup_add -> 'a cancel_ab_semigroup_add;
val strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
  #strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
  'a ordered_cancel_ab_semigroup_add -> 'a strict_ordered_ab_semigroup_add;

type 'a ordered_ab_semigroup_add_imp_le =
  {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le :
     'a ordered_cancel_ab_semigroup_add};
val ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le =
  #ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le :
  'a ordered_ab_semigroup_add_imp_le -> 'a ordered_cancel_ab_semigroup_add;

type 'a strict_ordered_comm_monoid_add =
  {comm_monoid_add_strict_ordered_comm_monoid_add : 'a comm_monoid_add,
    strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add :
      'a strict_ordered_ab_semigroup_add};
val comm_monoid_add_strict_ordered_comm_monoid_add =
  #comm_monoid_add_strict_ordered_comm_monoid_add :
  'a strict_ordered_comm_monoid_add -> 'a comm_monoid_add;
val strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add =
  #strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add :
  'a strict_ordered_comm_monoid_add -> 'a strict_ordered_ab_semigroup_add;

type 'a ordered_comm_monoid_add =
  {comm_monoid_add_ordered_comm_monoid_add : 'a comm_monoid_add,
    ordered_ab_semigroup_add_ordered_comm_monoid_add :
      'a ordered_ab_semigroup_add};
val comm_monoid_add_ordered_comm_monoid_add =
  #comm_monoid_add_ordered_comm_monoid_add :
  'a ordered_comm_monoid_add -> 'a comm_monoid_add;
val ordered_ab_semigroup_add_ordered_comm_monoid_add =
  #ordered_ab_semigroup_add_ordered_comm_monoid_add :
  'a ordered_comm_monoid_add -> 'a ordered_ab_semigroup_add;

type 'a ordered_cancel_comm_monoid_add =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add :
     'a ordered_cancel_ab_semigroup_add,
    ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
      'a ordered_comm_monoid_add,
    strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
      'a strict_ordered_comm_monoid_add};
val ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add =
  #ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a ordered_cancel_ab_semigroup_add;
val ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
  #ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a ordered_comm_monoid_add;
val strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
  #strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a strict_ordered_comm_monoid_add;

type 'a ordered_ab_semigroup_monoid_add_imp_le =
  {cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
     'a cancel_comm_monoid_add,
    ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le :
      'a ordered_ab_semigroup_add_imp_le,
    ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
      'a ordered_cancel_comm_monoid_add};
val cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
  #cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le -> 'a cancel_comm_monoid_add;
val ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le =
  #ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le ->
    'a ordered_ab_semigroup_add_imp_le;
val ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
  #ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le ->
    'a ordered_cancel_comm_monoid_add;

type 'a ordered_ab_group_add =
  {ab_group_add_ordered_ab_group_add : 'a ab_group_add,
    ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add :
      'a ordered_ab_semigroup_monoid_add_imp_le};
val ab_group_add_ordered_ab_group_add = #ab_group_add_ordered_ab_group_add :
  'a ordered_ab_group_add -> 'a ab_group_add;
val ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add =
  #ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add :
  'a ordered_ab_group_add -> 'a ordered_ab_semigroup_monoid_add_imp_le;

val ordered_ab_semigroup_add_int =
  {ab_semigroup_add_ordered_ab_semigroup_add = ab_semigroup_add_int,
    order_ordered_ab_semigroup_add = order_int}
  : inta ordered_ab_semigroup_add;

val strict_ordered_ab_semigroup_add_int =
  {ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add =
     ordered_ab_semigroup_add_int}
  : inta strict_ordered_ab_semigroup_add;

val ordered_cancel_ab_semigroup_add_int =
  {cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
     cancel_ab_semigroup_add_int,
    strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
      strict_ordered_ab_semigroup_add_int}
  : inta ordered_cancel_ab_semigroup_add;

val ordered_ab_semigroup_add_imp_le_int =
  {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le =
     ordered_cancel_ab_semigroup_add_int}
  : inta ordered_ab_semigroup_add_imp_le;

val strict_ordered_comm_monoid_add_int =
  {comm_monoid_add_strict_ordered_comm_monoid_add = comm_monoid_add_int,
    strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add =
      strict_ordered_ab_semigroup_add_int}
  : inta strict_ordered_comm_monoid_add;

val ordered_comm_monoid_add_int =
  {comm_monoid_add_ordered_comm_monoid_add = comm_monoid_add_int,
    ordered_ab_semigroup_add_ordered_comm_monoid_add =
      ordered_ab_semigroup_add_int}
  : inta ordered_comm_monoid_add;

val ordered_cancel_comm_monoid_add_int =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add =
     ordered_cancel_ab_semigroup_add_int,
    ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
      ordered_comm_monoid_add_int,
    strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
      strict_ordered_comm_monoid_add_int}
  : inta ordered_cancel_comm_monoid_add;

val ordered_ab_semigroup_monoid_add_imp_le_int =
  {cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
     cancel_comm_monoid_add_int,
    ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le =
      ordered_ab_semigroup_add_imp_le_int,
    ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
      ordered_cancel_comm_monoid_add_int}
  : inta ordered_ab_semigroup_monoid_add_imp_le;

val ordered_ab_group_add_int =
  {ab_group_add_ordered_ab_group_add = ab_group_add_int,
    ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add =
      ordered_ab_semigroup_monoid_add_imp_le_int}
  : inta ordered_ab_group_add;

type 'a linordered_ab_semigroup_add =
  {ordered_ab_semigroup_add_linordered_ab_semigroup_add :
     'a ordered_ab_semigroup_add,
    linorder_linordered_ab_semigroup_add : 'a linorder};
val ordered_ab_semigroup_add_linordered_ab_semigroup_add =
  #ordered_ab_semigroup_add_linordered_ab_semigroup_add :
  'a linordered_ab_semigroup_add -> 'a ordered_ab_semigroup_add;
val linorder_linordered_ab_semigroup_add = #linorder_linordered_ab_semigroup_add
  : 'a linordered_ab_semigroup_add -> 'a linorder;

type 'a linordered_cancel_ab_semigroup_add =
  {linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add :
     'a linordered_ab_semigroup_add,
    ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add :
      'a ordered_ab_semigroup_add_imp_le};
val linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add =
  #linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add :
  'a linordered_cancel_ab_semigroup_add -> 'a linordered_ab_semigroup_add;
val ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add =
  #ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add :
  'a linordered_cancel_ab_semigroup_add -> 'a ordered_ab_semigroup_add_imp_le;

type 'a linordered_ab_monoid_add =
  {linordered_ab_semigroup_add_linordered_ab_monoid_add :
     'a linordered_ab_semigroup_add,
    ordered_comm_monoid_add_linordered_ab_monoid_add :
      'a ordered_comm_monoid_add};
val linordered_ab_semigroup_add_linordered_ab_monoid_add =
  #linordered_ab_semigroup_add_linordered_ab_monoid_add :
  'a linordered_ab_monoid_add -> 'a linordered_ab_semigroup_add;
val ordered_comm_monoid_add_linordered_ab_monoid_add =
  #ordered_comm_monoid_add_linordered_ab_monoid_add :
  'a linordered_ab_monoid_add -> 'a ordered_comm_monoid_add;

type 'a linordered_cancel_ab_monoid_add =
  {linordered_ab_monoid_add_linordered_cancel_ab_monoid_add :
     'a linordered_ab_monoid_add,
    linordered_cancel_ab_semigroup_add_linordered_cancel_ab_monoid_add :
      'a linordered_cancel_ab_semigroup_add};
val linordered_ab_monoid_add_linordered_cancel_ab_monoid_add =
  #linordered_ab_monoid_add_linordered_cancel_ab_monoid_add :
  'a linordered_cancel_ab_monoid_add -> 'a linordered_ab_monoid_add;
val linordered_cancel_ab_semigroup_add_linordered_cancel_ab_monoid_add =
  #linordered_cancel_ab_semigroup_add_linordered_cancel_ab_monoid_add :
  'a linordered_cancel_ab_monoid_add -> 'a linordered_cancel_ab_semigroup_add;

type 'a linordered_ab_group_add =
  {linordered_cancel_ab_monoid_add_linordered_ab_group_add :
     'a linordered_cancel_ab_monoid_add,
    ordered_ab_group_add_linordered_ab_group_add : 'a ordered_ab_group_add};
val linordered_cancel_ab_monoid_add_linordered_ab_group_add =
  #linordered_cancel_ab_monoid_add_linordered_ab_group_add :
  'a linordered_ab_group_add -> 'a linordered_cancel_ab_monoid_add;
val ordered_ab_group_add_linordered_ab_group_add =
  #ordered_ab_group_add_linordered_ab_group_add :
  'a linordered_ab_group_add -> 'a ordered_ab_group_add;

val linordered_ab_semigroup_add_int =
  {ordered_ab_semigroup_add_linordered_ab_semigroup_add =
     ordered_ab_semigroup_add_int,
    linorder_linordered_ab_semigroup_add = linorder_int}
  : inta linordered_ab_semigroup_add;

val linordered_cancel_ab_semigroup_add_int =
  {linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add =
     linordered_ab_semigroup_add_int,
    ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add =
      ordered_ab_semigroup_add_imp_le_int}
  : inta linordered_cancel_ab_semigroup_add;

val linordered_ab_monoid_add_int =
  {linordered_ab_semigroup_add_linordered_ab_monoid_add =
     linordered_ab_semigroup_add_int,
    ordered_comm_monoid_add_linordered_ab_monoid_add =
      ordered_comm_monoid_add_int}
  : inta linordered_ab_monoid_add;

val linordered_cancel_ab_monoid_add_int =
  {linordered_ab_monoid_add_linordered_cancel_ab_monoid_add =
     linordered_ab_monoid_add_int,
    linordered_cancel_ab_semigroup_add_linordered_cancel_ab_monoid_add =
      linordered_cancel_ab_semigroup_add_int}
  : inta linordered_cancel_ab_monoid_add;

val linordered_ab_group_add_int =
  {linordered_cancel_ab_monoid_add_linordered_ab_group_add =
     linordered_cancel_ab_monoid_add_int,
    ordered_ab_group_add_linordered_ab_group_add = ordered_ab_group_add_int}
  : inta linordered_ab_group_add;

fun proper_interval_int (SOME x) (SOME y) = less_int one_inta (minus_inta y x)
  | proper_interval_int NONE uv = true
  | proper_interval_int uu NONE = true;

fun cproper_interval_inta x = proper_interval_int x;

type 'a cproper_interval =
  {ccompare_cproper_interval : 'a ccompare,
    cproper_interval : 'a option -> 'a option -> bool};
val ccompare_cproper_interval = #ccompare_cproper_interval :
  'a cproper_interval -> 'a ccompare;
val cproper_interval = #cproper_interval :
  'a cproper_interval -> 'a option -> 'a option -> bool;

val cproper_interval_int =
  {ccompare_cproper_interval = ccompare_int,
    cproper_interval = cproper_interval_inta}
  : inta cproper_interval;

val equal_nat = {equal = equal_nata} : nat equal;

fun typerep_nata t = Typerep ("Nat.nat", []);

val countable_nat = {} : nat countable;

val typerep_nat = {typerep = typerep_nata} : nat typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  nat heap;

fun times_nata m n = Nat (integer_of_nat m * integer_of_nat n);

type 'a dvd = {times_dvd : 'a times};
val times_dvd = #times_dvd : 'a dvd -> 'a times;

val times_nat = {times = times_nata} : nat times;

val dvd_nat = {times_dvd = times_nat} : nat dvd;

fun shows_prec_nat x = showsp_nat x;

fun shows_list_nat x = showsp_list shows_prec_nat zero_nata x;

val show_nat = {shows_prec = shows_prec_nat, shows_list = shows_list_nat} :
  nat show;

val one_nat = {one = one_nata} : nat one;

fun plus_nata m n = Nat (integer_of_nat m + integer_of_nat n);

val plus_nat = {plus = plus_nata} : nat plus;

val zero_nat = {zero = zero_nata} : nat zero;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

val semigroup_add_nat = {plus_semigroup_add = plus_nat} : nat semigroup_add;

val numeral_nat =
  {one_numeral = one_nat, semigroup_add_numeral = semigroup_add_nat} :
  nat numeral;

val power_nat = {one_power = one_nat, times_power = times_nat} : nat power;

fun minus_nata m n =
  Nat (max ord_integer (0 : Int.int) (integer_of_nat m - integer_of_nat n));

val minus_nat = {minusa = minus_nata} : nat minus;

fun less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};
val times_semigroup_mult = #times_semigroup_mult :
  'a semigroup_mult -> 'a times;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add,
    semigroup_mult_semiring : 'a semigroup_mult};
val ab_semigroup_add_semiring = #ab_semigroup_add_semiring :
  'a semiring -> 'a ab_semigroup_add;
val semigroup_mult_semiring = #semigroup_mult_semiring :
  'a semiring -> 'a semigroup_mult;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add,
    mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 :
  'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 :
  'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add,
    semiring_0_semiring_0_cancel : 'a semiring_0};
val cancel_comm_monoid_add_semiring_0_cancel =
  #cancel_comm_monoid_add_semiring_0_cancel :
  'a semiring_0_cancel -> 'a cancel_comm_monoid_add;
val semiring_0_semiring_0_cancel = #semiring_0_semiring_0_cancel :
  'a semiring_0_cancel -> 'a semiring_0;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};
val semigroup_mult_ab_semigroup_mult = #semigroup_mult_ab_semigroup_mult :
  'a ab_semigroup_mult -> 'a semigroup_mult;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult,
    semiring_comm_semiring : 'a semiring};
val ab_semigroup_mult_comm_semiring = #ab_semigroup_mult_comm_semiring :
  'a comm_semiring -> 'a ab_semigroup_mult;
val semiring_comm_semiring = #semiring_comm_semiring :
  'a comm_semiring -> 'a semiring;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring,
    semiring_0_comm_semiring_0 : 'a semiring_0};
val comm_semiring_comm_semiring_0 = #comm_semiring_comm_semiring_0 :
  'a comm_semiring_0 -> 'a comm_semiring;
val semiring_0_comm_semiring_0 = #semiring_0_comm_semiring_0 :
  'a comm_semiring_0 -> 'a semiring_0;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0,
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};
val comm_semiring_0_comm_semiring_0_cancel =
  #comm_semiring_0_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a comm_semiring_0;
val semiring_0_cancel_comm_semiring_0_cancel =
  #semiring_0_cancel_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a semiring_0_cancel;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult,
    power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult :
  'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult,
    numeral_semiring_numeral : 'a numeral,
    semiring_semiring_numeral : 'a semiring};
val monoid_mult_semiring_numeral = #monoid_mult_semiring_numeral :
  'a semiring_numeral -> 'a monoid_mult;
val numeral_semiring_numeral = #numeral_semiring_numeral :
  'a semiring_numeral -> 'a numeral;
val semiring_semiring_numeral = #semiring_semiring_numeral :
  'a semiring_numeral -> 'a semiring;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral,
    semiring_0_semiring_1 : 'a semiring_0,
    zero_neq_one_semiring_1 : 'a zero_neq_one};
val semiring_numeral_semiring_1 = #semiring_numeral_semiring_1 :
  'a semiring_1 -> 'a semiring_numeral;
val semiring_0_semiring_1 = #semiring_0_semiring_1 :
  'a semiring_1 -> 'a semiring_0;
val zero_neq_one_semiring_1 = #zero_neq_one_semiring_1 :
  'a semiring_1 -> 'a zero_neq_one;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel,
    semiring_1_semiring_1_cancel : 'a semiring_1};
val semiring_0_cancel_semiring_1_cancel = #semiring_0_cancel_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_0_cancel;
val semiring_1_semiring_1_cancel = #semiring_1_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_1;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult,
    monoid_mult_comm_monoid_mult : 'a monoid_mult,
    dvd_comm_monoid_mult : 'a dvd};
val ab_semigroup_mult_comm_monoid_mult = #ab_semigroup_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a ab_semigroup_mult;
val monoid_mult_comm_monoid_mult = #monoid_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a monoid_mult;
val dvd_comm_monoid_mult = #dvd_comm_monoid_mult :
  'a comm_monoid_mult -> 'a dvd;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult,
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0,
    semiring_1_comm_semiring_1 : 'a semiring_1};
val comm_monoid_mult_comm_semiring_1 = #comm_monoid_mult_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_monoid_mult;
val comm_semiring_0_comm_semiring_1 = #comm_semiring_0_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_semiring_0;
val semiring_1_comm_semiring_1 = #semiring_1_comm_semiring_1 :
  'a comm_semiring_1 -> 'a semiring_1;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel,
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1,
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};
val comm_semiring_0_cancel_comm_semiring_1_cancel =
  #comm_semiring_0_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_0_cancel;
val comm_semiring_1_comm_semiring_1_cancel =
  #comm_semiring_1_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_1;
val semiring_1_cancel_comm_semiring_1_cancel =
  #semiring_1_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a semiring_1_cancel;

type 'a interval =
  {linorder_interval : 'a linorder,
    comm_semiring_1_cancel_interval : 'a comm_semiring_1_cancel};
val linorder_interval = #linorder_interval : 'a interval -> 'a linorder;
val comm_semiring_1_cancel_interval = #comm_semiring_1_cancel_interval :
  'a interval -> 'a comm_semiring_1_cancel;

val cancel_semigroup_add_nat =
  {semigroup_add_cancel_semigroup_add = semigroup_add_nat} :
  nat cancel_semigroup_add;

val ab_semigroup_add_nat = {semigroup_add_ab_semigroup_add = semigroup_add_nat}
  : nat ab_semigroup_add;

val cancel_ab_semigroup_add_nat =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_nat,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_nat,
    minus_cancel_ab_semigroup_add = minus_nat}
  : nat cancel_ab_semigroup_add;

val monoid_add_nat =
  {semigroup_add_monoid_add = semigroup_add_nat, zero_monoid_add = zero_nat} :
  nat monoid_add;

val comm_monoid_add_nat =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_nat,
    monoid_add_comm_monoid_add = monoid_add_nat}
  : nat comm_monoid_add;

val cancel_comm_monoid_add_nat =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_nat,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_nat}
  : nat cancel_comm_monoid_add;

val mult_zero_nat = {times_mult_zero = times_nat, zero_mult_zero = zero_nat} :
  nat mult_zero;

val semigroup_mult_nat = {times_semigroup_mult = times_nat} :
  nat semigroup_mult;

val semiring_nat =
  {ab_semigroup_add_semiring = ab_semigroup_add_nat,
    semigroup_mult_semiring = semigroup_mult_nat}
  : nat semiring;

val semiring_0_nat =
  {comm_monoid_add_semiring_0 = comm_monoid_add_nat,
    mult_zero_semiring_0 = mult_zero_nat, semiring_semiring_0 = semiring_nat}
  : nat semiring_0;

val semiring_0_cancel_nat =
  {cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_nat,
    semiring_0_semiring_0_cancel = semiring_0_nat}
  : nat semiring_0_cancel;

val ab_semigroup_mult_nat =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_nat} :
  nat ab_semigroup_mult;

val comm_semiring_nat =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_nat,
    semiring_comm_semiring = semiring_nat}
  : nat comm_semiring;

val comm_semiring_0_nat =
  {comm_semiring_comm_semiring_0 = comm_semiring_nat,
    semiring_0_comm_semiring_0 = semiring_0_nat}
  : nat comm_semiring_0;

val comm_semiring_0_cancel_nat =
  {comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_nat,
    semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_nat}
  : nat comm_semiring_0_cancel;

val monoid_mult_nat =
  {semigroup_mult_monoid_mult = semigroup_mult_nat,
    power_monoid_mult = power_nat}
  : nat monoid_mult;

val semiring_numeral_nat =
  {monoid_mult_semiring_numeral = monoid_mult_nat,
    numeral_semiring_numeral = numeral_nat,
    semiring_semiring_numeral = semiring_nat}
  : nat semiring_numeral;

val zero_neq_one_nat =
  {one_zero_neq_one = one_nat, zero_zero_neq_one = zero_nat} : nat zero_neq_one;

val semiring_1_nat =
  {semiring_numeral_semiring_1 = semiring_numeral_nat,
    semiring_0_semiring_1 = semiring_0_nat,
    zero_neq_one_semiring_1 = zero_neq_one_nat}
  : nat semiring_1;

val semiring_1_cancel_nat =
  {semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_nat,
    semiring_1_semiring_1_cancel = semiring_1_nat}
  : nat semiring_1_cancel;

val comm_monoid_mult_nat =
  {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_nat,
    monoid_mult_comm_monoid_mult = monoid_mult_nat,
    dvd_comm_monoid_mult = dvd_nat}
  : nat comm_monoid_mult;

val comm_semiring_1_nat =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_nat,
    comm_semiring_0_comm_semiring_1 = comm_semiring_0_nat,
    semiring_1_comm_semiring_1 = semiring_1_nat}
  : nat comm_semiring_1;

val comm_semiring_1_cancel_nat =
  {comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_nat,
    comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_nat,
    semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_nat}
  : nat comm_semiring_1_cancel;

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

val interval_nat =
  {linorder_interval = linorder_nat,
    comm_semiring_1_cancel_interval = comm_semiring_1_cancel_nat}
  : nat interval;

fun compare_nata x = comparator_of (equal_nat, linorder_nat) x;

val compare_nat = {compare = compare_nata} : nat compare;

val ceq_nata : (nat -> nat -> bool) option = SOME equal_nata;

val ceq_nat = {ceq = ceq_nata} : nat ceq;

fun def_hashmap_size_nat x = (fn _ => nat_of_integer (16 : Int.int)) x;

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun hashcode_nat n = uint32_of_int (int_of_nat n);

val hashable_nat =
  {hashcode = hashcode_nat, def_hashmap_size = def_hashmap_size_nat} :
  nat hashable;

val set_impl_nata : (nat, set_impla) phantom = Phantom Set_RBT;

val set_impl_nat = {set_impl = set_impl_nata} : nat set_impl;

val cEnum_nat :
  (nat list * (((nat -> bool) -> bool) * ((nat -> bool) -> bool))) option
  = NONE;

val cenum_nat = {cEnum = cEnum_nat} : nat cenum;

val finite_UNIV_nata : (nat, bool) phantom = Phantom false;

val finite_UNIV_nat = {finite_UNIV = finite_UNIV_nata} : nat finite_UNIV;

val ccompare_nata : (nat -> nat -> ordera) option = SOME compare_nata;

val ccompare_nat = {ccompare = ccompare_nata} : nat ccompare;

fun proper_interval_nat no NONE = true
  | proper_interval_nat NONE (SOME x) = less_nat zero_nata x
  | proper_interval_nat (SOME x) (SOME y) = less_nat one_nata (minus_nata y x);

fun cproper_interval_nata x = proper_interval_nat x;

val cproper_interval_nat =
  {ccompare_cproper_interval = ccompare_nat,
    cproper_interval = cproper_interval_nata}
  : nat cproper_interval;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

datatype rat = Frct of (inta * inta);

fun quotient_of (Frct x) = x;

fun equal_rata a b =
  equal_proda equal_int equal_int (quotient_of a) (quotient_of b);

val equal_rat = {equal = equal_rata} : rat equal;

fun less_eq_rat p q = let
                        val (a, c) = quotient_of p;
                        val (b, d) = quotient_of q;
                      in
                        less_eq_int (times_inta a d) (times_inta c b)
                      end;

fun less_rat p q = let
                     val (a, c) = quotient_of p;
                     val (b, d) = quotient_of q;
                   in
                     less_int (times_inta a d) (times_inta c b)
                   end;

val ord_rat = {less_eq = less_eq_rat, less = less_rat} : rat ord;

val preorder_rat = {ord_preorder = ord_rat} : rat preorder;

val order_rat = {preorder_order = preorder_rat} : rat order;

val linorder_rat = {order_linorder = order_rat} : rat linorder;

datatype 'a set_dlist = Abs_dlist of 'a list;

fun list_of_dlist A_ (Abs_dlist x) = x;

fun list_member equal [] y = false
  | list_member equal (x :: xs) y = equal x y orelse list_member equal xs y;

datatype color = R | B;

datatype ('a, 'b) rbt = Empty |
  Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt;

datatype ('b, 'a) mapping_rbt = Mapping_RBTa of ('b, 'a) rbt;

datatype 'a set = Collect_set of ('a -> bool) | DList_set of 'a set_dlist |
  RBT_set of ('a, unit) mapping_rbt | Set_Monad of 'a list |
  Complement of 'a set;

fun uminus_set (Complement b) = b
  | uminus_set (Collect_set p) = Collect_set (fn x => not (p x))
  | uminus_set a = Complement a;

fun balance (Branch (R, a, w, x, b)) s t (Branch (R, c, y, z, d)) =
  Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
  | balance (Branch (R, Branch (R, a, w, x, b), s, t, c)) y z Empty =
    Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance (Branch (R, Branch (R, a, w, x, b), s, t, c)) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, a, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance (Branch (R, Empty, w, x, Branch (R, b, s, t, c))) y z Empty =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance
    (Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c))) y z
    Empty =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Empty))
  | balance (Branch (R, Empty, w, x, Branch (R, b, s, t, c))) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, Empty, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance
    (Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c))) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance Empty w x (Branch (R, b, s, t, Branch (R, c, y, z, d))) =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, b, s, t, Branch (R, c, y, z, d))) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, d))
  | balance Empty w x (Branch (R, Branch (R, b, s, t, c), y, z, Empty)) =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance Empty w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))) =
    Branch
      (R, Branch (B, Empty, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Empty)) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Empty))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
  | balance Empty s t Empty = Branch (B, Empty, s, t, Empty)
  | balance Empty s t (Branch (B, va, vb, vc, vd)) =
    Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
  | balance Empty s t (Branch (v, Empty, vb, vc, Empty)) =
    Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
  | balance Empty s t (Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty)) =
    Branch
      (B, Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
  | balance Empty s t (Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi))) =
    Branch
      (B, Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
  | balance Empty s t
    (Branch (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
    = Branch
        (B, Empty, s, t,
          Branch
            (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
  | balance (Branch (B, va, vb, vc, vd)) s t Empty =
    Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
  | balance (Branch (B, va, vb, vc, vd)) s t (Branch (B, ve, vf, vg, vh)) =
    Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
  | balance (Branch (B, va, vb, vc, vd)) s t (Branch (v, Empty, vf, vg, Empty))
    = Branch
        (B, Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)) =
    Branch
      (B, Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))) =
    Branch
      (B, Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm)))
    = Branch
        (B, Branch (B, va, vb, vc, vd), s, t,
          Branch
            (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm)))
  | balance (Branch (v, Empty, vb, vc, Empty)) s t Empty =
    Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
  | balance (Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh))) s t Empty =
    Branch
      (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty)
  | balance (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty)) s t Empty =
    Branch
      (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty)
  | balance
    (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)))
    s t Empty =
    Branch
      (B, Branch
            (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty)
  | balance (Branch (v, Empty, vf, vg, Empty)) s t (Branch (B, va, vb, vc, vd))
    = Branch
        (B, Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd))
  | balance (Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl))) s t
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd))
  | balance (Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty)) s t
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd))
  | balance
    (Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)))
    s t (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch
            (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd));

fun rbt_comp_ins c f k v Empty = Branch (R, Empty, k, v, Empty)
  | rbt_comp_ins c f k v (Branch (B, l, x, y, r)) =
    (case c k x of Eq => Branch (B, l, x, f k y v, r)
      | Lta => balance (rbt_comp_ins c f k v l) x y r
      | Gt => balance l x y (rbt_comp_ins c f k v r))
  | rbt_comp_ins c f k v (Branch (R, l, x, y, r)) =
    (case c k x of Eq => Branch (R, l, x, f k y v, r)
      | Lta => Branch (R, rbt_comp_ins c f k v l, x, y, r)
      | Gt => Branch (R, l, x, y, rbt_comp_ins c f k v r));

fun paint c Empty = Empty
  | paint c (Branch (uu, l, k, v, r)) = Branch (c, l, k, v, r);

fun rbt_comp_insert_with_key c f k v t = paint B (rbt_comp_ins c f k v t);

fun rbt_comp_insert c =
  rbt_comp_insert_with_key c (fn _ => fn _ => fn nv => nv);

fun impl_ofa B_ (Mapping_RBTa x) = x;

fun the (SOME x2) = x2;

fun insertb A_ xc xd xe =
  Mapping_RBTa (rbt_comp_insert (the (ccompare A_)) xc xd (impl_ofa A_ xe));

fun rbt_baliR t1 ab bb (Branch (R, t2, aa, ba, Branch (R, t3, a, b, t4))) =
  Branch (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
  | rbt_baliR t1 ab bb (Branch (R, Branch (R, t2, aa, ba, t3), a, b, Empty)) =
    Branch (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, Empty))
  | rbt_baliR t1 ab bb
    (Branch (R, Branch (R, t2, aa, ba, t3), a, b, Branch (B, va, vb, vc, vd))) =
    Branch
      (R, Branch (B, t1, ab, bb, t2), aa, ba,
        Branch (B, t3, a, b, Branch (B, va, vb, vc, vd)))
  | rbt_baliR t1 a b Empty = Branch (B, t1, a, b, Empty)
  | rbt_baliR t1 a b (Branch (B, va, vb, vc, vd)) =
    Branch (B, t1, a, b, Branch (B, va, vb, vc, vd))
  | rbt_baliR t1 a b (Branch (v, Empty, vb, vc, Empty)) =
    Branch (B, t1, a, b, Branch (v, Empty, vb, vc, Empty))
  | rbt_baliR t1 a b (Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty)) =
    Branch (B, t1, a, b, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
  | rbt_baliR t1 a b (Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi))) =
    Branch (B, t1, a, b, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
  | rbt_baliR t1 a b
    (Branch (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
    = Branch
        (B, t1, a, b,
          Branch
            (v, Branch (B, ve, vj, vk, vl), vb, vc,
              Branch (B, vf, vg, vh, vi)));

fun equal_color R B = false
  | equal_color B R = false
  | equal_color B B = true
  | equal_color R R = true;

fun suc n = plus_nata n one_nata;

fun bheight Empty = zero_nata
  | bheight (Branch (c, lt, k, v, rt)) =
    (if equal_color c B then suc (bheight lt) else bheight lt);

fun rbt_joinR l a b r =
  (if less_eq_nat (bheight l) (bheight r) then Branch (R, l, a, b, r)
    else (case l
           of Branch (R, la, ab, ba, ra) =>
             Branch (R, la, ab, ba, rbt_joinR ra a b r)
           | Branch (B, la, ab, ba, ra) =>
             rbt_baliR la ab ba (rbt_joinR ra a b r)));

fun rbt_baliL (Branch (R, Branch (R, t1, ab, bb, t2), aa, ba, t3)) a b t4 =
  Branch (R, Branch (B, t1, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
  | rbt_baliL (Branch (R, Empty, ab, bb, Branch (R, t2, aa, ba, t3))) a b t4 =
    Branch (R, Branch (B, Empty, ab, bb, t2), aa, ba, Branch (B, t3, a, b, t4))
  | rbt_baliL
    (Branch (R, Branch (B, va, vb, vc, vd), ab, bb, Branch (R, t2, aa, ba, t3)))
    a b t4 =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), ab, bb, t2), aa, ba,
        Branch (B, t3, a, b, t4))
  | rbt_baliL Empty a b t2 = Branch (B, Empty, a, b, t2)
  | rbt_baliL (Branch (B, va, vb, vc, vd)) a b t2 =
    Branch (B, Branch (B, va, vb, vc, vd), a, b, t2)
  | rbt_baliL (Branch (v, Empty, vb, vc, Empty)) a b t2 =
    Branch (B, Branch (v, Empty, vb, vc, Empty), a, b, t2)
  | rbt_baliL (Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh))) a b t2 =
    Branch (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), a, b, t2)
  | rbt_baliL (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty)) a b t2 =
    Branch (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), a, b, t2)
  | rbt_baliL
    (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)))
    a b t2 =
    Branch
      (B, Branch
            (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        a, b, t2);

fun rbt_joinL l a b r =
  (if less_eq_nat (bheight r) (bheight l) then Branch (R, l, a, b, r)
    else (case r
           of Branch (R, la, ab, ba, ra) =>
             Branch (R, rbt_joinL l a b la, ab, ba, ra)
           | Branch (B, la, ab, ba, ra) =>
             rbt_baliL (rbt_joinL l a b la) ab ba ra));

fun rbt_join l a b r =
  let
    val bhl = bheight l;
    val bhr = bheight r;
  in
    (if less_nat bhr bhl then paint B (rbt_joinR l a b r)
      else (if less_nat bhl bhr then paint B (rbt_joinL l a b r)
             else Branch (B, l, a, b, r)))
  end;

fun rbt_split_comp c Empty k = (Empty, (NONE, Empty))
  | rbt_split_comp c (Branch (uu, l, a, b, r)) x =
    (case c x a of Eq => (l, (SOME b, r))
      | Lta => let
                 val (l1, (beta, l2)) = rbt_split_comp c l x;
               in
                 (l1, (beta, rbt_join l2 a b r))
               end
      | Gt => let
                val (r1, (beta, r2)) = rbt_split_comp c r x;
              in
                (rbt_join l a b r1, (beta, r2))
              end);

fun folda f Empty x = x
  | folda f (Branch (c, lt, k, v, rt)) x = folda f rt (f k v (folda f lt x));

fun rbt_comp_union_swap_rec c f gamma t1 t2 =
  let
    val bh1 = bheight t1;
    val bh2 = bheight t2;
    val (gammaa, (t2a, (bh2a, (t1a, _)))) =
      (if less_nat bh1 bh2 then (not gamma, (t1, (bh1, (t2, bh2))))
        else (gamma, (t2, (bh2, (t1, bh1)))));
    val fa = (if gammaa then (fn k => fn v => fn va => f k va v) else f);
  in
    (if less_nat bh2a (nat_of_integer (4 : Int.int))
      then folda (rbt_comp_insert_with_key c fa) t2a t1a
      else (case t1a of Empty => t2a
             | Branch (_, l1, a, b, r1) =>
               let
                 val (l2, (beta, r2)) = rbt_split_comp c t2a a;
               in
                 rbt_join (rbt_comp_union_swap_rec c f gammaa l1 l2) a
                   (case beta of NONE => b | SOME ca => fa a b ca)
                   (rbt_comp_union_swap_rec c f gammaa r1 r2)
               end))
  end;

fun rbt_comp_union_with_key c f t1 t2 =
  paint B (rbt_comp_union_swap_rec c f false t1 t2);

fun join A_ xc xd xe =
  Mapping_RBTa
    (rbt_comp_union_with_key (the (ccompare A_)) xc (impl_ofa A_ xd)
      (impl_ofa A_ xe));

fun list_insert equal x xs = (if list_member equal xs x then xs else x :: xs);

fun inserta A_ xb xc =
  Abs_dlist (list_insert (the (ceq A_)) xb (list_of_dlist A_ xc));

fun fold f [] s = s
  | fold f (x :: xs) s = fold f xs (f x s);

fun foldc A_ x xc = fold x (list_of_dlist A_ xc);

fun union A_ = foldc A_ (inserta A_);

fun memberc A_ xa = list_member (the (ceq A_)) (list_of_dlist A_ xa);

fun equal_option A_ NONE (SOME x2) = false
  | equal_option A_ (SOME x2) NONE = false
  | equal_option A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_option A_ NONE NONE = true;

fun rbt_comp_lookup c Empty k = NONE
  | rbt_comp_lookup c (Branch (uu, l, x, y, r)) k =
    (case c k x of Eq => SOME y | Lta => rbt_comp_lookup c l k
      | Gt => rbt_comp_lookup c r k);

fun lookupb A_ xa = rbt_comp_lookup (the (ccompare A_)) (impl_ofa A_ xa);

fun equal_unita u v = true;

val equal_unit = {equal = equal_unita} : unit equal;

fun memberb A_ t x = equal_option equal_unit (lookupb A_ t x) (SOME ());

fun member (A1_, A2_) x (Set_Monad xs) =
  (case ceq A1_
    of NONE =>
      (raise Fail "member Set_Monad: ceq = None")
        (fn _ => member (A1_, A2_) x (Set_Monad xs))
    | SOME eq => list_member eq xs x)
  | member (A1_, A2_) xa (Complement x) = not (member (A1_, A2_) xa x)
  | member (A1_, A2_) x (RBT_set rbt) = memberb A2_ rbt x
  | member (A1_, A2_) x (DList_set dxs) = memberc A1_ dxs x
  | member (A1_, A2_) x (Collect_set a) = a x;

fun id x = (fn xa => xa) x;

fun is_none NONE = true
  | is_none (SOME x) = false;

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun inter_list A_ xb xc =
  Mapping_RBTa
    (fold (fn k => rbt_comp_insert (the (ccompare A_)) k ())
      (filter
        (fn x =>
          not (is_none
                (rbt_comp_lookup (the (ccompare A_)) (impl_ofa A_ xb) x)))
        xc)
      Empty);

fun length_tailrec [] n = n
  | length_tailrec (x :: xs) n = length_tailrec xs (suc n);

fun size_list xs = length_tailrec xs zero_nata;

fun map_prod f g (a, b) = (f a, g b);

fun divmod_nat m n =
  let
    val k = integer_of_nat m;
    val l = integer_of_nat n;
  in
    map_prod nat_of_integer nat_of_integer
      (if k = (0 : Int.int) then ((0 : Int.int), (0 : Int.int))
        else (if l = (0 : Int.int) then ((0 : Int.int), k)
               else Integer.div_mod (abs k) (abs l)))
  end;

fun apfst f (x, y) = (f x, y);

fun rbtreeify_g n kvs =
  (if equal_nata n zero_nata orelse equal_nata n one_nata then (Empty, kvs)
    else let
           val (na, r) = divmod_nat n (nat_of_integer (2 : Int.int));
         in
           (if equal_nata r zero_nata
             then let
                    val (t1, (k, v) :: kvsa) = rbtreeify_g na kvs;
                  in
                    apfst (fn a => Branch (B, t1, k, v, a))
                      (rbtreeify_g na kvsa)
                  end
             else let
                    val (t1, (k, v) :: kvsa) = rbtreeify_f na kvs;
                  in
                    apfst (fn a => Branch (B, t1, k, v, a))
                      (rbtreeify_g na kvsa)
                  end)
         end)
and rbtreeify_f n kvs =
  (if equal_nata n zero_nata then (Empty, kvs)
    else (if equal_nata n one_nata then let
  val (k, v) :: kvsa = kvs;
in
  (Branch (R, Empty, k, v, Empty), kvsa)
end
           else let
                  val (na, r) = divmod_nat n (nat_of_integer (2 : Int.int));
                in
                  (if equal_nata r zero_nata
                    then let
                           val (t1, (k, v) :: kvsa) = rbtreeify_f na kvs;
                         in
                           apfst (fn a => Branch (B, t1, k, v, a))
                             (rbtreeify_g na kvsa)
                         end
                    else let
                           val (t1, (k, v) :: kvsa) = rbtreeify_f na kvs;
                         in
                           apfst (fn a => Branch (B, t1, k, v, a))
                             (rbtreeify_f na kvsa)
                         end)
                end));

fun rbtreeify kvs = fst (rbtreeify_g (suc (size_list kvs)) kvs);

fun gen_entries [] Empty = []
  | gen_entries ((kv, t) :: kvts) Empty = kv :: gen_entries kvts t
  | gen_entries kvts (Branch (c, l, k, v, r)) =
    gen_entries (((k, v), r) :: kvts) l;

fun entries x = gen_entries [] x;

fun filterb A_ xb xc =
  Mapping_RBTa (rbtreeify (filter xb (entries (impl_ofa A_ xc))));

fun map_filter f [] = []
  | map_filter f (x :: xs) =
    (case f x of NONE => map_filter f xs | SOME y => y :: map_filter f xs);

fun map_filter_comp_inter c f t1 t2 =
  map_filter
    (fn (k, v) =>
      (case rbt_comp_lookup c t1 k of NONE => NONE
        | SOME va => SOME (k, f k va v)))
    (entries t2);

fun is_rbt_empty t =
  (case t of Empty => true | Branch (_, _, _, _, _) => false);

fun rbt_split_min Empty = (raise Fail "undefined")
  | rbt_split_min (Branch (uu, l, a, b, r)) =
    (if is_rbt_empty l then (a, (b, r))
      else let
             val (aa, (ba, la)) = rbt_split_min l;
           in
             (aa, (ba, rbt_join la a b r))
           end);

fun rbt_join2 l r =
  (if is_rbt_empty r then l else let
                                   val (a, (b, c)) = rbt_split_min r;
                                 in
                                   rbt_join l a b c
                                 end);

fun rbt_comp_inter_swap_rec c f gamma t1 t2 =
  let
    val bh1 = bheight t1;
    val bh2 = bheight t2;
    val (gammaa, (t2a, (bh2a, (t1a, _)))) =
      (if less_nat bh1 bh2 then (not gamma, (t1, (bh1, (t2, bh2))))
        else (gamma, (t2, (bh2, (t1, bh1)))));
    val fa = (if gammaa then (fn k => fn v => fn va => f k va v) else f);
  in
    (if less_nat bh2a (nat_of_integer (4 : Int.int))
      then rbtreeify (map_filter_comp_inter c fa t1a t2a)
      else (case t1a of Empty => Empty
             | Branch (_, l1, a, b, r1) =>
               let
                 val (l2, (beta, r2)) = rbt_split_comp c t2a a;
                 val l = rbt_comp_inter_swap_rec c f gammaa l1 l2;
                 val r = rbt_comp_inter_swap_rec c f gammaa r1 r2;
               in
                 (case beta of NONE => rbt_join2 l r
                   | SOME ba => rbt_join l a (fa a b ba) r)
               end))
  end;

fun rbt_comp_inter_with_key c f t1 t2 =
  paint B (rbt_comp_inter_swap_rec c f false t1 t2);

fun meet A_ xc xd xe =
  Mapping_RBTa
    (rbt_comp_inter_with_key (the (ccompare A_)) xc (impl_ofa A_ xd)
      (impl_ofa A_ xe));

fun filtera A_ xb xc = Abs_dlist (filter xb (list_of_dlist A_ xc));

fun inf_seta (A1_, A2_) (RBT_set rbt1) (Set_Monad xs) =
  (case ccompare A2_
    of NONE =>
      (raise Fail "inter RBT_set Set_Monad: ccompare = None")
        (fn _ => inf_seta (A1_, A2_) (RBT_set rbt1) (Set_Monad xs))
    | SOME _ => RBT_set (inter_list A2_ rbt1 xs))
  | inf_seta (A1_, A2_) (Set_Monad xs) (RBT_set rbt1) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "inter Set_Monad RBT_set: ccompare = None")
          (fn _ => inf_seta (A1_, A2_) (RBT_set rbt1) (Set_Monad xs))
      | SOME _ => RBT_set (inter_list A2_ rbt1 xs))
  | inf_seta (A1_, A2_) (Set_Monad xs) (DList_set dxs2) =
    (case ceq A1_
      of NONE =>
        (raise Fail "inter Set_Monad DList_set: ceq = None")
          (fn _ => inf_seta (A1_, A2_) (Set_Monad xs) (DList_set dxs2))
      | SOME eq => DList_set (filtera A1_ (list_member eq xs) dxs2))
  | inf_seta (A1_, A2_) (Set_Monad xs1) (Set_Monad xs2) =
    (case ceq A1_
      of NONE =>
        (raise Fail "inter Set_Monad Set_Monad: ceq = None")
          (fn _ => inf_seta (A1_, A2_) (Set_Monad xs1) (Set_Monad xs2))
      | SOME eq => Set_Monad (filter (list_member eq xs2) xs1))
  | inf_seta (A1_, A2_) (RBT_set rbt) (DList_set dxs) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "inter RBT_set DList_set: ccompare = None")
          (fn _ => inf_seta (A1_, A2_) (RBT_set rbt) (DList_set dxs))
      | SOME _ =>
        (case ceq A1_
          of NONE =>
            (raise Fail "inter RBT_set DList_set: ceq = None")
              (fn _ => inf_seta (A1_, A2_) (RBT_set rbt) (DList_set dxs))
          | SOME _ => RBT_set (inter_list A2_ rbt (list_of_dlist A1_ dxs))))
  | inf_seta (A1_, A2_) (RBT_set rbt1) (RBT_set rbt2) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "inter RBT_set RBT_set: ccompare = None")
          (fn _ => inf_seta (A1_, A2_) (RBT_set rbt1) (RBT_set rbt2))
      | SOME _ => RBT_set (meet A2_ (fn _ => fn _ => id) rbt1 rbt2))
  | inf_seta (A1_, A2_) (DList_set dxs1) (Set_Monad xs) =
    (case ceq A1_
      of NONE =>
        (raise Fail "inter DList_set Set_Monad: ceq = None")
          (fn _ => inf_seta (A1_, A2_) (DList_set dxs1) (Set_Monad xs))
      | SOME eq => DList_set (filtera A1_ (list_member eq xs) dxs1))
  | inf_seta (A1_, A2_) (DList_set dxs1) (DList_set dxs2) =
    (case ceq A1_
      of NONE =>
        (raise Fail "inter DList_set DList_set: ceq = None")
          (fn _ => inf_seta (A1_, A2_) (DList_set dxs1) (DList_set dxs2))
      | SOME _ => DList_set (filtera A1_ (memberc A1_ dxs2) dxs1))
  | inf_seta (A1_, A2_) (DList_set dxs) (RBT_set rbt) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "inter DList_set RBT_set: ccompare = None")
          (fn _ => inf_seta (A1_, A2_) (DList_set dxs) (RBT_set rbt))
      | SOME _ =>
        (case ceq A1_
          of NONE =>
            (raise Fail "inter DList_set RBT_set: ceq = None")
              (fn _ => inf_seta (A1_, A2_) (DList_set dxs) (RBT_set rbt))
          | SOME _ => RBT_set (inter_list A2_ rbt (list_of_dlist A1_ dxs))))
  | inf_seta (A1_, A2_) (Complement ba) (Complement b) =
    Complement (sup_seta (A1_, A2_) ba b)
  | inf_seta (A1_, A2_) g (RBT_set rbt2) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "inter RBT_set2: ccompare = None")
          (fn _ => inf_seta (A1_, A2_) g (RBT_set rbt2))
      | SOME _ =>
        RBT_set (filterb A2_ ((fn x => member (A1_, A2_) x g) o fst) rbt2))
  | inf_seta (A1_, A2_) (RBT_set rbt1) g =
    (case ccompare A2_
      of NONE =>
        (raise Fail "inter RBT_set1: ccompare = None")
          (fn _ => inf_seta (A1_, A2_) (RBT_set rbt1) g)
      | SOME _ =>
        RBT_set (filterb A2_ ((fn x => member (A1_, A2_) x g) o fst) rbt1))
  | inf_seta (A1_, A2_) h (DList_set dxs2) =
    (case ceq A1_
      of NONE =>
        (raise Fail "inter DList_set2: ceq = None")
          (fn _ => inf_seta (A1_, A2_) h (DList_set dxs2))
      | SOME _ => DList_set (filtera A1_ (fn x => member (A1_, A2_) x h) dxs2))
  | inf_seta (A1_, A2_) (DList_set dxs1) h =
    (case ceq A1_
      of NONE =>
        (raise Fail "inter DList_set1: ceq = None")
          (fn _ => inf_seta (A1_, A2_) (DList_set dxs1) h)
      | SOME _ => DList_set (filtera A1_ (fn x => member (A1_, A2_) x h) dxs1))
  | inf_seta (A1_, A2_) i (Set_Monad xs) =
    Set_Monad (filter (fn x => member (A1_, A2_) x i) xs)
  | inf_seta (A1_, A2_) (Set_Monad xs) i =
    Set_Monad (filter (fn x => member (A1_, A2_) x i) xs)
  | inf_seta (A1_, A2_) j (Collect_set a) =
    Collect_set (fn x => a x andalso member (A1_, A2_) x j)
  | inf_seta (A1_, A2_) (Collect_set a) j =
    Collect_set (fn x => a x andalso member (A1_, A2_) x j)
and sup_seta (A1_, A2_) ba (Complement b) =
  Complement (inf_seta (A1_, A2_) (uminus_set ba) b)
  | sup_seta (A1_, A2_) (Complement ba) b =
    Complement (inf_seta (A1_, A2_) ba (uminus_set b))
  | sup_seta (A1_, A2_) (RBT_set rbt1) (RBT_set rbt2) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "union RBT_set RBT_set: ccompare = None")
          (fn _ => sup_seta (A1_, A2_) (RBT_set rbt1) (RBT_set rbt2))
      | SOME _ => RBT_set (join A2_ (fn _ => fn _ => id) rbt1 rbt2))
  | sup_seta (A1_, A2_) (RBT_set rbt) (DList_set dxs) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "union RBT_set DList_set: ccompare = None")
          (fn _ => sup_seta (A1_, A2_) (RBT_set rbt) (DList_set dxs))
      | SOME _ =>
        (case ceq A1_
          of NONE =>
            (raise Fail "union RBT_set DList_set: ceq = None")
              (fn _ => sup_seta (A1_, A2_) (RBT_set rbt) (DList_set dxs))
          | SOME _ => RBT_set (foldc A1_ (fn k => insertb A2_ k ()) dxs rbt)))
  | sup_seta (A1_, A2_) (DList_set dxs) (RBT_set rbt) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "union DList_set RBT_set: ccompare = None")
          (fn _ => sup_seta (A1_, A2_) (RBT_set rbt) (DList_set dxs))
      | SOME _ =>
        (case ceq A1_
          of NONE =>
            (raise Fail "union DList_set RBT_set: ceq = None")
              (fn _ => sup_seta (A1_, A2_) (RBT_set rbt) (DList_set dxs))
          | SOME _ => RBT_set (foldc A1_ (fn k => insertb A2_ k ()) dxs rbt)))
  | sup_seta (A1_, A2_) (DList_set dxs1) (DList_set dxs2) =
    (case ceq A1_
      of NONE =>
        (raise Fail "union DList_set DList_set: ceq = None")
          (fn _ => sup_seta (A1_, A2_) (DList_set dxs1) (DList_set dxs2))
      | SOME _ => DList_set (union A1_ dxs1 dxs2))
  | sup_seta (A1_, A2_) (Set_Monad zs) (RBT_set rbt2) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "union Set_Monad RBT_set: ccompare = None")
          (fn _ => sup_seta (A1_, A2_) (Set_Monad zs) (RBT_set rbt2))
      | SOME _ => RBT_set (fold (fn k => insertb A2_ k ()) zs rbt2))
  | sup_seta (A1_, A2_) (RBT_set rbt1) (Set_Monad zs) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "union RBT_set Set_Monad: ccompare = None")
          (fn _ => sup_seta (A1_, A2_) (RBT_set rbt1) (Set_Monad zs))
      | SOME _ => RBT_set (fold (fn k => insertb A2_ k ()) zs rbt1))
  | sup_seta (A1_, A2_) (Set_Monad ws) (DList_set dxs2) =
    (case ceq A1_
      of NONE =>
        (raise Fail "union Set_Monad DList_set: ceq = None")
          (fn _ => sup_seta (A1_, A2_) (Set_Monad ws) (DList_set dxs2))
      | SOME _ => DList_set (fold (inserta A1_) ws dxs2))
  | sup_seta (A1_, A2_) (DList_set dxs1) (Set_Monad ws) =
    (case ceq A1_
      of NONE =>
        (raise Fail "union DList_set Set_Monad: ceq = None")
          (fn _ => sup_seta (A1_, A2_) (DList_set dxs1) (Set_Monad ws))
      | SOME _ => DList_set (fold (inserta A1_) ws dxs1))
  | sup_seta (A1_, A2_) (Set_Monad xs) (Set_Monad ys) = Set_Monad (xs @ ys)
  | sup_seta (A1_, A2_) b (Collect_set a) =
    Collect_set (fn x => a x orelse member (A1_, A2_) x b)
  | sup_seta (A1_, A2_) (Collect_set a) b =
    Collect_set (fn x => a x orelse member (A1_, A2_) x b);

fun inf_set (A1_, A2_) = {inf = inf_seta (A1_, A2_)} : 'a set inf;

fun sup_set (A1_, A2_) = {sup = sup_seta (A1_, A2_)} : 'a set sup;

fun equal_order Lta Gt = false
  | equal_order Gt Lta = false
  | equal_order Eq Gt = false
  | equal_order Gt Eq = false
  | equal_order Eq Lta = false
  | equal_order Lta Eq = false
  | equal_order Gt Gt = true
  | equal_order Lta Lta = true
  | equal_order Eq Eq = true;

datatype ('a, 'b) generator = Generator of (('b -> bool) * ('b -> 'a * 'b));

fun generator (Generator x) = x;

fun has_next g = fst (generator g);

fun next g = snd (generator g);

fun sorted_list_subset_fusion less eq g1 g2 s1 s2 =
  (if has_next g1 s1
    then let
           val (x, s1a) = next g1 s1;
         in
           has_next g2 s2 andalso
             let
               val (y, s2a) = next g2 s2;
             in
               (if eq x y then sorted_list_subset_fusion less eq g1 g2 s1a s2a
                 else less y x andalso
                        sorted_list_subset_fusion less eq g1 g2 s1 s2a)
             end
         end
    else true);

fun list_all_fusion g p s =
  (if has_next g s then let
                          val (x, sa) = next g s;
                        in
                          p x andalso list_all_fusion g p sa
                        end
    else true);

fun rbt_keys_next ((k, t) :: kts, Empty) = (k, (kts, t))
  | rbt_keys_next (kts, Branch (c, l, k, v, r)) =
    rbt_keys_next ((k, r) :: kts, l);

fun rbt_has_next ([], Empty) = false
  | rbt_has_next (vb :: vc, va) = true
  | rbt_has_next (v, Branch (vb, vc, vd, ve, vf)) = true;

val rbt_keys_generator :
  ('a, (('a * ('a, 'b) rbt) list * ('a, 'b) rbt)) generator
  = Generator (rbt_has_next, rbt_keys_next);

fun lt_of_comp acomp x y =
  (case acomp x y of Eq => false | Lta => true | Gt => false);

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun dlist_all A_ x xc = list_all x (list_of_dlist A_ xc);

fun rbt_init x = ([], x);

fun init A_ xa = rbt_init (impl_ofa A_ xa);

fun collect A_ p =
  (case cEnum A_ of NONE => Collect_set p
    | SOME (enum, _) => Set_Monad (filter p enum));

fun less_eq_set (A1_, A2_, A3_) (RBT_set rbt1) (RBT_set rbt2) =
  (case ccompare A3_
    of NONE =>
      (raise Fail "subset RBT_set RBT_set: ccompare = None")
        (fn _ => less_eq_set (A1_, A2_, A3_) (RBT_set rbt1) (RBT_set rbt2))
    | SOME c =>
      (case ceq A2_
        of NONE =>
          sorted_list_subset_fusion (lt_of_comp c)
            (fn x => fn y => equal_order (c x y) Eq) rbt_keys_generator
            rbt_keys_generator (init A3_ rbt1) (init A3_ rbt2)
        | SOME eq =>
          sorted_list_subset_fusion (lt_of_comp c) eq rbt_keys_generator
            rbt_keys_generator (init A3_ rbt1) (init A3_ rbt2)))
  | less_eq_set (A1_, A2_, A3_) (Complement a1) (Complement a2) =
    less_eq_set (A1_, A2_, A3_) a2 a1
  | less_eq_set (A1_, A2_, A3_) (Collect_set p) (Complement a) =
    less_eq_set (A1_, A2_, A3_) a (collect A1_ (fn x => not (p x)))
  | less_eq_set (A1_, A2_, A3_) (RBT_set rbt) b =
    (case ccompare A3_
      of NONE =>
        (raise Fail "subset RBT_set1: ccompare = None")
          (fn _ => less_eq_set (A1_, A2_, A3_) (RBT_set rbt) b)
      | SOME _ =>
        list_all_fusion rbt_keys_generator (fn x => member (A2_, A3_) x b)
          (init A3_ rbt))
  | less_eq_set (A1_, A2_, A3_) (DList_set dxs) c =
    (case ceq A2_
      of NONE =>
        (raise Fail "subset DList_set1: ceq = None")
          (fn _ => less_eq_set (A1_, A2_, A3_) (DList_set dxs) c)
      | SOME _ => dlist_all A2_ (fn x => member (A2_, A3_) x c) dxs)
  | less_eq_set (A1_, A2_, A3_) (Set_Monad xs) c =
    list_all (fn x => member (A2_, A3_) x c) xs;

fun less_set (A1_, A2_, A3_) a b =
  less_eq_set (A1_, A2_, A3_) a b andalso not (less_eq_set (A1_, A2_, A3_) b a);

fun ord_set (A1_, A2_, A3_) =
  {less_eq = less_eq_set (A1_, A2_, A3_), less = less_set (A1_, A2_, A3_)} :
  'a set ord;

fun preorder_set (A1_, A2_, A3_) = {ord_preorder = ord_set (A1_, A2_, A3_)} :
  'a set preorder;

fun order_set (A1_, A2_, A3_) = {preorder_order = preorder_set (A1_, A2_, A3_)}
  : 'a set order;

fun semilattice_sup_set (A1_, A2_, A3_) =
  {sup_semilattice_sup = sup_set (A2_, A3_),
    order_semilattice_sup = order_set (A1_, A2_, A3_)}
  : 'a set semilattice_sup;

fun semilattice_inf_set (A1_, A2_, A3_) =
  {inf_semilattice_inf = inf_set (A2_, A3_),
    order_semilattice_inf = order_set (A1_, A2_, A3_)}
  : 'a set semilattice_inf;

fun lattice_set (A1_, A2_, A3_) =
  {semilattice_inf_lattice = semilattice_inf_set (A1_, A2_, A3_),
    semilattice_sup_lattice = semilattice_sup_set (A1_, A2_, A3_)}
  : 'a set lattice;

fun list_all2_fusion p g1 g2 s1 s2 =
  (if has_next g1 s1
    then has_next g2 s2 andalso let
                                  val (x, s1a) = next g1 s1;
                                  val (y, s2a) = next g2 s2;
                                in
                                  p x y andalso list_all2_fusion p g1 g2 s1a s2a
                                end
    else not (has_next g2 s2));

fun set_eq (A1_, A2_, A3_) (RBT_set rbt1) (RBT_set rbt2) =
  (case ccompare A3_
    of NONE =>
      (raise Fail "set_eq RBT_set RBT_set: ccompare = None")
        (fn _ => set_eq (A1_, A2_, A3_) (RBT_set rbt1) (RBT_set rbt2))
    | SOME c =>
      (case ceq A2_
        of NONE =>
          list_all2_fusion (fn x => fn y => equal_order (c x y) Eq)
            rbt_keys_generator rbt_keys_generator (init A3_ rbt1)
            (init A3_ rbt2)
        | SOME eq =>
          list_all2_fusion eq rbt_keys_generator rbt_keys_generator
            (init A3_ rbt1) (init A3_ rbt2)))
  | set_eq (A1_, A2_, A3_) (Complement a) (Complement b) =
    set_eq (A1_, A2_, A3_) a b
  | set_eq (A1_, A2_, A3_) a b =
    less_eq_set (A1_, A2_, A3_) a b andalso less_eq_set (A1_, A2_, A3_) b a;

fun ceq_seta (A1_, A2_, A3_) =
  (case ceq A2_ of NONE => NONE | SOME _ => SOME (set_eq (A1_, A2_, A3_)));

fun ceq_set (A1_, A2_, A3_) = {ceq = ceq_seta (A1_, A2_, A3_)} : 'a set ceq;

val set_impl_seta : ('a set, set_impla) phantom = Phantom Set_Choose;

val set_impl_set = {set_impl = set_impl_seta} : 'a set set_impl;

fun of_phantom (Phantom x) = x;

fun finite_UNIV_seta A_ = Phantom (of_phantom (finite_UNIV A_));

fun finite_UNIV_set A_ = {finite_UNIV = finite_UNIV_seta A_} :
  'a set finite_UNIV;

fun set_less_eq_aux_Compl_fusion less proper_interval g1 g2 ao s1 s2 =
  (if has_next g1 s1
    then (if has_next g2 s2
           then let
                  val (x, s1a) = next g1 s1;
                  val (y, s2a) = next g2 s2;
                in
                  (if less x y
                    then proper_interval ao (SOME x) orelse
                           set_less_eq_aux_Compl_fusion less proper_interval g1
                             g2 (SOME x) s1a s2
                    else (if less y x
                           then proper_interval ao (SOME y) orelse
                                  set_less_eq_aux_Compl_fusion less
                                    proper_interval g1 g2 (SOME y) s1 s2a
                           else proper_interval ao (SOME y)))
                end
           else true)
    else true);

fun compl_set_less_eq_aux_fusion less proper_interval g1 g2 ao s1 s2 =
  (if has_next g1 s1
    then let
           val (x, s1a) = next g1 s1;
         in
           (if has_next g2 s2
             then let
                    val (y, s2a) = next g2 s2;
                  in
                    (if less x y
                      then not (proper_interval ao (SOME x)) andalso
                             compl_set_less_eq_aux_fusion less proper_interval
                               g1 g2 (SOME x) s1a s2
                      else (if less y x
                             then not (proper_interval ao (SOME y)) andalso
                                    compl_set_less_eq_aux_fusion less
                                      proper_interval g1 g2 (SOME y) s1 s2a
                             else not (proper_interval ao (SOME y))))
                  end
             else not (proper_interval ao (SOME x)) andalso
                    compl_set_less_eq_aux_fusion less proper_interval g1 g2
                      (SOME x) s1a s2)
         end
    else (if has_next g2 s2
           then let
                  val (y, s2a) = next g2 s2;
                in
                  not (proper_interval ao (SOME y)) andalso
                    compl_set_less_eq_aux_fusion less proper_interval g1 g2
                      (SOME y) s1 s2a
                end
           else not (proper_interval ao NONE)));

fun set_less_eq_aux_Compl less proper_interval ao [] ys = true
  | set_less_eq_aux_Compl less proper_interval ao xs [] = true
  | set_less_eq_aux_Compl less proper_interval ao (x :: xs) (y :: ys) =
    (if less x y
      then proper_interval ao (SOME x) orelse
             set_less_eq_aux_Compl less proper_interval (SOME x) xs (y :: ys)
      else (if less y x
             then proper_interval ao (SOME y) orelse
                    set_less_eq_aux_Compl less proper_interval (SOME y)
                      (x :: xs) ys
             else proper_interval ao (SOME y)));

fun compl_set_less_eq_aux less proper_interval ao [] [] =
  not (proper_interval ao NONE)
  | compl_set_less_eq_aux less proper_interval ao [] (y :: ys) =
    not (proper_interval ao (SOME y)) andalso
      compl_set_less_eq_aux less proper_interval (SOME y) [] ys
  | compl_set_less_eq_aux less proper_interval ao (x :: xs) [] =
    not (proper_interval ao (SOME x)) andalso
      compl_set_less_eq_aux less proper_interval (SOME x) xs []
  | compl_set_less_eq_aux less proper_interval ao (x :: xs) (y :: ys) =
    (if less x y
      then not (proper_interval ao (SOME x)) andalso
             compl_set_less_eq_aux less proper_interval (SOME x) xs (y :: ys)
      else (if less y x
             then not (proper_interval ao (SOME y)) andalso
                    compl_set_less_eq_aux less proper_interval (SOME y)
                      (x :: xs) ys
             else not (proper_interval ao (SOME y))));

fun lexord_eq_fusion less g1 g2 s1 s2 =
  (if has_next g1 s1
    then has_next g2 s2 andalso
           let
             val (x, s1a) = next g1 s1;
             val (y, s2a) = next g2 s2;
           in
             less x y orelse
               not (less y x) andalso lexord_eq_fusion less g1 g2 s1a s2a
           end
    else true);

fun remdups_sorted less [] = []
  | remdups_sorted less [x] = [x]
  | remdups_sorted less (x :: y :: xs) =
    (if less x y then x :: remdups_sorted less (y :: xs)
      else remdups_sorted less (y :: xs));

fun quicksort_acc less ac [] = ac
  | quicksort_acc less ac [x] = x :: ac
  | quicksort_acc less ac (x :: v :: va) =
    quicksort_part less ac x [] [] [] (v :: va)
and quicksort_part less ac x lts eqs gts [] =
  quicksort_acc less (eqs @ x :: quicksort_acc less ac gts) lts
  | quicksort_part less ac x lts eqs gts (z :: zs) =
    (if less x z then quicksort_part less ac x lts eqs (z :: gts) zs
      else (if less z x then quicksort_part less ac x (z :: lts) eqs gts zs
             else quicksort_part less ac x lts (z :: eqs) gts zs));

fun quicksort less = quicksort_acc less [];

fun gen_keys [] Empty = []
  | gen_keys ((k, t) :: kts) Empty = k :: gen_keys kts t
  | gen_keys kts (Branch (c, l, k, v, r)) = gen_keys ((k, r) :: kts) l;

fun keys x = gen_keys [] x;

fun keysa A_ xa = keys (impl_ofa A_ xa);

fun csorted_list_of_set (A1_, A2_) (Set_Monad xs) =
  (case ccompare A2_
    of NONE =>
      (raise Fail "csorted_list_of_set Set_Monad: ccompare = None")
        (fn _ => csorted_list_of_set (A1_, A2_) (Set_Monad xs))
    | SOME c => remdups_sorted (lt_of_comp c) (quicksort (lt_of_comp c) xs))
  | csorted_list_of_set (A1_, A2_) (DList_set dxs) =
    (case ceq A1_
      of NONE =>
        (raise Fail "csorted_list_of_set DList_set: ceq = None")
          (fn _ => csorted_list_of_set (A1_, A2_) (DList_set dxs))
      | SOME _ =>
        (case ccompare A2_
          of NONE =>
            (raise Fail "csorted_list_of_set DList_set: ccompare = None")
              (fn _ => csorted_list_of_set (A1_, A2_) (DList_set dxs))
          | SOME c => quicksort (lt_of_comp c) (list_of_dlist A1_ dxs)))
  | csorted_list_of_set (A1_, A2_) (RBT_set rbt) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "csorted_list_of_set RBT_set: ccompare = None")
          (fn _ => csorted_list_of_set (A1_, A2_) (RBT_set rbt))
      | SOME _ => keysa A2_ rbt);

fun emptyc A_ = Mapping_RBTa Empty;

fun emptyb A_ = Abs_dlist [];

fun set_empty_choose (A1_, A2_) =
  (case ccompare A2_
    of NONE =>
      (case ceq A1_ of NONE => Set_Monad [] | SOME _ => DList_set (emptyb A1_))
    | SOME _ => RBT_set (emptyc A2_));

fun set_empty (A1_, A2_) Set_Collect = Collect_set (fn _ => false)
  | set_empty (A1_, A2_) Set_DList = DList_set (emptyb A1_)
  | set_empty (A1_, A2_) Set_RBT = RBT_set (emptyc A2_)
  | set_empty (A1_, A2_) Set_Monada = Set_Monad []
  | set_empty (A1_, A2_) Set_Choose = set_empty_choose (A1_, A2_);

fun bot_set (A1_, A2_, A3_) = set_empty (A1_, A2_) (of_phantom (set_impl A3_));

fun top_set (A1_, A2_, A3_) = uminus_set (bot_set (A1_, A2_, A3_));

fun le_of_comp acomp x y =
  (case acomp x y of Eq => true | Lta => true | Gt => false);

fun lexordp_eq less [] ys = true
  | lexordp_eq less xs [] = null xs
  | lexordp_eq less (x :: xs) (y :: ys) =
    less x y orelse not (less y x) andalso lexordp_eq less xs ys;

fun finite (A1_, A2_, A3_) (Collect_set p) =
  of_phantom (finite_UNIV A1_) orelse
    (raise Fail "finite Collect_set")
      (fn _ => finite (A1_, A2_, A3_) (Collect_set p))
  | finite (A1_, A2_, A3_) (Set_Monad xs) = true
  | finite (A1_, A2_, A3_) (Complement a) =
    (if of_phantom (finite_UNIV A1_) then true
      else (if finite (A1_, A2_, A3_) a then false
             else (raise Fail "finite Complement: infinite set")
                    (fn _ => finite (A1_, A2_, A3_) (Complement a))))
  | finite (A1_, A2_, A3_) (RBT_set rbt) =
    (case ccompare A3_
      of NONE =>
        (raise Fail "finite RBT_set: ccompare = None")
          (fn _ => finite (A1_, A2_, A3_) (RBT_set rbt))
      | SOME _ => true)
  | finite (A1_, A2_, A3_) (DList_set dxs) =
    (case ceq A2_
      of NONE =>
        (raise Fail "finite DList_set: ceq = None")
          (fn _ => finite (A1_, A2_, A3_) (DList_set dxs))
      | SOME _ => true);

fun set_less_aux_Compl_fusion less proper_interval g1 g2 ao s1 s2 =
  (if has_next g1 s1
    then let
           val (x, s1a) = next g1 s1;
         in
           (if has_next g2 s2
             then let
                    val (y, s2a) = next g2 s2;
                  in
                    (if less x y
                      then proper_interval ao (SOME x) orelse
                             set_less_aux_Compl_fusion less proper_interval g1
                               g2 (SOME x) s1a s2
                      else (if less y x
                             then proper_interval ao (SOME y) orelse
                                    set_less_aux_Compl_fusion less
                                      proper_interval g1 g2 (SOME y) s1 s2a
                             else proper_interval ao (SOME y)))
                  end
             else proper_interval ao (SOME x) orelse
                    set_less_aux_Compl_fusion less proper_interval g1 g2
                      (SOME x) s1a s2)
         end
    else (if has_next g2 s2
           then let
                  val (y, s2a) = next g2 s2;
                in
                  proper_interval ao (SOME y) orelse
                    set_less_aux_Compl_fusion less proper_interval g1 g2
                      (SOME y) s1 s2a
                end
           else proper_interval ao NONE));

fun compl_set_less_aux_fusion less proper_interval g1 g2 ao s1 s2 =
  has_next g1 s1 andalso
    (has_next g2 s2 andalso
      let
        val (x, s1a) = next g1 s1;
        val (y, s2a) = next g2 s2;
      in
        (if less x y
          then not (proper_interval ao (SOME x)) andalso
                 compl_set_less_aux_fusion less proper_interval g1 g2 (SOME x)
                   s1a s2
          else (if less y x
                 then not (proper_interval ao (SOME y)) andalso
                        compl_set_less_aux_fusion less proper_interval g1 g2
                          (SOME y) s1 s2a
                 else not (proper_interval ao (SOME y))))
      end);

fun set_less_aux_Compl less proper_interval ao [] [] = proper_interval ao NONE
  | set_less_aux_Compl less proper_interval ao [] (y :: ys) =
    proper_interval ao (SOME y) orelse
      set_less_aux_Compl less proper_interval (SOME y) [] ys
  | set_less_aux_Compl less proper_interval ao (x :: xs) [] =
    proper_interval ao (SOME x) orelse
      set_less_aux_Compl less proper_interval (SOME x) xs []
  | set_less_aux_Compl less proper_interval ao (x :: xs) (y :: ys) =
    (if less x y
      then proper_interval ao (SOME x) orelse
             set_less_aux_Compl less proper_interval (SOME x) xs (y :: ys)
      else (if less y x
             then proper_interval ao (SOME y) orelse
                    set_less_aux_Compl less proper_interval (SOME y) (x :: xs)
                      ys
             else proper_interval ao (SOME y)));

fun compl_set_less_aux less proper_interval ao [] ys = false
  | compl_set_less_aux less proper_interval ao xs [] = false
  | compl_set_less_aux less proper_interval ao (x :: xs) (y :: ys) =
    (if less x y
      then not (proper_interval ao (SOME x)) andalso
             compl_set_less_aux less proper_interval (SOME x) xs (y :: ys)
      else (if less y x
             then not (proper_interval ao (SOME y)) andalso
                    compl_set_less_aux less proper_interval (SOME y) (x :: xs)
                      ys
             else not (proper_interval ao (SOME y))));

fun lexord_fusion less g1 g2 s1 s2 =
  (if has_next g1 s1
    then (if has_next g2 s2
           then let
                  val (x, s1a) = next g1 s1;
                  val (y, s2a) = next g2 s2;
                in
                  less x y orelse
                    not (less y x) andalso lexord_fusion less g1 g2 s1a s2a
                end
           else false)
    else has_next g2 s2);

fun lexordp less [] ys = not (null ys)
  | lexordp less xs [] = false
  | lexordp less (x :: xs) (y :: ys) =
    less x y orelse not (less y x) andalso lexordp less xs ys;

fun comp_of_ords le lt x y =
  (if lt x y then Lta else (if le x y then Eq else Gt));

fun ccompare_seta (A1_, A2_, A3_, A4_) =
  (case ccompare (ccompare_cproper_interval A3_) of NONE => NONE
    | SOME _ =>
      SOME (comp_of_ords (cless_eq_set (A1_, A2_, A3_, A4_))
             (cless_set (A1_, A2_, A3_, A4_))))
and cless_set (A1_, A2_, A3_, A4_) (Complement (RBT_set rbt1)) (RBT_set rbt2) =
  (case ccompare (ccompare_cproper_interval A3_)
    of NONE =>
      (raise Fail "cless_set (Complement RBT_set) RBT_set: ccompare = None")
        (fn _ =>
          cless_set (A1_, A2_, A3_, A4_) (Complement (RBT_set rbt1))
            (RBT_set rbt2))
    | SOME c =>
      finite (A1_, A2_, ccompare_cproper_interval A3_)
        (top_set (A2_, ccompare_cproper_interval A3_, A4_)) andalso
        compl_set_less_aux_fusion (lt_of_comp c) (cproper_interval A3_)
          rbt_keys_generator rbt_keys_generator NONE
          (init (ccompare_cproper_interval A3_) rbt1)
          (init (ccompare_cproper_interval A3_) rbt2))
  | cless_set (A1_, A2_, A3_, A4_) (RBT_set rbt1) (Complement (RBT_set rbt2)) =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_set RBT_set (Complement RBT_set): ccompare = None")
          (fn _ =>
            cless_set (A1_, A2_, A3_, A4_) (RBT_set rbt1)
              (Complement (RBT_set rbt2)))
      | SOME c =>
        (if finite (A1_, A2_, ccompare_cproper_interval A3_)
              (top_set (A2_, ccompare_cproper_interval A3_, A4_))
          then set_less_aux_Compl_fusion (lt_of_comp c) (cproper_interval A3_)
                 rbt_keys_generator rbt_keys_generator NONE
                 (init (ccompare_cproper_interval A3_) rbt1)
                 (init (ccompare_cproper_interval A3_) rbt2)
          else true))
  | cless_set (A1_, A2_, A3_, A4_) (RBT_set rbta) (RBT_set rbt) =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_set RBT_set RBT_set: ccompare = None")
          (fn _ => cless_set (A1_, A2_, A3_, A4_) (RBT_set rbta) (RBT_set rbt))
      | SOME c =>
        lexord_fusion (fn x => fn y => lt_of_comp c y x) rbt_keys_generator
          rbt_keys_generator (init (ccompare_cproper_interval A3_) rbta)
          (init (ccompare_cproper_interval A3_) rbt))
  | cless_set (A1_, A2_, A3_, A4_) (Complement a) (Complement b) =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_set Complement Complement: ccompare = None")
          (fn _ => cless_set (A1_, A2_, A3_, A4_) (Complement a) (Complement b))
      | SOME _ => lt_of_comp (the (ccompare_seta (A1_, A2_, A3_, A4_))) b a)
  | cless_set (A1_, A2_, A3_, A4_) (Complement a) b =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_set Complement1: ccompare = None")
          (fn _ => cless_set (A1_, A2_, A3_, A4_) (Complement a) b)
      | SOME c =>
        (if finite (A1_, A2_, ccompare_cproper_interval A3_) a andalso
              finite (A1_, A2_, ccompare_cproper_interval A3_) b
          then finite (A1_, A2_, ccompare_cproper_interval A3_)
                 (top_set (A2_, ccompare_cproper_interval A3_, A4_)) andalso
                 compl_set_less_aux (lt_of_comp c) (cproper_interval A3_) NONE
                   (csorted_list_of_set (A2_, ccompare_cproper_interval A3_) a)
                   (csorted_list_of_set (A2_, ccompare_cproper_interval A3_) b)
          else (raise Fail "cless_set Complement1: infinite set")
                 (fn _ => cless_set (A1_, A2_, A3_, A4_) (Complement a) b)))
  | cless_set (A1_, A2_, A3_, A4_) a (Complement b) =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_set Complement2: ccompare = None")
          (fn _ => cless_set (A1_, A2_, A3_, A4_) a (Complement b))
      | SOME c =>
        (if finite (A1_, A2_, ccompare_cproper_interval A3_) a andalso
              finite (A1_, A2_, ccompare_cproper_interval A3_) b
          then (if finite (A1_, A2_, ccompare_cproper_interval A3_)
                     (top_set (A2_, ccompare_cproper_interval A3_, A4_))
                 then set_less_aux_Compl (lt_of_comp c) (cproper_interval A3_)
                        NONE
                        (csorted_list_of_set
                          (A2_, ccompare_cproper_interval A3_) a)
                        (csorted_list_of_set
                          (A2_, ccompare_cproper_interval A3_) b)
                 else true)
          else (raise Fail "cless_set Complement2: infinite set")
                 (fn _ => cless_set (A1_, A2_, A3_, A4_) a (Complement b))))
  | cless_set (A1_, A2_, A3_, A4_) a b =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_set: ccompare = None")
          (fn _ => cless_set (A1_, A2_, A3_, A4_) a b)
      | SOME c =>
        (if finite (A1_, A2_, ccompare_cproper_interval A3_) a andalso
              finite (A1_, A2_, ccompare_cproper_interval A3_) b
          then lexordp (fn x => fn y => lt_of_comp c y x)
                 (csorted_list_of_set (A2_, ccompare_cproper_interval A3_) a)
                 (csorted_list_of_set (A2_, ccompare_cproper_interval A3_) b)
          else (raise Fail "cless_set: infinite set")
                 (fn _ => cless_set (A1_, A2_, A3_, A4_) a b)))
and cless_eq_set (A1_, A2_, A3_, A4_) (Complement (RBT_set rbt1)) (RBT_set rbt2)
  = (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail
          "cless_eq_set (Complement RBT_set) RBT_set: ccompare = None")
          (fn _ =>
            cless_eq_set (A1_, A2_, A3_, A4_) (Complement (RBT_set rbt1))
              (RBT_set rbt2))
      | SOME c =>
        finite (A1_, A2_, ccompare_cproper_interval A3_)
          (top_set (A2_, ccompare_cproper_interval A3_, A4_)) andalso
          compl_set_less_eq_aux_fusion (lt_of_comp c) (cproper_interval A3_)
            rbt_keys_generator rbt_keys_generator NONE
            (init (ccompare_cproper_interval A3_) rbt1)
            (init (ccompare_cproper_interval A3_) rbt2))
  | cless_eq_set (A1_, A2_, A3_, A4_) (RBT_set rbt1) (Complement (RBT_set rbt2))
    = (case ccompare (ccompare_cproper_interval A3_)
        of NONE =>
          (raise Fail
            "cless_eq_set RBT_set (Complement RBT_set): ccompare = None")
            (fn _ =>
              cless_eq_set (A1_, A2_, A3_, A4_) (RBT_set rbt1)
                (Complement (RBT_set rbt2)))
        | SOME c =>
          (if finite (A1_, A2_, ccompare_cproper_interval A3_)
                (top_set (A2_, ccompare_cproper_interval A3_, A4_))
            then set_less_eq_aux_Compl_fusion (lt_of_comp c)
                   (cproper_interval A3_) rbt_keys_generator rbt_keys_generator
                   NONE (init (ccompare_cproper_interval A3_) rbt1)
                   (init (ccompare_cproper_interval A3_) rbt2)
            else true))
  | cless_eq_set (A1_, A2_, A3_, A4_) (RBT_set rbta) (RBT_set rbt) =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_eq_set RBT_set RBT_set: ccompare = None")
          (fn _ =>
            cless_eq_set (A1_, A2_, A3_, A4_) (RBT_set rbta) (RBT_set rbt))
      | SOME c =>
        lexord_eq_fusion (fn x => fn y => lt_of_comp c y x) rbt_keys_generator
          rbt_keys_generator (init (ccompare_cproper_interval A3_) rbta)
          (init (ccompare_cproper_interval A3_) rbt))
  | cless_eq_set (A1_, A2_, A3_, A4_) (Complement a) (Complement b) =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_eq_set Complement Complement: ccompare = None")
          (fn _ =>
            le_of_comp (the (ccompare_seta (A1_, A2_, A3_, A4_))) (Complement a)
              (Complement b))
      | SOME _ => cless_eq_set (A1_, A2_, A3_, A4_) b a)
  | cless_eq_set (A1_, A2_, A3_, A4_) (Complement a) b =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_eq_set Complement1: ccompare = None")
          (fn _ => cless_eq_set (A1_, A2_, A3_, A4_) (Complement a) b)
      | SOME c =>
        (if finite (A1_, A2_, ccompare_cproper_interval A3_) a andalso
              finite (A1_, A2_, ccompare_cproper_interval A3_) b
          then finite (A1_, A2_, ccompare_cproper_interval A3_)
                 (top_set (A2_, ccompare_cproper_interval A3_, A4_)) andalso
                 compl_set_less_eq_aux (lt_of_comp c) (cproper_interval A3_)
                   NONE
                   (csorted_list_of_set (A2_, ccompare_cproper_interval A3_) a)
                   (csorted_list_of_set (A2_, ccompare_cproper_interval A3_) b)
          else (raise Fail "cless_eq_set Complement1: infinite set")
                 (fn _ => cless_eq_set (A1_, A2_, A3_, A4_) (Complement a) b)))
  | cless_eq_set (A1_, A2_, A3_, A4_) a (Complement b) =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_eq_set Complement2: ccompare = None")
          (fn _ => cless_eq_set (A1_, A2_, A3_, A4_) a (Complement b))
      | SOME c =>
        (if finite (A1_, A2_, ccompare_cproper_interval A3_) a andalso
              finite (A1_, A2_, ccompare_cproper_interval A3_) b
          then (if finite (A1_, A2_, ccompare_cproper_interval A3_)
                     (top_set (A2_, ccompare_cproper_interval A3_, A4_))
                 then set_less_eq_aux_Compl (lt_of_comp c)
                        (cproper_interval A3_) NONE
                        (csorted_list_of_set
                          (A2_, ccompare_cproper_interval A3_) a)
                        (csorted_list_of_set
                          (A2_, ccompare_cproper_interval A3_) b)
                 else true)
          else (raise Fail "cless_eq_set Complement2: infinite set")
                 (fn _ => cless_eq_set (A1_, A2_, A3_, A4_) a (Complement b))))
  | cless_eq_set (A1_, A2_, A3_, A4_) a b =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "cless_eq_set: ccompare = None")
          (fn _ => cless_eq_set (A1_, A2_, A3_, A4_) a b)
      | SOME c =>
        (if finite (A1_, A2_, ccompare_cproper_interval A3_) a andalso
              finite (A1_, A2_, ccompare_cproper_interval A3_) b
          then lexordp_eq (fn x => fn y => lt_of_comp c y x)
                 (csorted_list_of_set (A2_, ccompare_cproper_interval A3_) a)
                 (csorted_list_of_set (A2_, ccompare_cproper_interval A3_) b)
          else (raise Fail "cless_eq_set: infinite set")
                 (fn _ => cless_eq_set (A1_, A2_, A3_, A4_) a b)));

fun ccompare_set (A1_, A2_, A3_, A4_) =
  {ccompare = ccompare_seta (A1_, A2_, A3_, A4_)} : 'a set ccompare;

fun less_eq_bool false b = true
  | less_eq_bool true b = b;

fun less_bool false b = b
  | less_bool true b = false;

val ord_bool = {less_eq = less_eq_bool, less = less_bool} : bool ord;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

fun typerep_lista A_ t = Typerep ("List.list", [typerep A_ Type]);

fun countable_list A_ = {} : ('a list) countable;

fun typerep_list A_ = {typerep = typerep_lista A_} : ('a list) typerep;

fun heap_list A_ =
  {countable_heap = countable_list (countable_heap A_),
    typerep_heap = typerep_list (typerep_heap A_)}
  : ('a list) heap;

fun shows_prec_list A_ p xs = shows_list A_ xs;

fun shows_list_list A_ xss = showsp_list (shows_prec_list A_) zero_nata xss;

fun show_list A_ =
  {shows_prec = shows_prec_list A_, shows_list = shows_list_list A_} :
  ('a list) show;

fun equality_list eq_a [] [] = true
  | equality_list eq_a [] (y :: ya) = false
  | equality_list eq_a (x :: xa) [] = false
  | equality_list eq_a (x :: xa) (y :: ya) =
    eq_a x y andalso equality_list eq_a xa ya;

fun ceq_lista A_ =
  (case ceq A_ of NONE => NONE | SOME eq_a => SOME (equality_list eq_a));

fun ceq_list A_ = {ceq = ceq_lista A_} : ('a list) ceq;

fun def_hashmap_size_list A_ =
  (fn _ =>
    times_nata (nat_of_integer (2 : Int.int)) (def_hashmap_size A_ Type));

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun hashcode_list A_ =
  foldl (fn h => fn x =>
          Word32.+ (Word32.* (h, Word32.fromLargeInt (Int.toLarge (33 : Int.int))), hashcode
            A_ x))
    (Word32.fromLargeInt (Int.toLarge (5381 : Int.int)));

fun hashable_list A_ =
  {hashcode = hashcode_list A_, def_hashmap_size = def_hashmap_size_list A_} :
  ('a list) hashable;

val set_impl_lista : (('a list), set_impla) phantom = Phantom Set_Choose;

val set_impl_list = {set_impl = set_impl_lista} : ('a list) set_impl;

fun comparator_list comp_a [] [] = Eq
  | comparator_list comp_a [] (y :: ya) = Lta
  | comparator_list comp_a (x :: xa) [] = Gt
  | comparator_list comp_a (x :: xa) (y :: ya) =
    (case comp_a x y of Eq => comparator_list comp_a xa ya | Lta => Lta
      | Gt => Gt);

fun ccompare_lista A_ =
  (case ccompare A_ of NONE => NONE
    | SOME comp_a => SOME (comparator_list comp_a));

fun ccompare_list A_ = {ccompare = ccompare_lista A_} : ('a list) ccompare;

fun typerep_arraya A_ t = Typerep ("Heap.array", [typerep A_ Type]);

val countable_array = {} : ('a array) countable;

fun typerep_array A_ = {typerep = typerep_arraya A_} : ('a array) typerep;

fun heap_array A_ =
  {countable_heap = countable_array, typerep_heap = typerep_array A_} :
  ('a array) heap;

fun equal_bool false p = not p
  | equal_bool true p = p
  | equal_bool p false = not p
  | equal_bool p true = p;

fun equal_chara (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
  (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
  equal_bool x1 y1 andalso
    (equal_bool x2 y2 andalso
      (equal_bool x3 y3 andalso
        (equal_bool x4 y4 andalso
          (equal_bool x5 y5 andalso
            (equal_bool x6 y6 andalso
              (equal_bool x7 y7 andalso equal_bool x8 y8))))));

val equal_char = {equal = equal_chara} : char equal;

fun shows_prec_char p c = (fn a => c :: a);

fun shows_list_char cs = shows_string cs;

val show_char = {shows_prec = shows_prec_char, shows_list = shows_list_char} :
  char show;

fun lexordp_eqa A_ [] ys = true
  | lexordp_eqa A_ xs [] = null xs
  | lexordp_eqa A_ (x :: xs) (y :: ys) =
    less A_ x y orelse not (less A_ y x) andalso lexordp_eqa A_ xs ys;

fun less_eq_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7))
  (Chara (c0, c1, c2, c3, c4, c5, c6, c7)) =
  lexordp_eqa ord_bool [b7, b6, b5, b4, b3, b2, b1, b0]
    [c7, c6, c5, c4, c3, c2, c1, c0];

fun lexordpa A_ [] ys = not (null ys)
  | lexordpa A_ xs [] = false
  | lexordpa A_ (x :: xs) (y :: ys) =
    less A_ x y orelse not (less A_ y x) andalso lexordpa A_ xs ys;

fun less_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7))
  (Chara (c0, c1, c2, c3, c4, c5, c6, c7)) =
  lexordpa ord_bool [b7, b6, b5, b4, b3, b2, b1, b0]
    [c7, c6, c5, c4, c3, c2, c1, c0];

val ord_char = {less_eq = less_eq_char, less = less_char} : char ord;

val preorder_char = {ord_preorder = ord_char} : char preorder;

val order_char = {preorder_order = preorder_char} : char order;

val linorder_char = {order_linorder = order_char} : char linorder;

datatype 'a dBMEntry = Le of 'a | Lt of 'a | INF;

fun typerep_DBMEntrya A_ t = Typerep ("DBM.DBMEntry", [typerep A_ Type]);

fun countable_DBMEntry A_ = {} : 'a dBMEntry countable;

fun typerep_DBMEntry A_ = {typerep = typerep_DBMEntrya A_} :
  'a dBMEntry typerep;

fun heap_DBMEntry A_ =
  {countable_heap = countable_DBMEntry (countable_heap A_),
    typerep_heap = typerep_DBMEntry (typerep_heap A_)}
  : 'a dBMEntry heap;

fun dbm_add A_ INF uu = INF
  | dbm_add A_ (Le v) INF = INF
  | dbm_add A_ (Lt v) INF = INF
  | dbm_add A_ (Le a) (Le b) =
    Le (plus ((plus_semigroup_add o semigroup_add_ab_semigroup_add o
                ab_semigroup_add_cancel_ab_semigroup_add o
                cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add o
                ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le o
                ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add)
               A_)
         a b)
  | dbm_add A_ (Le a) (Lt b) =
    Lt (plus ((plus_semigroup_add o semigroup_add_ab_semigroup_add o
                ab_semigroup_add_cancel_ab_semigroup_add o
                cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add o
                ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le o
                ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add)
               A_)
         a b)
  | dbm_add A_ (Lt a) (Le b) =
    Lt (plus ((plus_semigroup_add o semigroup_add_ab_semigroup_add o
                ab_semigroup_add_cancel_ab_semigroup_add o
                cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add o
                ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le o
                ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add)
               A_)
         a b)
  | dbm_add A_ (Lt a) (Lt b) =
    Lt (plus ((plus_semigroup_add o semigroup_add_ab_semigroup_add o
                ab_semigroup_add_cancel_ab_semigroup_add o
                cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add o
                ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le o
                ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add)
               A_)
         a b);

fun plus_DBMEntrya A_ =
  dbm_add
    (linordered_cancel_ab_semigroup_add_linordered_cancel_ab_monoid_add A_);

fun plus_DBMEntry A_ = {plus = plus_DBMEntrya A_} : 'a dBMEntry plus;

fun zero_DBMEntrya A_ = Le (zero A_);

fun zero_DBMEntry A_ = {zero = zero_DBMEntrya A_} : 'a dBMEntry zero;

fun equal_DBMEntry A_ (Lt x2) INF = false
  | equal_DBMEntry A_ INF (Lt x2) = false
  | equal_DBMEntry A_ (Le x1) INF = false
  | equal_DBMEntry A_ INF (Le x1) = false
  | equal_DBMEntry A_ (Le x1) (Lt x2) = false
  | equal_DBMEntry A_ (Lt x2) (Le x1) = false
  | equal_DBMEntry A_ (Lt x2) (Lt y2) = eq A_ x2 y2
  | equal_DBMEntry A_ (Le x1) (Le y1) = eq A_ x1 y1
  | equal_DBMEntry A_ INF INF = true;

fun dbm_lt A_ (Lt a) INF = true
  | dbm_lt A_ (Le a) INF = true
  | dbm_lt A_ (Le a) (Le b) =
    less ((ord_preorder o preorder_order o order_linorder) A_) a b
  | dbm_lt A_ (Le a) (Lt b) =
    less ((ord_preorder o preorder_order o order_linorder) A_) a b
  | dbm_lt A_ (Lt a) (Le b) =
    less_eq ((ord_preorder o preorder_order o order_linorder) A_) a b
  | dbm_lt A_ (Lt a) (Lt b) =
    less ((ord_preorder o preorder_order o order_linorder) A_) a b
  | dbm_lt A_ INF x = false;

fun dbm_le (A1_, A2_) a b = equal_DBMEntry A1_ a b orelse dbm_lt A2_ a b;

fun less_eq_DBMEntry (A1_, A2_) = dbm_le (A1_, A2_);

fun less_DBMEntry A_ = dbm_lt A_;

fun ord_DBMEntry (A1_, A2_) =
  {less_eq = less_eq_DBMEntry (A1_, A2_), less = less_DBMEntry A2_} :
  'a dBMEntry ord;

fun preorder_DBMEntry (A1_, A2_) = {ord_preorder = ord_DBMEntry (A1_, A2_)} :
  'a dBMEntry preorder;

fun order_DBMEntry (A1_, A2_) = {preorder_order = preorder_DBMEntry (A1_, A2_)}
  : 'a dBMEntry order;

fun semigroup_add_DBMEntry A_ = {plus_semigroup_add = plus_DBMEntry A_} :
  'a dBMEntry semigroup_add;

fun monoid_add_DBMEntry A_ =
  {semigroup_add_monoid_add = semigroup_add_DBMEntry A_,
    zero_monoid_add =
      zero_DBMEntry
        ((zero_monoid_add o monoid_add_comm_monoid_add o
           comm_monoid_add_ordered_comm_monoid_add o
           ordered_comm_monoid_add_linordered_ab_monoid_add o
           linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
          A_)}
  : 'a dBMEntry monoid_add;

fun linorder_DBMEntry (A1_, A2_) = {order_linorder = order_DBMEntry (A1_, A2_)}
  : 'a dBMEntry linorder;

fun ab_semigroup_add_DBMEntry A_ =
  {semigroup_add_ab_semigroup_add = semigroup_add_DBMEntry A_} :
  'a dBMEntry ab_semigroup_add;

fun comm_monoid_add_DBMEntry A_ =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_DBMEntry A_,
    monoid_add_comm_monoid_add = monoid_add_DBMEntry A_}
  : 'a dBMEntry comm_monoid_add;

fun ordered_ab_semigroup_add_DBMEntry (A1_, A2_) =
  {ab_semigroup_add_ordered_ab_semigroup_add = ab_semigroup_add_DBMEntry A1_,
    order_ordered_ab_semigroup_add =
      order_DBMEntry
        (A2_, (linorder_linordered_ab_semigroup_add o
                linordered_ab_semigroup_add_linordered_ab_monoid_add o
                linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
                A1_)}
  : 'a dBMEntry ordered_ab_semigroup_add;

fun ordered_comm_monoid_add_DBMEntry (A1_, A2_) =
  {comm_monoid_add_ordered_comm_monoid_add = comm_monoid_add_DBMEntry A1_,
    ordered_ab_semigroup_add_ordered_comm_monoid_add =
      ordered_ab_semigroup_add_DBMEntry (A1_, A2_)}
  : 'a dBMEntry ordered_comm_monoid_add;

fun linordered_ab_semigroup_add_DBMEntry (A1_, A2_) =
  {ordered_ab_semigroup_add_linordered_ab_semigroup_add =
     ordered_ab_semigroup_add_DBMEntry (A1_, A2_),
    linorder_linordered_ab_semigroup_add =
      linorder_DBMEntry
        (A2_, (linorder_linordered_ab_semigroup_add o
                linordered_ab_semigroup_add_linordered_ab_monoid_add o
                linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
                A1_)}
  : 'a dBMEntry linordered_ab_semigroup_add;

fun linordered_ab_monoid_add_DBMEntry (A1_, A2_) =
  {linordered_ab_semigroup_add_linordered_ab_monoid_add =
     linordered_ab_semigroup_add_DBMEntry (A1_, A2_),
    ordered_comm_monoid_add_linordered_ab_monoid_add =
      ordered_comm_monoid_add_DBMEntry (A1_, A2_)}
  : 'a dBMEntry linordered_ab_monoid_add;

fun shows_space x =
  shows_prec_char zero_nata
    (Chara (false, false, false, false, false, true, false, false)) x;

datatype 'a act = In of 'a | Out of 'a | Sil of 'a;

fun shows_pr p =
  (if less_nat zero_nata p
    then shows_prec_char zero_nata
           (Chara (true, false, false, true, false, true, false, false))
    else id);

fun shows_pl p =
  (if less_nat zero_nata p
    then shows_prec_char zero_nata
           (Chara (false, false, false, true, false, true, false, false))
    else id);

fun showsp_act show_a p (In x) =
  shows_pl p o
    shows_string
      [Chara (true, false, false, true, false, false, true, false),
        Chara (false, true, true, true, false, true, true, false)] o
    shows_space o
    show_a one_nata x o
    shows_pr p
  | showsp_act show_a p (Out x) =
    shows_pl p o
      shows_string
        [Chara (true, true, true, true, false, false, true, false),
          Chara (true, false, true, false, true, true, true, false),
          Chara (false, false, true, false, true, true, true, false)] o
      shows_space o
      show_a one_nata x o
      shows_pr p
  | showsp_act show_a p (Sil x) =
    shows_pl p o
      shows_string
        [Chara (true, true, false, false, true, false, true, false),
          Chara (true, false, false, true, false, true, true, false),
          Chara (false, false, true, true, false, true, true, false)] o
      shows_space o
      show_a one_nata x o
      shows_pr p;

fun shows_prec_act A_ = showsp_act (shows_prec A_);

fun shows_list_act A_ = showsp_list (shows_prec_act A_) zero_nata;

fun show_act A_ =
  {shows_prec = shows_prec_act A_, shows_list = shows_list_act A_} :
  'a act show;

val equal_literal = {equal = (fn a => fn b => ((a : string) = b))} :
  string equal;

fun bit_cut_integer k =
  (if k = (0 : Int.int) then ((0 : Int.int), false)
    else let
           val (r, s) = Integer.div_mod (abs k) (abs (2 : Int.int));
         in
           ((if (0 : Int.int) < k then r else ~ r - s), s = (1 : Int.int))
         end);

fun char_of_integer k = let
                          val (q0, b0) = bit_cut_integer k;
                          val (q1, b1) = bit_cut_integer q0;
                          val (q2, b2) = bit_cut_integer q1;
                          val (q3, b3) = bit_cut_integer q2;
                          val (q4, b4) = bit_cut_integer q3;
                          val (q5, b5) = bit_cut_integer q4;
                          val (q6, b6) = bit_cut_integer q5;
                          val (_, a) = bit_cut_integer q6;
                        in
                          Chara (b0, b1, b2, b3, b4, b5, b6, a)
                        end;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun explode s = map char_of_integer (Str_Literal.asciis_of_literal s);

fun shows_prec_literal p s = shows_string (explode s);

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun shows_list_literal x = foldr (fn s => shows_string (explode s)) x;

val show_literal =
  {shows_prec = shows_prec_literal, shows_list = shows_list_literal} :
  string show;

val ord_literal =
  {less_eq = (fn a => fn b => a <= b), less = (fn a => fn b => a < b)} :
  string ord;

val preorder_literal = {ord_preorder = ord_literal} : string preorder;

val order_literal = {preorder_order = preorder_literal} : string order;

val linorder_literal = {order_linorder = order_literal} : string linorder;

fun compare_literala x = comparator_of (equal_literal, linorder_literal) x;

val compare_literal = {compare = compare_literala} : string compare;

val ceq_literala : (string -> string -> bool) option =
  SOME (fn a => fn b => ((a : string) = b));

val ceq_literal = {ceq = ceq_literala} : string ceq;

val set_impl_literala : (string, set_impla) phantom = Phantom Set_RBT;

val set_impl_literal = {set_impl = set_impl_literala} : string set_impl;

val countable_literal = {} : string countable;

val cEnum_literal :
  (string list *
    (((string -> bool) -> bool) * ((string -> bool) -> bool))) option
  = NONE;

val cenum_literal = {cEnum = cEnum_literal} : string cenum;

val finite_UNIV_literala : (string, bool) phantom = Phantom false;

val finite_UNIV_literal = {finite_UNIV = finite_UNIV_literala} :
  string finite_UNIV;

val ccompare_literala : (string -> string -> ordera) option =
  SOME compare_literala;

val ccompare_literal = {ccompare = ccompare_literala} : string ccompare;

datatype mapping_impla = Mapping_Choose | Mapping_Assoc_List | Mapping_RBT |
  Mapping_Mapping;

val mapping_impl_literala : (string, mapping_impla) phantom =
  Phantom Mapping_RBT;

type 'a mapping_impl = {mapping_impl : ('a, mapping_impla) phantom};
val mapping_impl = #mapping_impl :
  'a mapping_impl -> ('a, mapping_impla) phantom;

val mapping_impl_literal = {mapping_impl = mapping_impl_literala} :
  string mapping_impl;

fun cproper_interval_literala xso yso = (raise Fail "undefined");

val cproper_interval_literal =
  {ccompare_cproper_interval = ccompare_literal,
    cproper_interval = cproper_interval_literala}
  : string cproper_interval;

datatype 'a formula = Atom of 'a | Bot | Not of 'a formula |
  And of 'a formula * 'a formula | Or of 'a formula * 'a formula |
  Imp of 'a formula * 'a formula;

fun equal_formulaa A_ (Or (x51, x52)) (Imp (x61, x62)) = false
  | equal_formulaa A_ (Imp (x61, x62)) (Or (x51, x52)) = false
  | equal_formulaa A_ (And (x41, x42)) (Imp (x61, x62)) = false
  | equal_formulaa A_ (Imp (x61, x62)) (And (x41, x42)) = false
  | equal_formulaa A_ (And (x41, x42)) (Or (x51, x52)) = false
  | equal_formulaa A_ (Or (x51, x52)) (And (x41, x42)) = false
  | equal_formulaa A_ (Not x3) (Imp (x61, x62)) = false
  | equal_formulaa A_ (Imp (x61, x62)) (Not x3) = false
  | equal_formulaa A_ (Not x3) (Or (x51, x52)) = false
  | equal_formulaa A_ (Or (x51, x52)) (Not x3) = false
  | equal_formulaa A_ (Not x3) (And (x41, x42)) = false
  | equal_formulaa A_ (And (x41, x42)) (Not x3) = false
  | equal_formulaa A_ Bot (Imp (x61, x62)) = false
  | equal_formulaa A_ (Imp (x61, x62)) Bot = false
  | equal_formulaa A_ Bot (Or (x51, x52)) = false
  | equal_formulaa A_ (Or (x51, x52)) Bot = false
  | equal_formulaa A_ Bot (And (x41, x42)) = false
  | equal_formulaa A_ (And (x41, x42)) Bot = false
  | equal_formulaa A_ Bot (Not x3) = false
  | equal_formulaa A_ (Not x3) Bot = false
  | equal_formulaa A_ (Atom x1) (Imp (x61, x62)) = false
  | equal_formulaa A_ (Imp (x61, x62)) (Atom x1) = false
  | equal_formulaa A_ (Atom x1) (Or (x51, x52)) = false
  | equal_formulaa A_ (Or (x51, x52)) (Atom x1) = false
  | equal_formulaa A_ (Atom x1) (And (x41, x42)) = false
  | equal_formulaa A_ (And (x41, x42)) (Atom x1) = false
  | equal_formulaa A_ (Atom x1) (Not x3) = false
  | equal_formulaa A_ (Not x3) (Atom x1) = false
  | equal_formulaa A_ (Atom x1) Bot = false
  | equal_formulaa A_ Bot (Atom x1) = false
  | equal_formulaa A_ (Imp (x61, x62)) (Imp (y61, y62)) =
    equal_formulaa A_ x61 y61 andalso equal_formulaa A_ x62 y62
  | equal_formulaa A_ (Or (x51, x52)) (Or (y51, y52)) =
    equal_formulaa A_ x51 y51 andalso equal_formulaa A_ x52 y52
  | equal_formulaa A_ (And (x41, x42)) (And (y41, y42)) =
    equal_formulaa A_ x41 y41 andalso equal_formulaa A_ x42 y42
  | equal_formulaa A_ (Not x3) (Not y3) = equal_formulaa A_ x3 y3
  | equal_formulaa A_ (Atom x1) (Atom y1) = eq A_ x1 y1
  | equal_formulaa A_ Bot Bot = true;

fun equal_formula A_ = {equal = equal_formulaa A_} : 'a formula equal;

fun comparator_formula comp_a (Atom x) (Atom y) = comp_a x y
  | comparator_formula comp_a (Atom x) Bot = Lta
  | comparator_formula comp_a (Atom x) (Not ya) = Lta
  | comparator_formula comp_a (Atom x) (And (yb, yc)) = Lta
  | comparator_formula comp_a (Atom x) (Or (yd, ye)) = Lta
  | comparator_formula comp_a (Atom x) (Imp (yf, yg)) = Lta
  | comparator_formula comp_a Bot (Atom y) = Gt
  | comparator_formula comp_a Bot Bot = Eq
  | comparator_formula comp_a Bot (Not ya) = Lta
  | comparator_formula comp_a Bot (And (yb, yc)) = Lta
  | comparator_formula comp_a Bot (Or (yd, ye)) = Lta
  | comparator_formula comp_a Bot (Imp (yf, yg)) = Lta
  | comparator_formula comp_a (Not x) (Atom y) = Gt
  | comparator_formula comp_a (Not x) Bot = Gt
  | comparator_formula comp_a (Not x) (Not ya) = comparator_formula comp_a x ya
  | comparator_formula comp_a (Not x) (And (yb, yc)) = Lta
  | comparator_formula comp_a (Not x) (Or (yd, ye)) = Lta
  | comparator_formula comp_a (Not x) (Imp (yf, yg)) = Lta
  | comparator_formula comp_a (And (x, xa)) (Atom y) = Gt
  | comparator_formula comp_a (And (x, xa)) Bot = Gt
  | comparator_formula comp_a (And (x, xa)) (Not ya) = Gt
  | comparator_formula comp_a (And (x, xa)) (And (yb, yc)) =
    (case comparator_formula comp_a x yb
      of Eq => comparator_formula comp_a xa yc | Lta => Lta | Gt => Gt)
  | comparator_formula comp_a (And (x, xa)) (Or (yd, ye)) = Lta
  | comparator_formula comp_a (And (x, xa)) (Imp (yf, yg)) = Lta
  | comparator_formula comp_a (Or (x, xa)) (Atom y) = Gt
  | comparator_formula comp_a (Or (x, xa)) Bot = Gt
  | comparator_formula comp_a (Or (x, xa)) (Not ya) = Gt
  | comparator_formula comp_a (Or (x, xa)) (And (yb, yc)) = Gt
  | comparator_formula comp_a (Or (x, xa)) (Or (yd, ye)) =
    (case comparator_formula comp_a x yd
      of Eq => comparator_formula comp_a xa ye | Lta => Lta | Gt => Gt)
  | comparator_formula comp_a (Or (x, xa)) (Imp (yf, yg)) = Lta
  | comparator_formula comp_a (Imp (x, xa)) (Atom y) = Gt
  | comparator_formula comp_a (Imp (x, xa)) Bot = Gt
  | comparator_formula comp_a (Imp (x, xa)) (Not ya) = Gt
  | comparator_formula comp_a (Imp (x, xa)) (And (yb, yc)) = Gt
  | comparator_formula comp_a (Imp (x, xa)) (Or (yd, ye)) = Gt
  | comparator_formula comp_a (Imp (x, xa)) (Imp (yf, yg)) =
    (case comparator_formula comp_a x yf
      of Eq => comparator_formula comp_a xa yg | Lta => Lta | Gt => Gt);

fun less_eq_formula (A1_, A2_) =
  le_of_comp (comparator_formula (comparator_of (A1_, A2_)));

fun less_formula (A1_, A2_) =
  lt_of_comp (comparator_formula (comparator_of (A1_, A2_)));

fun ord_formula (A1_, A2_) =
  {less_eq = less_eq_formula (A1_, A2_), less = less_formula (A1_, A2_)} :
  'a formula ord;

fun preorder_formula (A1_, A2_) = {ord_preorder = ord_formula (A1_, A2_)} :
  'a formula preorder;

fun order_formula (A1_, A2_) = {preorder_order = preorder_formula (A1_, A2_)} :
  'a formula order;

fun linorder_formula (A1_, A2_) = {order_linorder = order_formula (A1_, A2_)} :
  'a formula linorder;

datatype fract = Rata of bool * inta * inta;

fun equal_fract (Rata (x1, x2, x3)) (Rata (y1, y2, y3)) =
  equal_bool x1 y1 andalso (equal_inta x2 y2 andalso equal_inta x3 y3);

datatype json = Object of (char list * json) list | Arraya of json list |
  Stringa of char list | Int of inta | Nata of nat | Rat of fract |
  Boolean of bool | Null;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

fun equal_JSON () = {equal = equal_JSONa} : json equal
and equal_JSONa (Boolean x7) Null = false
  | equal_JSONa Null (Boolean x7) = false
  | equal_JSONa (Rat x6) Null = false
  | equal_JSONa Null (Rat x6) = false
  | equal_JSONa (Rat x6) (Boolean x7) = false
  | equal_JSONa (Boolean x7) (Rat x6) = false
  | equal_JSONa (Nata x5) Null = false
  | equal_JSONa Null (Nata x5) = false
  | equal_JSONa (Nata x5) (Boolean x7) = false
  | equal_JSONa (Boolean x7) (Nata x5) = false
  | equal_JSONa (Nata x5) (Rat x6) = false
  | equal_JSONa (Rat x6) (Nata x5) = false
  | equal_JSONa (Int x4) Null = false
  | equal_JSONa Null (Int x4) = false
  | equal_JSONa (Int x4) (Boolean x7) = false
  | equal_JSONa (Boolean x7) (Int x4) = false
  | equal_JSONa (Int x4) (Rat x6) = false
  | equal_JSONa (Rat x6) (Int x4) = false
  | equal_JSONa (Int x4) (Nata x5) = false
  | equal_JSONa (Nata x5) (Int x4) = false
  | equal_JSONa (Stringa x3) Null = false
  | equal_JSONa Null (Stringa x3) = false
  | equal_JSONa (Stringa x3) (Boolean x7) = false
  | equal_JSONa (Boolean x7) (Stringa x3) = false
  | equal_JSONa (Stringa x3) (Rat x6) = false
  | equal_JSONa (Rat x6) (Stringa x3) = false
  | equal_JSONa (Stringa x3) (Nata x5) = false
  | equal_JSONa (Nata x5) (Stringa x3) = false
  | equal_JSONa (Stringa x3) (Int x4) = false
  | equal_JSONa (Int x4) (Stringa x3) = false
  | equal_JSONa (Arraya x2) Null = false
  | equal_JSONa Null (Arraya x2) = false
  | equal_JSONa (Arraya x2) (Boolean x7) = false
  | equal_JSONa (Boolean x7) (Arraya x2) = false
  | equal_JSONa (Arraya x2) (Rat x6) = false
  | equal_JSONa (Rat x6) (Arraya x2) = false
  | equal_JSONa (Arraya x2) (Nata x5) = false
  | equal_JSONa (Nata x5) (Arraya x2) = false
  | equal_JSONa (Arraya x2) (Int x4) = false
  | equal_JSONa (Int x4) (Arraya x2) = false
  | equal_JSONa (Arraya x2) (Stringa x3) = false
  | equal_JSONa (Stringa x3) (Arraya x2) = false
  | equal_JSONa (Object x1) Null = false
  | equal_JSONa Null (Object x1) = false
  | equal_JSONa (Object x1) (Boolean x7) = false
  | equal_JSONa (Boolean x7) (Object x1) = false
  | equal_JSONa (Object x1) (Rat x6) = false
  | equal_JSONa (Rat x6) (Object x1) = false
  | equal_JSONa (Object x1) (Nata x5) = false
  | equal_JSONa (Nata x5) (Object x1) = false
  | equal_JSONa (Object x1) (Int x4) = false
  | equal_JSONa (Int x4) (Object x1) = false
  | equal_JSONa (Object x1) (Stringa x3) = false
  | equal_JSONa (Stringa x3) (Object x1) = false
  | equal_JSONa (Object x1) (Arraya x2) = false
  | equal_JSONa (Arraya x2) (Object x1) = false
  | equal_JSONa (Boolean x7) (Boolean y7) = equal_bool x7 y7
  | equal_JSONa (Rat x6) (Rat y6) = equal_fract x6 y6
  | equal_JSONa (Nata x5) (Nata y5) = equal_nata x5 y5
  | equal_JSONa (Int x4) (Int y4) = equal_inta x4 y4
  | equal_JSONa (Stringa x3) (Stringa y3) = equal_lista equal_char x3 y3
  | equal_JSONa (Arraya x2) (Arraya y2) = equal_lista (equal_JSON ()) x2 y2
  | equal_JSONa (Object x1) (Object y1) =
    equal_lista (equal_prod (equal_list equal_char) (equal_JSON ())) x1 y1
  | equal_JSONa Null Null = true;
val equal_JSON = equal_JSON ();

fun typerep_proda A_ B_ t =
  Typerep ("Product_Type.prod", [typerep A_ Type, typerep B_ Type]);

fun countable_prod A_ B_ = {} : ('a * 'b) countable;

fun typerep_prod A_ B_ = {typerep = typerep_proda A_ B_} : ('a * 'b) typerep;

fun heap_prod A_ B_ =
  {countable_heap = countable_prod (countable_heap A_) (countable_heap B_),
    typerep_heap = typerep_prod (typerep_heap A_) (typerep_heap B_)}
  : ('a * 'b) heap;

fun showsp_prod s1 s2 p (x, y) =
  shows_string [Chara (false, false, false, true, false, true, false, false)] o
    s1 one_nata x o
    shows_string
      [Chara (false, false, true, true, false, true, false, false),
        Chara (false, false, false, false, false, true, false, false)] o
    s2 one_nata y o
    shows_string [Chara (true, false, false, true, false, true, false, false)];

fun shows_prec_prod A_ B_ = showsp_prod (shows_prec A_) (shows_prec B_);

fun shows_list_prod A_ B_ = showsp_list (shows_prec_prod A_ B_) zero_nata;

fun show_prod A_ B_ =
  {shows_prec = shows_prec_prod A_ B_, shows_list = shows_list_prod A_ B_} :
  ('a * 'b) show;

fun equality_prod eq_a eq_b (x, xa) (y, ya) = eq_a x y andalso eq_b xa ya;

fun ceq_proda A_ B_ =
  (case ceq A_ of NONE => NONE
    | SOME eq_a =>
      (case ceq B_ of NONE => NONE
        | SOME eq_b => SOME (equality_prod eq_a eq_b)));

fun ceq_prod A_ B_ = {ceq = ceq_proda A_ B_} : ('a * 'b) ceq;

fun def_hashmap_size_prod A_ B_ =
  (fn _ => plus_nata (def_hashmap_size A_ Type) (def_hashmap_size B_ Type));

fun hashcode_prod A_ B_ x =
  Word32.+ (Word32.* (hashcode A_
                        (fst x), Word32.fromLargeInt (Int.toLarge (33 : Int.int))), hashcode
            B_ (snd x));

fun hashable_prod A_ B_ =
  {hashcode = hashcode_prod A_ B_,
    def_hashmap_size = def_hashmap_size_prod A_ B_}
  : ('a * 'b) hashable;

fun set_impl_choose2 Set_Monada Set_Monada = Set_Monada
  | set_impl_choose2 Set_RBT Set_RBT = Set_RBT
  | set_impl_choose2 Set_DList Set_DList = Set_DList
  | set_impl_choose2 Set_Collect Set_Collect = Set_Collect
  | set_impl_choose2 x y = Set_Choose;

fun set_impl_proda A_ B_ =
  Phantom
    (set_impl_choose2 (of_phantom (set_impl A_)) (of_phantom (set_impl B_)));

fun set_impl_prod A_ B_ = {set_impl = set_impl_proda A_ B_} :
  ('a * 'b) set_impl;

fun product [] uu = []
  | product (x :: xs) ys = map (fn a => (x, a)) ys @ product xs ys;

fun cEnum_prod A_ B_ =
  (case cEnum A_ of NONE => NONE
    | SOME (enum_a, (enum_all_a, enum_ex_a)) =>
      (case cEnum B_ of NONE => NONE
        | SOME (enum_b, (enum_all_b, enum_ex_b)) =>
          SOME (product enum_a enum_b,
                 ((fn p => enum_all_a (fn x => enum_all_b (fn y => p (x, y)))),
                   (fn p =>
                     enum_ex_a (fn x => enum_ex_b (fn y => p (x, y))))))));

fun cenum_prod A_ B_ = {cEnum = cEnum_prod A_ B_} : ('a * 'b) cenum;

fun finite_UNIV_proda A_ B_ =
  Phantom (of_phantom (finite_UNIV A_) andalso of_phantom (finite_UNIV B_));

fun finite_UNIV_prod A_ B_ = {finite_UNIV = finite_UNIV_proda A_ B_} :
  ('a * 'b) finite_UNIV;

fun comparator_prod comp_a comp_b (x, xa) (y, ya) =
  (case comp_a x y of Eq => comp_b xa ya | Lta => Lta | Gt => Gt);

fun ccompare_proda A_ B_ =
  (case ccompare A_ of NONE => NONE
    | SOME comp_a =>
      (case ccompare B_ of NONE => NONE
        | SOME comp_b => SOME (comparator_prod comp_a comp_b)));

fun ccompare_prod A_ B_ = {ccompare = ccompare_proda A_ B_} :
  ('a * 'b) ccompare;

fun cproper_interval_proda A_ B_ NONE NONE = true
  | cproper_interval_proda A_ B_ NONE (SOME (y1, y2)) =
    cproper_interval A_ NONE (SOME y1) orelse cproper_interval B_ NONE (SOME y2)
  | cproper_interval_proda A_ B_ (SOME (x1, x2)) NONE =
    cproper_interval A_ (SOME x1) NONE orelse cproper_interval B_ (SOME x2) NONE
  | cproper_interval_proda A_ B_ (SOME (x1, x2)) (SOME (y1, y2)) =
    cproper_interval A_ (SOME x1) (SOME y1) orelse
      (lt_of_comp (the (ccompare (ccompare_cproper_interval A_))) x1 y1 andalso
         (cproper_interval B_ (SOME x2) NONE orelse
           cproper_interval B_ NONE (SOME y2)) orelse
        not (lt_of_comp (the (ccompare (ccompare_cproper_interval A_))) y1
              x1) andalso
          cproper_interval B_ (SOME x2) (SOME y2));

fun cproper_interval_prod A_ B_ =
  {ccompare_cproper_interval =
     ccompare_prod (ccompare_cproper_interval A_)
       (ccompare_cproper_interval B_),
    cproper_interval = cproper_interval_proda A_ B_}
  : ('a * 'b) cproper_interval;

datatype func = Func of string;

datatype 'a primitive_numeric_expression = PNE of func * 'a list;

fun equal_funca (Func x) (Func ya) = ((x : string) = ya);

fun equal_primitive_numeric_expression A_ (PNE (x1, x2)) (PNE (y1, y2)) =
  equal_funca x1 y1 andalso equal_lista A_ x2 y2;

datatype 'a numeric_expression = ConstantExpr of rat | DurationExpr |
  AddExpr of 'a numeric_expression * 'a numeric_expression |
  SubExpr of 'a numeric_expression * 'a numeric_expression |
  MulExpr of 'a numeric_expression * 'a numeric_expression |
  DivExpr of 'a numeric_expression * 'a numeric_expression |
  SinExpr of 'a numeric_expression | CosExpr of 'a numeric_expression |
  ExpExpr of 'a numeric_expression | PiExpr |
  FunctionExpr of 'a primitive_numeric_expression;

fun equal_numeric_expression A_ PiExpr (FunctionExpr x11) = false
  | equal_numeric_expression A_ (FunctionExpr x11) PiExpr = false
  | equal_numeric_expression A_ (ExpExpr x9) (FunctionExpr x11) = false
  | equal_numeric_expression A_ (FunctionExpr x11) (ExpExpr x9) = false
  | equal_numeric_expression A_ (ExpExpr x9) PiExpr = false
  | equal_numeric_expression A_ PiExpr (ExpExpr x9) = false
  | equal_numeric_expression A_ (CosExpr x8) (FunctionExpr x11) = false
  | equal_numeric_expression A_ (FunctionExpr x11) (CosExpr x8) = false
  | equal_numeric_expression A_ (CosExpr x8) PiExpr = false
  | equal_numeric_expression A_ PiExpr (CosExpr x8) = false
  | equal_numeric_expression A_ (CosExpr x8) (ExpExpr x9) = false
  | equal_numeric_expression A_ (ExpExpr x9) (CosExpr x8) = false
  | equal_numeric_expression A_ (SinExpr x7) (FunctionExpr x11) = false
  | equal_numeric_expression A_ (FunctionExpr x11) (SinExpr x7) = false
  | equal_numeric_expression A_ (SinExpr x7) PiExpr = false
  | equal_numeric_expression A_ PiExpr (SinExpr x7) = false
  | equal_numeric_expression A_ (SinExpr x7) (ExpExpr x9) = false
  | equal_numeric_expression A_ (ExpExpr x9) (SinExpr x7) = false
  | equal_numeric_expression A_ (SinExpr x7) (CosExpr x8) = false
  | equal_numeric_expression A_ (CosExpr x8) (SinExpr x7) = false
  | equal_numeric_expression A_ (DivExpr (x61, x62)) (FunctionExpr x11) = false
  | equal_numeric_expression A_ (FunctionExpr x11) (DivExpr (x61, x62)) = false
  | equal_numeric_expression A_ (DivExpr (x61, x62)) PiExpr = false
  | equal_numeric_expression A_ PiExpr (DivExpr (x61, x62)) = false
  | equal_numeric_expression A_ (DivExpr (x61, x62)) (ExpExpr x9) = false
  | equal_numeric_expression A_ (ExpExpr x9) (DivExpr (x61, x62)) = false
  | equal_numeric_expression A_ (DivExpr (x61, x62)) (CosExpr x8) = false
  | equal_numeric_expression A_ (CosExpr x8) (DivExpr (x61, x62)) = false
  | equal_numeric_expression A_ (DivExpr (x61, x62)) (SinExpr x7) = false
  | equal_numeric_expression A_ (SinExpr x7) (DivExpr (x61, x62)) = false
  | equal_numeric_expression A_ (MulExpr (x51, x52)) (FunctionExpr x11) = false
  | equal_numeric_expression A_ (FunctionExpr x11) (MulExpr (x51, x52)) = false
  | equal_numeric_expression A_ (MulExpr (x51, x52)) PiExpr = false
  | equal_numeric_expression A_ PiExpr (MulExpr (x51, x52)) = false
  | equal_numeric_expression A_ (MulExpr (x51, x52)) (ExpExpr x9) = false
  | equal_numeric_expression A_ (ExpExpr x9) (MulExpr (x51, x52)) = false
  | equal_numeric_expression A_ (MulExpr (x51, x52)) (CosExpr x8) = false
  | equal_numeric_expression A_ (CosExpr x8) (MulExpr (x51, x52)) = false
  | equal_numeric_expression A_ (MulExpr (x51, x52)) (SinExpr x7) = false
  | equal_numeric_expression A_ (SinExpr x7) (MulExpr (x51, x52)) = false
  | equal_numeric_expression A_ (MulExpr (x51, x52)) (DivExpr (x61, x62)) =
    false
  | equal_numeric_expression A_ (DivExpr (x61, x62)) (MulExpr (x51, x52)) =
    false
  | equal_numeric_expression A_ (SubExpr (x41, x42)) (FunctionExpr x11) = false
  | equal_numeric_expression A_ (FunctionExpr x11) (SubExpr (x41, x42)) = false
  | equal_numeric_expression A_ (SubExpr (x41, x42)) PiExpr = false
  | equal_numeric_expression A_ PiExpr (SubExpr (x41, x42)) = false
  | equal_numeric_expression A_ (SubExpr (x41, x42)) (ExpExpr x9) = false
  | equal_numeric_expression A_ (ExpExpr x9) (SubExpr (x41, x42)) = false
  | equal_numeric_expression A_ (SubExpr (x41, x42)) (CosExpr x8) = false
  | equal_numeric_expression A_ (CosExpr x8) (SubExpr (x41, x42)) = false
  | equal_numeric_expression A_ (SubExpr (x41, x42)) (SinExpr x7) = false
  | equal_numeric_expression A_ (SinExpr x7) (SubExpr (x41, x42)) = false
  | equal_numeric_expression A_ (SubExpr (x41, x42)) (DivExpr (x61, x62)) =
    false
  | equal_numeric_expression A_ (DivExpr (x61, x62)) (SubExpr (x41, x42)) =
    false
  | equal_numeric_expression A_ (SubExpr (x41, x42)) (MulExpr (x51, x52)) =
    false
  | equal_numeric_expression A_ (MulExpr (x51, x52)) (SubExpr (x41, x42)) =
    false
  | equal_numeric_expression A_ (AddExpr (x31, x32)) (FunctionExpr x11) = false
  | equal_numeric_expression A_ (FunctionExpr x11) (AddExpr (x31, x32)) = false
  | equal_numeric_expression A_ (AddExpr (x31, x32)) PiExpr = false
  | equal_numeric_expression A_ PiExpr (AddExpr (x31, x32)) = false
  | equal_numeric_expression A_ (AddExpr (x31, x32)) (ExpExpr x9) = false
  | equal_numeric_expression A_ (ExpExpr x9) (AddExpr (x31, x32)) = false
  | equal_numeric_expression A_ (AddExpr (x31, x32)) (CosExpr x8) = false
  | equal_numeric_expression A_ (CosExpr x8) (AddExpr (x31, x32)) = false
  | equal_numeric_expression A_ (AddExpr (x31, x32)) (SinExpr x7) = false
  | equal_numeric_expression A_ (SinExpr x7) (AddExpr (x31, x32)) = false
  | equal_numeric_expression A_ (AddExpr (x31, x32)) (DivExpr (x61, x62)) =
    false
  | equal_numeric_expression A_ (DivExpr (x61, x62)) (AddExpr (x31, x32)) =
    false
  | equal_numeric_expression A_ (AddExpr (x31, x32)) (MulExpr (x51, x52)) =
    false
  | equal_numeric_expression A_ (MulExpr (x51, x52)) (AddExpr (x31, x32)) =
    false
  | equal_numeric_expression A_ (AddExpr (x31, x32)) (SubExpr (x41, x42)) =
    false
  | equal_numeric_expression A_ (SubExpr (x41, x42)) (AddExpr (x31, x32)) =
    false
  | equal_numeric_expression A_ DurationExpr (FunctionExpr x11) = false
  | equal_numeric_expression A_ (FunctionExpr x11) DurationExpr = false
  | equal_numeric_expression A_ DurationExpr PiExpr = false
  | equal_numeric_expression A_ PiExpr DurationExpr = false
  | equal_numeric_expression A_ DurationExpr (ExpExpr x9) = false
  | equal_numeric_expression A_ (ExpExpr x9) DurationExpr = false
  | equal_numeric_expression A_ DurationExpr (CosExpr x8) = false
  | equal_numeric_expression A_ (CosExpr x8) DurationExpr = false
  | equal_numeric_expression A_ DurationExpr (SinExpr x7) = false
  | equal_numeric_expression A_ (SinExpr x7) DurationExpr = false
  | equal_numeric_expression A_ DurationExpr (DivExpr (x61, x62)) = false
  | equal_numeric_expression A_ (DivExpr (x61, x62)) DurationExpr = false
  | equal_numeric_expression A_ DurationExpr (MulExpr (x51, x52)) = false
  | equal_numeric_expression A_ (MulExpr (x51, x52)) DurationExpr = false
  | equal_numeric_expression A_ DurationExpr (SubExpr (x41, x42)) = false
  | equal_numeric_expression A_ (SubExpr (x41, x42)) DurationExpr = false
  | equal_numeric_expression A_ DurationExpr (AddExpr (x31, x32)) = false
  | equal_numeric_expression A_ (AddExpr (x31, x32)) DurationExpr = false
  | equal_numeric_expression A_ (ConstantExpr x1) (FunctionExpr x11) = false
  | equal_numeric_expression A_ (FunctionExpr x11) (ConstantExpr x1) = false
  | equal_numeric_expression A_ (ConstantExpr x1) PiExpr = false
  | equal_numeric_expression A_ PiExpr (ConstantExpr x1) = false
  | equal_numeric_expression A_ (ConstantExpr x1) (ExpExpr x9) = false
  | equal_numeric_expression A_ (ExpExpr x9) (ConstantExpr x1) = false
  | equal_numeric_expression A_ (ConstantExpr x1) (CosExpr x8) = false
  | equal_numeric_expression A_ (CosExpr x8) (ConstantExpr x1) = false
  | equal_numeric_expression A_ (ConstantExpr x1) (SinExpr x7) = false
  | equal_numeric_expression A_ (SinExpr x7) (ConstantExpr x1) = false
  | equal_numeric_expression A_ (ConstantExpr x1) (DivExpr (x61, x62)) = false
  | equal_numeric_expression A_ (DivExpr (x61, x62)) (ConstantExpr x1) = false
  | equal_numeric_expression A_ (ConstantExpr x1) (MulExpr (x51, x52)) = false
  | equal_numeric_expression A_ (MulExpr (x51, x52)) (ConstantExpr x1) = false
  | equal_numeric_expression A_ (ConstantExpr x1) (SubExpr (x41, x42)) = false
  | equal_numeric_expression A_ (SubExpr (x41, x42)) (ConstantExpr x1) = false
  | equal_numeric_expression A_ (ConstantExpr x1) (AddExpr (x31, x32)) = false
  | equal_numeric_expression A_ (AddExpr (x31, x32)) (ConstantExpr x1) = false
  | equal_numeric_expression A_ (ConstantExpr x1) DurationExpr = false
  | equal_numeric_expression A_ DurationExpr (ConstantExpr x1) = false
  | equal_numeric_expression A_ (FunctionExpr x11) (FunctionExpr y11) =
    equal_primitive_numeric_expression A_ x11 y11
  | equal_numeric_expression A_ (ExpExpr x9) (ExpExpr y9) =
    equal_numeric_expression A_ x9 y9
  | equal_numeric_expression A_ (CosExpr x8) (CosExpr y8) =
    equal_numeric_expression A_ x8 y8
  | equal_numeric_expression A_ (SinExpr x7) (SinExpr y7) =
    equal_numeric_expression A_ x7 y7
  | equal_numeric_expression A_ (DivExpr (x61, x62)) (DivExpr (y61, y62)) =
    equal_numeric_expression A_ x61 y61 andalso
      equal_numeric_expression A_ x62 y62
  | equal_numeric_expression A_ (MulExpr (x51, x52)) (MulExpr (y51, y52)) =
    equal_numeric_expression A_ x51 y51 andalso
      equal_numeric_expression A_ x52 y52
  | equal_numeric_expression A_ (SubExpr (x41, x42)) (SubExpr (y41, y42)) =
    equal_numeric_expression A_ x41 y41 andalso
      equal_numeric_expression A_ x42 y42
  | equal_numeric_expression A_ (AddExpr (x31, x32)) (AddExpr (y31, y32)) =
    equal_numeric_expression A_ x31 y31 andalso
      equal_numeric_expression A_ x32 y32
  | equal_numeric_expression A_ (ConstantExpr x1) (ConstantExpr y1) =
    equal_rata x1 y1
  | equal_numeric_expression A_ PiExpr PiExpr = true
  | equal_numeric_expression A_ DurationExpr DurationExpr = true;

datatype predicate = Pred of string;

fun equal_predicatea (Pred x) (Pred ya) = ((x : string) = ya);

datatype 'a atom = PredAtm of predicate * 'a list | EqAtm of 'a * 'a |
  NumericEqAtm of 'a numeric_expression * 'a numeric_expression |
  NumericLessAtm of 'a numeric_expression * 'a numeric_expression |
  NumericLEAtm of 'a numeric_expression * 'a numeric_expression |
  NumericGreaterAtm of 'a numeric_expression * 'a numeric_expression |
  NumericGEAtm of 'a numeric_expression * 'a numeric_expression;

fun equal_atoma A_ (NumericGreaterAtm (x61, x62)) (NumericGEAtm (x71, x72)) =
  false
  | equal_atoma A_ (NumericGEAtm (x71, x72)) (NumericGreaterAtm (x61, x62)) =
    false
  | equal_atoma A_ (NumericLEAtm (x51, x52)) (NumericGEAtm (x71, x72)) = false
  | equal_atoma A_ (NumericGEAtm (x71, x72)) (NumericLEAtm (x51, x52)) = false
  | equal_atoma A_ (NumericLEAtm (x51, x52)) (NumericGreaterAtm (x61, x62)) =
    false
  | equal_atoma A_ (NumericGreaterAtm (x61, x62)) (NumericLEAtm (x51, x52)) =
    false
  | equal_atoma A_ (NumericLessAtm (x41, x42)) (NumericGEAtm (x71, x72)) = false
  | equal_atoma A_ (NumericGEAtm (x71, x72)) (NumericLessAtm (x41, x42)) = false
  | equal_atoma A_ (NumericLessAtm (x41, x42)) (NumericGreaterAtm (x61, x62)) =
    false
  | equal_atoma A_ (NumericGreaterAtm (x61, x62)) (NumericLessAtm (x41, x42)) =
    false
  | equal_atoma A_ (NumericLessAtm (x41, x42)) (NumericLEAtm (x51, x52)) = false
  | equal_atoma A_ (NumericLEAtm (x51, x52)) (NumericLessAtm (x41, x42)) = false
  | equal_atoma A_ (NumericEqAtm (x31, x32)) (NumericGEAtm (x71, x72)) = false
  | equal_atoma A_ (NumericGEAtm (x71, x72)) (NumericEqAtm (x31, x32)) = false
  | equal_atoma A_ (NumericEqAtm (x31, x32)) (NumericGreaterAtm (x61, x62)) =
    false
  | equal_atoma A_ (NumericGreaterAtm (x61, x62)) (NumericEqAtm (x31, x32)) =
    false
  | equal_atoma A_ (NumericEqAtm (x31, x32)) (NumericLEAtm (x51, x52)) = false
  | equal_atoma A_ (NumericLEAtm (x51, x52)) (NumericEqAtm (x31, x32)) = false
  | equal_atoma A_ (NumericEqAtm (x31, x32)) (NumericLessAtm (x41, x42)) = false
  | equal_atoma A_ (NumericLessAtm (x41, x42)) (NumericEqAtm (x31, x32)) = false
  | equal_atoma A_ (EqAtm (x21, x22)) (NumericGEAtm (x71, x72)) = false
  | equal_atoma A_ (NumericGEAtm (x71, x72)) (EqAtm (x21, x22)) = false
  | equal_atoma A_ (EqAtm (x21, x22)) (NumericGreaterAtm (x61, x62)) = false
  | equal_atoma A_ (NumericGreaterAtm (x61, x62)) (EqAtm (x21, x22)) = false
  | equal_atoma A_ (EqAtm (x21, x22)) (NumericLEAtm (x51, x52)) = false
  | equal_atoma A_ (NumericLEAtm (x51, x52)) (EqAtm (x21, x22)) = false
  | equal_atoma A_ (EqAtm (x21, x22)) (NumericLessAtm (x41, x42)) = false
  | equal_atoma A_ (NumericLessAtm (x41, x42)) (EqAtm (x21, x22)) = false
  | equal_atoma A_ (EqAtm (x21, x22)) (NumericEqAtm (x31, x32)) = false
  | equal_atoma A_ (NumericEqAtm (x31, x32)) (EqAtm (x21, x22)) = false
  | equal_atoma A_ (PredAtm (x11, x12)) (NumericGEAtm (x71, x72)) = false
  | equal_atoma A_ (NumericGEAtm (x71, x72)) (PredAtm (x11, x12)) = false
  | equal_atoma A_ (PredAtm (x11, x12)) (NumericGreaterAtm (x61, x62)) = false
  | equal_atoma A_ (NumericGreaterAtm (x61, x62)) (PredAtm (x11, x12)) = false
  | equal_atoma A_ (PredAtm (x11, x12)) (NumericLEAtm (x51, x52)) = false
  | equal_atoma A_ (NumericLEAtm (x51, x52)) (PredAtm (x11, x12)) = false
  | equal_atoma A_ (PredAtm (x11, x12)) (NumericLessAtm (x41, x42)) = false
  | equal_atoma A_ (NumericLessAtm (x41, x42)) (PredAtm (x11, x12)) = false
  | equal_atoma A_ (PredAtm (x11, x12)) (NumericEqAtm (x31, x32)) = false
  | equal_atoma A_ (NumericEqAtm (x31, x32)) (PredAtm (x11, x12)) = false
  | equal_atoma A_ (PredAtm (x11, x12)) (EqAtm (x21, x22)) = false
  | equal_atoma A_ (EqAtm (x21, x22)) (PredAtm (x11, x12)) = false
  | equal_atoma A_ (NumericGEAtm (x71, x72)) (NumericGEAtm (y71, y72)) =
    equal_numeric_expression A_ x71 y71 andalso
      equal_numeric_expression A_ x72 y72
  | equal_atoma A_ (NumericGreaterAtm (x61, x62)) (NumericGreaterAtm (y61, y62))
    = equal_numeric_expression A_ x61 y61 andalso
        equal_numeric_expression A_ x62 y62
  | equal_atoma A_ (NumericLEAtm (x51, x52)) (NumericLEAtm (y51, y52)) =
    equal_numeric_expression A_ x51 y51 andalso
      equal_numeric_expression A_ x52 y52
  | equal_atoma A_ (NumericLessAtm (x41, x42)) (NumericLessAtm (y41, y42)) =
    equal_numeric_expression A_ x41 y41 andalso
      equal_numeric_expression A_ x42 y42
  | equal_atoma A_ (NumericEqAtm (x31, x32)) (NumericEqAtm (y31, y32)) =
    equal_numeric_expression A_ x31 y31 andalso
      equal_numeric_expression A_ x32 y32
  | equal_atoma A_ (EqAtm (x21, x22)) (EqAtm (y21, y22)) =
    eq A_ x21 y21 andalso eq A_ x22 y22
  | equal_atoma A_ (PredAtm (x11, x12)) (PredAtm (y11, y12)) =
    equal_predicatea x11 y11 andalso equal_lista A_ x12 y12;

fun equal_atom A_ = {equal = equal_atoma A_} : 'a atom equal;

fun comparator_func (Func x) (Func y) =
  comparator_of (equal_literal, linorder_literal) x y;

fun comparator_primitive_numeric_expression comp_e_n_t (PNE (x, xa))
  (PNE (y, ya)) =
  (case comparator_func x y of Eq => comparator_list comp_e_n_t xa ya
    | Lta => Lta | Gt => Gt);

fun comparator_numeric_expression comp_e_n_t (ConstantExpr x) (ConstantExpr y) =
  comparator_of (equal_rat, linorder_rat) x y
  | comparator_numeric_expression comp_e_n_t (ConstantExpr x) DurationExpr = Lta
  | comparator_numeric_expression comp_e_n_t (ConstantExpr x) (AddExpr (ya, yb))
    = Lta
  | comparator_numeric_expression comp_e_n_t (ConstantExpr x) (SubExpr (yc, yd))
    = Lta
  | comparator_numeric_expression comp_e_n_t (ConstantExpr x) (MulExpr (ye, yf))
    = Lta
  | comparator_numeric_expression comp_e_n_t (ConstantExpr x) (DivExpr (yg, yh))
    = Lta
  | comparator_numeric_expression comp_e_n_t (ConstantExpr x) (SinExpr yi) = Lta
  | comparator_numeric_expression comp_e_n_t (ConstantExpr x) (CosExpr yj) = Lta
  | comparator_numeric_expression comp_e_n_t (ConstantExpr x) (ExpExpr yk) = Lta
  | comparator_numeric_expression comp_e_n_t (ConstantExpr x) PiExpr = Lta
  | comparator_numeric_expression comp_e_n_t (ConstantExpr x) (FunctionExpr yl)
    = Lta
  | comparator_numeric_expression comp_e_n_t DurationExpr (ConstantExpr y) = Gt
  | comparator_numeric_expression comp_e_n_t DurationExpr DurationExpr = Eq
  | comparator_numeric_expression comp_e_n_t DurationExpr (AddExpr (ya, yb)) =
    Lta
  | comparator_numeric_expression comp_e_n_t DurationExpr (SubExpr (yc, yd)) =
    Lta
  | comparator_numeric_expression comp_e_n_t DurationExpr (MulExpr (ye, yf)) =
    Lta
  | comparator_numeric_expression comp_e_n_t DurationExpr (DivExpr (yg, yh)) =
    Lta
  | comparator_numeric_expression comp_e_n_t DurationExpr (SinExpr yi) = Lta
  | comparator_numeric_expression comp_e_n_t DurationExpr (CosExpr yj) = Lta
  | comparator_numeric_expression comp_e_n_t DurationExpr (ExpExpr yk) = Lta
  | comparator_numeric_expression comp_e_n_t DurationExpr PiExpr = Lta
  | comparator_numeric_expression comp_e_n_t DurationExpr (FunctionExpr yl) =
    Lta
  | comparator_numeric_expression comp_e_n_t (AddExpr (x, xa)) (ConstantExpr y)
    = Gt
  | comparator_numeric_expression comp_e_n_t (AddExpr (x, xa)) DurationExpr = Gt
  | comparator_numeric_expression comp_e_n_t (AddExpr (x, xa))
    (AddExpr (ya, yb)) =
    (case comparator_numeric_expression comp_e_n_t x ya
      of Eq => comparator_numeric_expression comp_e_n_t xa yb | Lta => Lta
      | Gt => Gt)
  | comparator_numeric_expression comp_e_n_t (AddExpr (x, xa))
    (SubExpr (yc, yd)) = Lta
  | comparator_numeric_expression comp_e_n_t (AddExpr (x, xa))
    (MulExpr (ye, yf)) = Lta
  | comparator_numeric_expression comp_e_n_t (AddExpr (x, xa))
    (DivExpr (yg, yh)) = Lta
  | comparator_numeric_expression comp_e_n_t (AddExpr (x, xa)) (SinExpr yi) =
    Lta
  | comparator_numeric_expression comp_e_n_t (AddExpr (x, xa)) (CosExpr yj) =
    Lta
  | comparator_numeric_expression comp_e_n_t (AddExpr (x, xa)) (ExpExpr yk) =
    Lta
  | comparator_numeric_expression comp_e_n_t (AddExpr (x, xa)) PiExpr = Lta
  | comparator_numeric_expression comp_e_n_t (AddExpr (x, xa)) (FunctionExpr yl)
    = Lta
  | comparator_numeric_expression comp_e_n_t (SubExpr (x, xa)) (ConstantExpr y)
    = Gt
  | comparator_numeric_expression comp_e_n_t (SubExpr (x, xa)) DurationExpr = Gt
  | comparator_numeric_expression comp_e_n_t (SubExpr (x, xa))
    (AddExpr (ya, yb)) = Gt
  | comparator_numeric_expression comp_e_n_t (SubExpr (x, xa))
    (SubExpr (yc, yd)) =
    (case comparator_numeric_expression comp_e_n_t x yc
      of Eq => comparator_numeric_expression comp_e_n_t xa yd | Lta => Lta
      | Gt => Gt)
  | comparator_numeric_expression comp_e_n_t (SubExpr (x, xa))
    (MulExpr (ye, yf)) = Lta
  | comparator_numeric_expression comp_e_n_t (SubExpr (x, xa))
    (DivExpr (yg, yh)) = Lta
  | comparator_numeric_expression comp_e_n_t (SubExpr (x, xa)) (SinExpr yi) =
    Lta
  | comparator_numeric_expression comp_e_n_t (SubExpr (x, xa)) (CosExpr yj) =
    Lta
  | comparator_numeric_expression comp_e_n_t (SubExpr (x, xa)) (ExpExpr yk) =
    Lta
  | comparator_numeric_expression comp_e_n_t (SubExpr (x, xa)) PiExpr = Lta
  | comparator_numeric_expression comp_e_n_t (SubExpr (x, xa)) (FunctionExpr yl)
    = Lta
  | comparator_numeric_expression comp_e_n_t (MulExpr (x, xa)) (ConstantExpr y)
    = Gt
  | comparator_numeric_expression comp_e_n_t (MulExpr (x, xa)) DurationExpr = Gt
  | comparator_numeric_expression comp_e_n_t (MulExpr (x, xa))
    (AddExpr (ya, yb)) = Gt
  | comparator_numeric_expression comp_e_n_t (MulExpr (x, xa))
    (SubExpr (yc, yd)) = Gt
  | comparator_numeric_expression comp_e_n_t (MulExpr (x, xa))
    (MulExpr (ye, yf)) =
    (case comparator_numeric_expression comp_e_n_t x ye
      of Eq => comparator_numeric_expression comp_e_n_t xa yf | Lta => Lta
      | Gt => Gt)
  | comparator_numeric_expression comp_e_n_t (MulExpr (x, xa))
    (DivExpr (yg, yh)) = Lta
  | comparator_numeric_expression comp_e_n_t (MulExpr (x, xa)) (SinExpr yi) =
    Lta
  | comparator_numeric_expression comp_e_n_t (MulExpr (x, xa)) (CosExpr yj) =
    Lta
  | comparator_numeric_expression comp_e_n_t (MulExpr (x, xa)) (ExpExpr yk) =
    Lta
  | comparator_numeric_expression comp_e_n_t (MulExpr (x, xa)) PiExpr = Lta
  | comparator_numeric_expression comp_e_n_t (MulExpr (x, xa)) (FunctionExpr yl)
    = Lta
  | comparator_numeric_expression comp_e_n_t (DivExpr (x, xa)) (ConstantExpr y)
    = Gt
  | comparator_numeric_expression comp_e_n_t (DivExpr (x, xa)) DurationExpr = Gt
  | comparator_numeric_expression comp_e_n_t (DivExpr (x, xa))
    (AddExpr (ya, yb)) = Gt
  | comparator_numeric_expression comp_e_n_t (DivExpr (x, xa))
    (SubExpr (yc, yd)) = Gt
  | comparator_numeric_expression comp_e_n_t (DivExpr (x, xa))
    (MulExpr (ye, yf)) = Gt
  | comparator_numeric_expression comp_e_n_t (DivExpr (x, xa))
    (DivExpr (yg, yh)) =
    (case comparator_numeric_expression comp_e_n_t x yg
      of Eq => comparator_numeric_expression comp_e_n_t xa yh | Lta => Lta
      | Gt => Gt)
  | comparator_numeric_expression comp_e_n_t (DivExpr (x, xa)) (SinExpr yi) =
    Lta
  | comparator_numeric_expression comp_e_n_t (DivExpr (x, xa)) (CosExpr yj) =
    Lta
  | comparator_numeric_expression comp_e_n_t (DivExpr (x, xa)) (ExpExpr yk) =
    Lta
  | comparator_numeric_expression comp_e_n_t (DivExpr (x, xa)) PiExpr = Lta
  | comparator_numeric_expression comp_e_n_t (DivExpr (x, xa)) (FunctionExpr yl)
    = Lta
  | comparator_numeric_expression comp_e_n_t (SinExpr x) (ConstantExpr y) = Gt
  | comparator_numeric_expression comp_e_n_t (SinExpr x) DurationExpr = Gt
  | comparator_numeric_expression comp_e_n_t (SinExpr x) (AddExpr (ya, yb)) = Gt
  | comparator_numeric_expression comp_e_n_t (SinExpr x) (SubExpr (yc, yd)) = Gt
  | comparator_numeric_expression comp_e_n_t (SinExpr x) (MulExpr (ye, yf)) = Gt
  | comparator_numeric_expression comp_e_n_t (SinExpr x) (DivExpr (yg, yh)) = Gt
  | comparator_numeric_expression comp_e_n_t (SinExpr x) (SinExpr yi) =
    comparator_numeric_expression comp_e_n_t x yi
  | comparator_numeric_expression comp_e_n_t (SinExpr x) (CosExpr yj) = Lta
  | comparator_numeric_expression comp_e_n_t (SinExpr x) (ExpExpr yk) = Lta
  | comparator_numeric_expression comp_e_n_t (SinExpr x) PiExpr = Lta
  | comparator_numeric_expression comp_e_n_t (SinExpr x) (FunctionExpr yl) = Lta
  | comparator_numeric_expression comp_e_n_t (CosExpr x) (ConstantExpr y) = Gt
  | comparator_numeric_expression comp_e_n_t (CosExpr x) DurationExpr = Gt
  | comparator_numeric_expression comp_e_n_t (CosExpr x) (AddExpr (ya, yb)) = Gt
  | comparator_numeric_expression comp_e_n_t (CosExpr x) (SubExpr (yc, yd)) = Gt
  | comparator_numeric_expression comp_e_n_t (CosExpr x) (MulExpr (ye, yf)) = Gt
  | comparator_numeric_expression comp_e_n_t (CosExpr x) (DivExpr (yg, yh)) = Gt
  | comparator_numeric_expression comp_e_n_t (CosExpr x) (SinExpr yi) = Gt
  | comparator_numeric_expression comp_e_n_t (CosExpr x) (CosExpr yj) =
    comparator_numeric_expression comp_e_n_t x yj
  | comparator_numeric_expression comp_e_n_t (CosExpr x) (ExpExpr yk) = Lta
  | comparator_numeric_expression comp_e_n_t (CosExpr x) PiExpr = Lta
  | comparator_numeric_expression comp_e_n_t (CosExpr x) (FunctionExpr yl) = Lta
  | comparator_numeric_expression comp_e_n_t (ExpExpr x) (ConstantExpr y) = Gt
  | comparator_numeric_expression comp_e_n_t (ExpExpr x) DurationExpr = Gt
  | comparator_numeric_expression comp_e_n_t (ExpExpr x) (AddExpr (ya, yb)) = Gt
  | comparator_numeric_expression comp_e_n_t (ExpExpr x) (SubExpr (yc, yd)) = Gt
  | comparator_numeric_expression comp_e_n_t (ExpExpr x) (MulExpr (ye, yf)) = Gt
  | comparator_numeric_expression comp_e_n_t (ExpExpr x) (DivExpr (yg, yh)) = Gt
  | comparator_numeric_expression comp_e_n_t (ExpExpr x) (SinExpr yi) = Gt
  | comparator_numeric_expression comp_e_n_t (ExpExpr x) (CosExpr yj) = Gt
  | comparator_numeric_expression comp_e_n_t (ExpExpr x) (ExpExpr yk) =
    comparator_numeric_expression comp_e_n_t x yk
  | comparator_numeric_expression comp_e_n_t (ExpExpr x) PiExpr = Lta
  | comparator_numeric_expression comp_e_n_t (ExpExpr x) (FunctionExpr yl) = Lta
  | comparator_numeric_expression comp_e_n_t PiExpr (ConstantExpr y) = Gt
  | comparator_numeric_expression comp_e_n_t PiExpr DurationExpr = Gt
  | comparator_numeric_expression comp_e_n_t PiExpr (AddExpr (ya, yb)) = Gt
  | comparator_numeric_expression comp_e_n_t PiExpr (SubExpr (yc, yd)) = Gt
  | comparator_numeric_expression comp_e_n_t PiExpr (MulExpr (ye, yf)) = Gt
  | comparator_numeric_expression comp_e_n_t PiExpr (DivExpr (yg, yh)) = Gt
  | comparator_numeric_expression comp_e_n_t PiExpr (SinExpr yi) = Gt
  | comparator_numeric_expression comp_e_n_t PiExpr (CosExpr yj) = Gt
  | comparator_numeric_expression comp_e_n_t PiExpr (ExpExpr yk) = Gt
  | comparator_numeric_expression comp_e_n_t PiExpr PiExpr = Eq
  | comparator_numeric_expression comp_e_n_t PiExpr (FunctionExpr yl) = Lta
  | comparator_numeric_expression comp_e_n_t (FunctionExpr x) (ConstantExpr y) =
    Gt
  | comparator_numeric_expression comp_e_n_t (FunctionExpr x) DurationExpr = Gt
  | comparator_numeric_expression comp_e_n_t (FunctionExpr x) (AddExpr (ya, yb))
    = Gt
  | comparator_numeric_expression comp_e_n_t (FunctionExpr x) (SubExpr (yc, yd))
    = Gt
  | comparator_numeric_expression comp_e_n_t (FunctionExpr x) (MulExpr (ye, yf))
    = Gt
  | comparator_numeric_expression comp_e_n_t (FunctionExpr x) (DivExpr (yg, yh))
    = Gt
  | comparator_numeric_expression comp_e_n_t (FunctionExpr x) (SinExpr yi) = Gt
  | comparator_numeric_expression comp_e_n_t (FunctionExpr x) (CosExpr yj) = Gt
  | comparator_numeric_expression comp_e_n_t (FunctionExpr x) (ExpExpr yk) = Gt
  | comparator_numeric_expression comp_e_n_t (FunctionExpr x) PiExpr = Gt
  | comparator_numeric_expression comp_e_n_t (FunctionExpr x) (FunctionExpr yl)
    = comparator_primitive_numeric_expression comp_e_n_t x yl;

fun comparator_predicate (Pred x) (Pred y) =
  comparator_of (equal_literal, linorder_literal) x y;

fun comparator_atom comp_e_n_t (PredAtm (x, xa)) (PredAtm (y, ya)) =
  (case comparator_predicate x y of Eq => comparator_list comp_e_n_t xa ya
    | Lta => Lta | Gt => Gt)
  | comparator_atom comp_e_n_t (PredAtm (x, xa)) (EqAtm (yb, yc)) = Lta
  | comparator_atom comp_e_n_t (PredAtm (x, xa)) (NumericEqAtm (yd, ye)) = Lta
  | comparator_atom comp_e_n_t (PredAtm (x, xa)) (NumericLessAtm (yf, yg)) = Lta
  | comparator_atom comp_e_n_t (PredAtm (x, xa)) (NumericLEAtm (yh, yi)) = Lta
  | comparator_atom comp_e_n_t (PredAtm (x, xa)) (NumericGreaterAtm (yj, yk)) =
    Lta
  | comparator_atom comp_e_n_t (PredAtm (x, xa)) (NumericGEAtm (yl, ym)) = Lta
  | comparator_atom comp_e_n_t (EqAtm (x, xa)) (PredAtm (y, ya)) = Gt
  | comparator_atom comp_e_n_t (EqAtm (x, xa)) (EqAtm (yb, yc)) =
    (case comp_e_n_t x yb of Eq => comp_e_n_t xa yc | Lta => Lta | Gt => Gt)
  | comparator_atom comp_e_n_t (EqAtm (x, xa)) (NumericEqAtm (yd, ye)) = Lta
  | comparator_atom comp_e_n_t (EqAtm (x, xa)) (NumericLessAtm (yf, yg)) = Lta
  | comparator_atom comp_e_n_t (EqAtm (x, xa)) (NumericLEAtm (yh, yi)) = Lta
  | comparator_atom comp_e_n_t (EqAtm (x, xa)) (NumericGreaterAtm (yj, yk)) =
    Lta
  | comparator_atom comp_e_n_t (EqAtm (x, xa)) (NumericGEAtm (yl, ym)) = Lta
  | comparator_atom comp_e_n_t (NumericEqAtm (x, xa)) (PredAtm (y, ya)) = Gt
  | comparator_atom comp_e_n_t (NumericEqAtm (x, xa)) (EqAtm (yb, yc)) = Gt
  | comparator_atom comp_e_n_t (NumericEqAtm (x, xa)) (NumericEqAtm (yd, ye)) =
    (case comparator_numeric_expression comp_e_n_t x yd
      of Eq => comparator_numeric_expression comp_e_n_t xa ye | Lta => Lta
      | Gt => Gt)
  | comparator_atom comp_e_n_t (NumericEqAtm (x, xa)) (NumericLessAtm (yf, yg))
    = Lta
  | comparator_atom comp_e_n_t (NumericEqAtm (x, xa)) (NumericLEAtm (yh, yi)) =
    Lta
  | comparator_atom comp_e_n_t (NumericEqAtm (x, xa))
    (NumericGreaterAtm (yj, yk)) = Lta
  | comparator_atom comp_e_n_t (NumericEqAtm (x, xa)) (NumericGEAtm (yl, ym)) =
    Lta
  | comparator_atom comp_e_n_t (NumericLessAtm (x, xa)) (PredAtm (y, ya)) = Gt
  | comparator_atom comp_e_n_t (NumericLessAtm (x, xa)) (EqAtm (yb, yc)) = Gt
  | comparator_atom comp_e_n_t (NumericLessAtm (x, xa)) (NumericEqAtm (yd, ye))
    = Gt
  | comparator_atom comp_e_n_t (NumericLessAtm (x, xa))
    (NumericLessAtm (yf, yg)) =
    (case comparator_numeric_expression comp_e_n_t x yf
      of Eq => comparator_numeric_expression comp_e_n_t xa yg | Lta => Lta
      | Gt => Gt)
  | comparator_atom comp_e_n_t (NumericLessAtm (x, xa)) (NumericLEAtm (yh, yi))
    = Lta
  | comparator_atom comp_e_n_t (NumericLessAtm (x, xa))
    (NumericGreaterAtm (yj, yk)) = Lta
  | comparator_atom comp_e_n_t (NumericLessAtm (x, xa)) (NumericGEAtm (yl, ym))
    = Lta
  | comparator_atom comp_e_n_t (NumericLEAtm (x, xa)) (PredAtm (y, ya)) = Gt
  | comparator_atom comp_e_n_t (NumericLEAtm (x, xa)) (EqAtm (yb, yc)) = Gt
  | comparator_atom comp_e_n_t (NumericLEAtm (x, xa)) (NumericEqAtm (yd, ye)) =
    Gt
  | comparator_atom comp_e_n_t (NumericLEAtm (x, xa)) (NumericLessAtm (yf, yg))
    = Gt
  | comparator_atom comp_e_n_t (NumericLEAtm (x, xa)) (NumericLEAtm (yh, yi)) =
    (case comparator_numeric_expression comp_e_n_t x yh
      of Eq => comparator_numeric_expression comp_e_n_t xa yi | Lta => Lta
      | Gt => Gt)
  | comparator_atom comp_e_n_t (NumericLEAtm (x, xa))
    (NumericGreaterAtm (yj, yk)) = Lta
  | comparator_atom comp_e_n_t (NumericLEAtm (x, xa)) (NumericGEAtm (yl, ym)) =
    Lta
  | comparator_atom comp_e_n_t (NumericGreaterAtm (x, xa)) (PredAtm (y, ya)) =
    Gt
  | comparator_atom comp_e_n_t (NumericGreaterAtm (x, xa)) (EqAtm (yb, yc)) = Gt
  | comparator_atom comp_e_n_t (NumericGreaterAtm (x, xa))
    (NumericEqAtm (yd, ye)) = Gt
  | comparator_atom comp_e_n_t (NumericGreaterAtm (x, xa))
    (NumericLessAtm (yf, yg)) = Gt
  | comparator_atom comp_e_n_t (NumericGreaterAtm (x, xa))
    (NumericLEAtm (yh, yi)) = Gt
  | comparator_atom comp_e_n_t (NumericGreaterAtm (x, xa))
    (NumericGreaterAtm (yj, yk)) =
    (case comparator_numeric_expression comp_e_n_t x yj
      of Eq => comparator_numeric_expression comp_e_n_t xa yk | Lta => Lta
      | Gt => Gt)
  | comparator_atom comp_e_n_t (NumericGreaterAtm (x, xa))
    (NumericGEAtm (yl, ym)) = Lta
  | comparator_atom comp_e_n_t (NumericGEAtm (x, xa)) (PredAtm (y, ya)) = Gt
  | comparator_atom comp_e_n_t (NumericGEAtm (x, xa)) (EqAtm (yb, yc)) = Gt
  | comparator_atom comp_e_n_t (NumericGEAtm (x, xa)) (NumericEqAtm (yd, ye)) =
    Gt
  | comparator_atom comp_e_n_t (NumericGEAtm (x, xa)) (NumericLessAtm (yf, yg))
    = Gt
  | comparator_atom comp_e_n_t (NumericGEAtm (x, xa)) (NumericLEAtm (yh, yi)) =
    Gt
  | comparator_atom comp_e_n_t (NumericGEAtm (x, xa))
    (NumericGreaterAtm (yj, yk)) = Gt
  | comparator_atom comp_e_n_t (NumericGEAtm (x, xa)) (NumericGEAtm (yl, ym)) =
    (case comparator_numeric_expression comp_e_n_t x yl
      of Eq => comparator_numeric_expression comp_e_n_t xa ym | Lta => Lta
      | Gt => Gt);

fun less_eq_atom (A1_, A2_) =
  le_of_comp (comparator_atom (comparator_of (A1_, A2_)));

fun less_atom (A1_, A2_) =
  lt_of_comp (comparator_atom (comparator_of (A1_, A2_)));

fun ord_atom (A1_, A2_) =
  {less_eq = less_eq_atom (A1_, A2_), less = less_atom (A1_, A2_)} :
  'a atom ord;

fun preorder_atom (A1_, A2_) = {ord_preorder = ord_atom (A1_, A2_)} :
  'a atom preorder;

fun order_atom (A1_, A2_) = {preorder_order = preorder_atom (A1_, A2_)} :
  'a atom order;

fun ceq_atoma A_ = SOME (equal_atoma A_);

fun ceq_atom A_ = {ceq = ceq_atoma A_} : 'a atom ceq;

val set_impl_atoma : ('a atom, set_impla) phantom = Phantom Set_DList;

val set_impl_atom = {set_impl = set_impl_atoma} : 'a atom set_impl;

fun linorder_atom (A1_, A2_) = {order_linorder = order_atom (A1_, A2_)} :
  'a atom linorder;

fun ccompare_atoma A_ =
  (case ccompare A_ of NONE => NONE
    | SOME comp_ent => SOME (comparator_atom comp_ent));

fun ccompare_atom A_ = {ccompare = ccompare_atoma A_} : 'a atom ccompare;

val equal_func = {equal = equal_funca} : func equal;

fun less_eq_func x = le_of_comp comparator_func x;

fun less_func x = lt_of_comp comparator_func x;

val ord_func = {less_eq = less_eq_func, less = less_func} : func ord;

val preorder_func = {ord_preorder = ord_func} : func preorder;

val order_func = {preorder_order = preorder_func} : func order;

val linorder_func = {order_linorder = order_func} : func linorder;

datatype variable = Vara of string;

fun equal_variablea (Vara x) (Vara ya) = ((x : string) = ya);

datatype object = Obj of string;

fun equal_objecta (Obj x) (Obj ya) = ((x : string) = ya);

datatype term = VAR of variable | CONST of object;

fun equal_terma (VAR x1) (CONST x2) = false
  | equal_terma (CONST x2) (VAR x1) = false
  | equal_terma (CONST x2) (CONST y2) = equal_objecta x2 y2
  | equal_terma (VAR x1) (VAR y1) = equal_variablea x1 y1;

val equal_term = {equal = equal_terma} : term equal;

fun comparator_variable (Vara x) (Vara y) =
  comparator_of (equal_literal, linorder_literal) x y;

fun comparator_object (Obj x) (Obj y) =
  comparator_of (equal_literal, linorder_literal) x y;

fun comparator_term (VAR x) (VAR y) = comparator_variable x y
  | comparator_term (VAR x) (CONST ya) = Lta
  | comparator_term (CONST x) (VAR y) = Gt
  | comparator_term (CONST x) (CONST ya) = comparator_object x ya;

val ccompare_terma : (term -> term -> ordera) option = SOME comparator_term;

val ccompare_term = {ccompare = ccompare_terma} : term ccompare;

datatype typea = Either of string list;

fun equal_typea (Either x) (Either ya) = equal_lista equal_literal x ya;

val equal_type = {equal = equal_typea} : typea equal;

val one_integera : int = (1 : Int.int);

val one_integer = {one = one_integera} : int one;

val zero_integer = {zero = (0 : Int.int)} : int zero;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  int zero_neq_one;

val equal_object = {equal = equal_objecta} : object equal;

fun less_eq_object x = le_of_comp comparator_object x;

fun less_object x = lt_of_comp comparator_object x;

val ord_object = {less_eq = less_eq_object, less = less_object} : object ord;

val preorder_object = {ord_preorder = ord_object} : object preorder;

val order_object = {preorder_order = preorder_object} : object order;

val linorder_object = {order_linorder = order_object} : object linorder;

val ccompare_objecta : (object -> object -> ordera) option =
  SOME comparator_object;

val ccompare_object = {ccompare = ccompare_objecta} : object ccompare;

val mapping_impl_objecta : (object, mapping_impla) phantom =
  Phantom Mapping_RBT;

val mapping_impl_object = {mapping_impl = mapping_impl_objecta} :
  object mapping_impl;

datatype ('a, 'b) bexp = True | Nota of ('a, 'b) bexp |
  Anda of ('a, 'b) bexp * ('a, 'b) bexp | Ora of ('a, 'b) bexp * ('a, 'b) bexp |
  Imply of ('a, 'b) bexp * ('a, 'b) bexp | Eqa of ('a, 'b) exp * ('a, 'b) exp |
  Lea of ('a, 'b) exp * ('a, 'b) exp | Ltb of ('a, 'b) exp * ('a, 'b) exp |
  Ge of ('a, 'b) exp * ('a, 'b) exp | Gta of ('a, 'b) exp * ('a, 'b) exp
and ('a, 'b) exp = Const of 'b | Var of 'a |
  If_then_else of ('a, 'b) bexp * ('a, 'b) exp * ('a, 'b) exp |
  Binop of ('b -> 'b -> 'b) * ('a, 'b) exp * ('a, 'b) exp |
  Unop of ('b -> 'b) * ('a, 'b) exp;

fun shows_exp A_ B_ (Const c) = shows_prec B_ zero_nata c []
  | shows_exp A_ B_ (Var v) = shows_prec A_ zero_nata v []
  | shows_exp A_ B_ (If_then_else (b, e1, e2)) =
    shows_bexp A_ B_ b @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (true, true, true, true, true, true, false, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_exp A_ B_ e1 @
          [Chara (false, false, false, false, false, true, false, false),
            Chara (false, true, false, true, true, true, false, false),
            Chara (false, false, false, false, false, true, false, false)] @
            shows_exp A_ B_ e2
  | shows_exp A_ B_ (Binop (uu, e1, e2)) =
    [Chara (false, true, false, false, false, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, true, true, true, false, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (false, false, false, false, false, true, false, false)] @
      shows_exp A_ B_ e1 @
        [Chara (false, false, false, false, false, true, false, false)] @
          shows_exp A_ B_ e2
  | shows_exp A_ B_ (Unop (uv, e)) =
    [Chara (true, false, true, false, true, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, true, true, true, false, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (false, false, false, false, false, true, false, false)] @
      shows_exp A_ B_ e
and shows_bexp A_ B_ (Ltb (a, b)) =
  shows_exp A_ B_ a @
    [Chara (false, false, false, false, false, true, false, false),
      Chara (false, false, true, true, true, true, false, false),
      Chara (false, false, false, false, false, true, false, false)] @
      shows_exp A_ B_ b
  | shows_bexp A_ B_ (Lea (a, b)) =
    shows_exp A_ B_ a @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, false, true, true, true, true, false, false),
        Chara (true, false, true, true, true, true, false, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_exp A_ B_ b
  | shows_bexp A_ B_ (Eqa (a, b)) =
    shows_exp A_ B_ a @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (true, false, true, true, true, true, false, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_exp A_ B_ b
  | shows_bexp A_ B_ (Ge (a, b)) =
    shows_exp A_ B_ a @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, true, true, true, true, false, false),
        Chara (true, false, true, true, true, true, false, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_exp A_ B_ b
  | shows_bexp A_ B_ (Gta (a, b)) =
    shows_exp A_ B_ a @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, true, true, true, true, false, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_exp A_ B_ b
  | shows_bexp A_ B_ True =
    [Chara (false, false, true, false, true, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, true, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false)]
  | shows_bexp A_ B_ (Nota b) =
    [Chara (true, false, false, false, false, true, false, false),
      Chara (false, false, false, false, false, true, false, false)] @
      shows_bexp A_ B_ b
  | shows_bexp A_ B_ (Anda (a, b)) =
    shows_bexp A_ B_ a @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, true, false, false, true, false, false),
        Chara (false, true, true, false, false, true, false, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_bexp A_ B_ b
  | shows_bexp A_ B_ (Ora (a, b)) =
    shows_bexp A_ B_ a @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, false, true, true, true, true, true, false),
        Chara (false, false, true, true, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_bexp A_ B_ b
  | shows_bexp A_ B_ (Imply (a, b)) =
    shows_bexp A_ B_ a @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (false, true, true, true, true, true, false, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_bexp A_ B_ b;

fun shows_prec_exp A_ B_ p e rest = shows_exp A_ B_ e @ rest;

fun intersperse sep (x :: y :: xs) = x :: sep :: intersperse sep (y :: xs)
  | intersperse uu [] = []
  | intersperse uu [v] = [v];

fun concat xss = foldr (fn a => fn b => a @ b) xss [];

fun shows_list_exp A_ B_ es s =
  [Chara (true, true, false, true, true, false, true, false)] @
    concat
      (intersperse
        [Chara (false, false, true, true, false, true, false, false),
          Chara (false, false, false, false, false, true, false, false)]
        (map (shows_exp A_ B_) es)) @
      [Chara (true, false, true, true, true, false, true, false)] @ s;

fun show_exp A_ B_ =
  {shows_prec = shows_prec_exp A_ B_, shows_list = shows_list_exp A_ B_} :
  ('a, 'b) exp show;

fun shows_prec_bexp A_ B_ p e rest = shows_bexp A_ B_ e @ rest;

fun shows_list_bexp A_ B_ es s =
  [Chara (true, true, false, true, true, false, true, false)] @
    concat
      (intersperse
        [Chara (false, false, true, true, false, true, false, false),
          Chara (false, false, false, false, false, true, false, false)]
        (map (shows_bexp A_ B_) es)) @
      [Chara (true, false, true, true, true, false, true, false)] @ s;

fun show_bexp A_ B_ =
  {shows_prec = shows_prec_bexp A_ B_, shows_list = shows_list_bexp A_ B_} :
  ('a, 'b) bexp show;

val equal_variable = {equal = equal_variablea} : variable equal;

fun less_eq_variable x = le_of_comp comparator_variable x;

fun less_variable x = lt_of_comp comparator_variable x;

val ord_variable = {less_eq = less_eq_variable, less = less_variable} :
  variable ord;

val preorder_variable = {ord_preorder = ord_variable} : variable preorder;

val order_variable = {preorder_order = preorder_variable} : variable order;

val linorder_variable = {order_linorder = order_variable} : variable linorder;

val equal_predicate = {equal = equal_predicatea} : predicate equal;

fun less_eq_predicate x = le_of_comp comparator_predicate x;

fun less_predicate x = lt_of_comp comparator_predicate x;

val ord_predicate = {less_eq = less_eq_predicate, less = less_predicate} :
  predicate ord;

val preorder_predicate = {ord_preorder = ord_predicate} : predicate preorder;

val order_predicate = {preorder_order = preorder_predicate} : predicate order;

val ceq_predicatea : (predicate -> predicate -> bool) option =
  SOME equal_predicatea;

val ceq_predicate = {ceq = ceq_predicatea} : predicate ceq;

val set_impl_predicatea : (predicate, set_impla) phantom = Phantom Set_DList;

val set_impl_predicate = {set_impl = set_impl_predicatea} : predicate set_impl;

val linorder_predicate = {order_linorder = order_predicate} :
  predicate linorder;

val finite_UNIV_predicatea : (predicate, bool) phantom = Phantom false;

val card_UNIV_predicatea : (predicate, nat) phantom = Phantom zero_nata;

type 'a card_UNIV =
  {finite_UNIV_card_UNIV : 'a finite_UNIV, card_UNIV : ('a, nat) phantom};
val finite_UNIV_card_UNIV = #finite_UNIV_card_UNIV :
  'a card_UNIV -> 'a finite_UNIV;
val card_UNIV = #card_UNIV : 'a card_UNIV -> ('a, nat) phantom;

val finite_UNIV_predicate = {finite_UNIV = finite_UNIV_predicatea} :
  predicate finite_UNIV;

val card_UNIV_predicate =
  {finite_UNIV_card_UNIV = finite_UNIV_predicate,
    card_UNIV = card_UNIV_predicatea}
  : predicate card_UNIV;

val ccompare_predicatea : (predicate -> predicate -> ordera) option =
  SOME comparator_predicate;

val ccompare_predicate = {ccompare = ccompare_predicatea} : predicate ccompare;

fun cproper_interval_predicatea uu uv = (raise Fail "undefined");

val cproper_interval_predicate =
  {ccompare_cproper_interval = ccompare_predicate,
    cproper_interval = cproper_interval_predicatea}
  : predicate cproper_interval;

datatype numeric_effect_op = Assign | ScaleUp | ScaleDown | Increase | Decrease;

datatype 'a numeric_effect =
  NumericEffect of
    numeric_effect_op * 'a primitive_numeric_expression * 'a numeric_expression;

datatype 'a ast_effect =
  Effect of
    'a atom formula list * 'a atom formula list * 'a numeric_effect list;

fun equal_numeric_effect_op Increase Decrease = false
  | equal_numeric_effect_op Decrease Increase = false
  | equal_numeric_effect_op ScaleDown Decrease = false
  | equal_numeric_effect_op Decrease ScaleDown = false
  | equal_numeric_effect_op ScaleDown Increase = false
  | equal_numeric_effect_op Increase ScaleDown = false
  | equal_numeric_effect_op ScaleUp Decrease = false
  | equal_numeric_effect_op Decrease ScaleUp = false
  | equal_numeric_effect_op ScaleUp Increase = false
  | equal_numeric_effect_op Increase ScaleUp = false
  | equal_numeric_effect_op ScaleUp ScaleDown = false
  | equal_numeric_effect_op ScaleDown ScaleUp = false
  | equal_numeric_effect_op Assign Decrease = false
  | equal_numeric_effect_op Decrease Assign = false
  | equal_numeric_effect_op Assign Increase = false
  | equal_numeric_effect_op Increase Assign = false
  | equal_numeric_effect_op Assign ScaleDown = false
  | equal_numeric_effect_op ScaleDown Assign = false
  | equal_numeric_effect_op Assign ScaleUp = false
  | equal_numeric_effect_op ScaleUp Assign = false
  | equal_numeric_effect_op Decrease Decrease = true
  | equal_numeric_effect_op Increase Increase = true
  | equal_numeric_effect_op ScaleDown ScaleDown = true
  | equal_numeric_effect_op ScaleUp ScaleUp = true
  | equal_numeric_effect_op Assign Assign = true;

fun equal_numeric_effecta A_ (NumericEffect (x1, x2, x3))
  (NumericEffect (y1, y2, y3)) =
  equal_numeric_effect_op x1 y1 andalso
    (equal_primitive_numeric_expression A_ x2 y2 andalso
      equal_numeric_expression A_ x3 y3);

fun equal_numeric_effect A_ = {equal = equal_numeric_effecta A_} :
  'a numeric_effect equal;

fun equal_ast_effecta A_ (Effect (x1, x2, x3)) (Effect (y1, y2, y3)) =
  equal_lista (equal_formula (equal_atom A_)) x1 y1 andalso
    (equal_lista (equal_formula (equal_atom A_)) x2 y2 andalso
      equal_lista (equal_numeric_effect A_) x3 y3);

fun equal_ast_effect A_ = {equal = equal_ast_effecta A_} : 'a ast_effect equal;

datatype 'a lower_bound = GT of 'a | GE of 'a;

fun less_eq_lower_bound A_ (GE x) (GE y) =
  less_eq ((ord_preorder o preorder_order o order_linorder) A_) x y
  | less_eq_lower_bound A_ (GE x) (GT y) =
    less_eq ((ord_preorder o preorder_order o order_linorder) A_) x y
  | less_eq_lower_bound A_ (GT x) (GE y) =
    less ((ord_preorder o preorder_order o order_linorder) A_) x y
  | less_eq_lower_bound A_ (GT x) (GT y) =
    less_eq ((ord_preorder o preorder_order o order_linorder) A_) x y;

fun less_lower_bound A_ (GE x) (GE y) =
  less ((ord_preorder o preorder_order o order_linorder) A_) x y
  | less_lower_bound A_ (GE x) (GT y) =
    less_eq ((ord_preorder o preorder_order o order_linorder) A_) x y
  | less_lower_bound A_ (GT x) (GE y) =
    less ((ord_preorder o preorder_order o order_linorder) A_) x y
  | less_lower_bound A_ (GT x) (GT y) =
    less ((ord_preorder o preorder_order o order_linorder) A_) x y;

fun ord_lower_bound A_ =
  {less_eq = less_eq_lower_bound A_, less = less_lower_bound A_} :
  'a lower_bound ord;

fun preorder_lower_bound A_ = {ord_preorder = ord_lower_bound A_} :
  'a lower_bound preorder;

fun order_lower_bound A_ = {preorder_order = preorder_lower_bound A_} :
  'a lower_bound order;

fun linorder_lower_bound A_ = {order_linorder = order_lower_bound A_} :
  'a lower_bound linorder;

datatype 'a upper_bound = LT of 'a | LE of 'a;

fun less_eq_upper_bound A_ (LT x) (LT y) =
  less_eq ((ord_preorder o preorder_order o order_linorder) A_) x y
  | less_eq_upper_bound A_ (LT x) (LE y) =
    less_eq ((ord_preorder o preorder_order o order_linorder) A_) x y
  | less_eq_upper_bound A_ (LE x) (LT y) =
    less ((ord_preorder o preorder_order o order_linorder) A_) x y
  | less_eq_upper_bound A_ (LE x) (LE y) =
    less_eq ((ord_preorder o preorder_order o order_linorder) A_) x y;

fun less_upper_bound A_ (LT x) (LT y) =
  less ((ord_preorder o preorder_order o order_linorder) A_) x y
  | less_upper_bound A_ (LT x) (LE y) =
    less_eq ((ord_preorder o preorder_order o order_linorder) A_) x y
  | less_upper_bound A_ (LE x) (LT y) =
    less ((ord_preorder o preorder_order o order_linorder) A_) x y
  | less_upper_bound A_ (LE x) (LE y) =
    less ((ord_preorder o preorder_order o order_linorder) A_) x y;

fun ord_upper_bound A_ =
  {less_eq = less_eq_upper_bound A_, less = less_upper_bound A_} :
  'a upper_bound ord;

fun preorder_upper_bound A_ = {ord_preorder = ord_upper_bound A_} :
  'a upper_bound preorder;

fun order_upper_bound A_ = {preorder_order = preorder_upper_bound A_} :
  'a upper_bound order;

fun linorder_upper_bound A_ = {order_linorder = order_upper_bound A_} :
  'a upper_bound linorder;

datatype ('a, 'b) acconstraint = LTa of 'a * 'b | LEa of 'a * 'b |
  EQa of 'a * 'b | GTa of 'a * 'b | GEa of 'a * 'b;

fun showsp_acconstraint show_c show_t p (LTa (x, y)) =
  shows_pl p o
    shows_string
      [Chara (false, false, true, true, false, false, true, false),
        Chara (false, false, true, false, true, false, true, false)] o
    shows_space o
    show_c one_nata x o
    shows_space o
    show_t one_nata y o
    shows_pr p
  | showsp_acconstraint show_c show_t p (LEa (x, y)) =
    shows_pl p o
      shows_string
        [Chara (false, false, true, true, false, false, true, false),
          Chara (true, false, true, false, false, false, true, false)] o
      shows_space o
      show_c one_nata x o
      shows_space o
      show_t one_nata y o
      shows_pr p
  | showsp_acconstraint show_c show_t p (EQa (x, y)) =
    shows_pl p o
      shows_string
        [Chara (true, false, true, false, false, false, true, false),
          Chara (true, false, false, false, true, false, true, false)] o
      shows_space o
      show_c one_nata x o
      shows_space o
      show_t one_nata y o
      shows_pr p
  | showsp_acconstraint show_c show_t p (GTa (x, y)) =
    shows_pl p o
      shows_string
        [Chara (true, true, true, false, false, false, true, false),
          Chara (false, false, true, false, true, false, true, false)] o
      shows_space o
      show_c one_nata x o
      shows_space o
      show_t one_nata y o
      shows_pr p
  | showsp_acconstraint show_c show_t p (GEa (x, y)) =
    shows_pl p o
      shows_string
        [Chara (true, true, true, false, false, false, true, false),
          Chara (true, false, true, false, false, false, true, false)] o
      shows_space o
      show_c one_nata x o
      shows_space o
      show_t one_nata y o
      shows_pr p;

fun shows_prec_acconstraint A_ B_ =
  showsp_acconstraint (shows_prec A_) (shows_prec B_);

fun shows_list_acconstraint A_ B_ =
  showsp_list (shows_prec_acconstraint A_ B_) zero_nata;

fun show_acconstraint A_ B_ =
  {shows_prec = shows_prec_acconstraint A_ B_,
    shows_list = shows_list_acconstraint A_ B_}
  : ('a, 'b) acconstraint show;

fun equal_acconstraint A_ B_ (GTa (x41, x42)) (GEa (x51, x52)) = false
  | equal_acconstraint A_ B_ (GEa (x51, x52)) (GTa (x41, x42)) = false
  | equal_acconstraint A_ B_ (EQa (x31, x32)) (GEa (x51, x52)) = false
  | equal_acconstraint A_ B_ (GEa (x51, x52)) (EQa (x31, x32)) = false
  | equal_acconstraint A_ B_ (EQa (x31, x32)) (GTa (x41, x42)) = false
  | equal_acconstraint A_ B_ (GTa (x41, x42)) (EQa (x31, x32)) = false
  | equal_acconstraint A_ B_ (LEa (x21, x22)) (GEa (x51, x52)) = false
  | equal_acconstraint A_ B_ (GEa (x51, x52)) (LEa (x21, x22)) = false
  | equal_acconstraint A_ B_ (LEa (x21, x22)) (GTa (x41, x42)) = false
  | equal_acconstraint A_ B_ (GTa (x41, x42)) (LEa (x21, x22)) = false
  | equal_acconstraint A_ B_ (LEa (x21, x22)) (EQa (x31, x32)) = false
  | equal_acconstraint A_ B_ (EQa (x31, x32)) (LEa (x21, x22)) = false
  | equal_acconstraint A_ B_ (LTa (x11, x12)) (GEa (x51, x52)) = false
  | equal_acconstraint A_ B_ (GEa (x51, x52)) (LTa (x11, x12)) = false
  | equal_acconstraint A_ B_ (LTa (x11, x12)) (GTa (x41, x42)) = false
  | equal_acconstraint A_ B_ (GTa (x41, x42)) (LTa (x11, x12)) = false
  | equal_acconstraint A_ B_ (LTa (x11, x12)) (EQa (x31, x32)) = false
  | equal_acconstraint A_ B_ (EQa (x31, x32)) (LTa (x11, x12)) = false
  | equal_acconstraint A_ B_ (LTa (x11, x12)) (LEa (x21, x22)) = false
  | equal_acconstraint A_ B_ (LEa (x21, x22)) (LTa (x11, x12)) = false
  | equal_acconstraint A_ B_ (GEa (x51, x52)) (GEa (y51, y52)) =
    eq A_ x51 y51 andalso eq B_ x52 y52
  | equal_acconstraint A_ B_ (GTa (x41, x42)) (GTa (y41, y42)) =
    eq A_ x41 y41 andalso eq B_ x42 y42
  | equal_acconstraint A_ B_ (EQa (x31, x32)) (EQa (y31, y32)) =
    eq A_ x31 y31 andalso eq B_ x32 y32
  | equal_acconstraint A_ B_ (LEa (x21, x22)) (LEa (y21, y22)) =
    eq A_ x21 y21 andalso eq B_ x22 y22
  | equal_acconstraint A_ B_ (LTa (x11, x12)) (LTa (y11, y12)) =
    eq A_ x11 y11 andalso eq B_ x12 y12;

fun ceq_acconstrainta A_ B_ = SOME (equal_acconstraint A_ B_);

fun ceq_acconstraint A_ B_ = {ceq = ceq_acconstrainta A_ B_} :
  ('a, 'b) acconstraint ceq;

val set_impl_acconstrainta : (('a, 'b) acconstraint, set_impla) phantom =
  Phantom Set_RBT;

val set_impl_acconstraint = {set_impl = set_impl_acconstrainta} :
  ('a, 'b) acconstraint set_impl;

fun comparator_acconstraint comp_c comp_t (LTa (x, xa)) (LTa (y, ya)) =
  (case comp_c x y of Eq => comp_t xa ya | Lta => Lta | Gt => Gt)
  | comparator_acconstraint comp_c comp_t (LTa (x, xa)) (LEa (yb, yc)) = Lta
  | comparator_acconstraint comp_c comp_t (LTa (x, xa)) (EQa (yd, ye)) = Lta
  | comparator_acconstraint comp_c comp_t (LTa (x, xa)) (GTa (yf, yg)) = Lta
  | comparator_acconstraint comp_c comp_t (LTa (x, xa)) (GEa (yh, yi)) = Lta
  | comparator_acconstraint comp_c comp_t (LEa (x, xa)) (LTa (y, ya)) = Gt
  | comparator_acconstraint comp_c comp_t (LEa (x, xa)) (LEa (yb, yc)) =
    (case comp_c x yb of Eq => comp_t xa yc | Lta => Lta | Gt => Gt)
  | comparator_acconstraint comp_c comp_t (LEa (x, xa)) (EQa (yd, ye)) = Lta
  | comparator_acconstraint comp_c comp_t (LEa (x, xa)) (GTa (yf, yg)) = Lta
  | comparator_acconstraint comp_c comp_t (LEa (x, xa)) (GEa (yh, yi)) = Lta
  | comparator_acconstraint comp_c comp_t (EQa (x, xa)) (LTa (y, ya)) = Gt
  | comparator_acconstraint comp_c comp_t (EQa (x, xa)) (LEa (yb, yc)) = Gt
  | comparator_acconstraint comp_c comp_t (EQa (x, xa)) (EQa (yd, ye)) =
    (case comp_c x yd of Eq => comp_t xa ye | Lta => Lta | Gt => Gt)
  | comparator_acconstraint comp_c comp_t (EQa (x, xa)) (GTa (yf, yg)) = Lta
  | comparator_acconstraint comp_c comp_t (EQa (x, xa)) (GEa (yh, yi)) = Lta
  | comparator_acconstraint comp_c comp_t (GTa (x, xa)) (LTa (y, ya)) = Gt
  | comparator_acconstraint comp_c comp_t (GTa (x, xa)) (LEa (yb, yc)) = Gt
  | comparator_acconstraint comp_c comp_t (GTa (x, xa)) (EQa (yd, ye)) = Gt
  | comparator_acconstraint comp_c comp_t (GTa (x, xa)) (GTa (yf, yg)) =
    (case comp_c x yf of Eq => comp_t xa yg | Lta => Lta | Gt => Gt)
  | comparator_acconstraint comp_c comp_t (GTa (x, xa)) (GEa (yh, yi)) = Lta
  | comparator_acconstraint comp_c comp_t (GEa (x, xa)) (LTa (y, ya)) = Gt
  | comparator_acconstraint comp_c comp_t (GEa (x, xa)) (LEa (yb, yc)) = Gt
  | comparator_acconstraint comp_c comp_t (GEa (x, xa)) (EQa (yd, ye)) = Gt
  | comparator_acconstraint comp_c comp_t (GEa (x, xa)) (GTa (yf, yg)) = Gt
  | comparator_acconstraint comp_c comp_t (GEa (x, xa)) (GEa (yh, yi)) =
    (case comp_c x yh of Eq => comp_t xa yi | Lta => Lta | Gt => Gt);

fun compare_acconstraint A_ B_ =
  comparator_acconstraint (compare A_) (compare B_);

fun ccompare_acconstrainta A_ B_ = SOME (compare_acconstraint A_ B_);

fun ccompare_acconstraint A_ B_ = {ccompare = ccompare_acconstrainta A_ B_} :
  ('a, 'b) acconstraint ccompare;

datatype duration_op = EQ | LEQ | GEQ;

fun equal_duration_op LEQ GEQ = false
  | equal_duration_op GEQ LEQ = false
  | equal_duration_op EQ GEQ = false
  | equal_duration_op GEQ EQ = false
  | equal_duration_op EQ LEQ = false
  | equal_duration_op LEQ EQ = false
  | equal_duration_op GEQ GEQ = true
  | equal_duration_op LEQ LEQ = true
  | equal_duration_op EQ EQ = true;

datatype 'a duration_constraint =
  DurationConstraint of duration_op * 'a numeric_expression;

fun equal_duration_constrainta A_ (DurationConstraint (x1, x2))
  (DurationConstraint (y1, y2)) =
  equal_duration_op x1 y1 andalso equal_numeric_expression A_ x2 y2;

fun equal_duration_constraint A_ = {equal = equal_duration_constrainta A_} :
  'a duration_constraint equal;

datatype temporal_annotation = At_Start | Over_All | At_End;

fun equal_temporal_annotationa Over_All At_End = false
  | equal_temporal_annotationa At_End Over_All = false
  | equal_temporal_annotationa At_Start At_End = false
  | equal_temporal_annotationa At_End At_Start = false
  | equal_temporal_annotationa At_Start Over_All = false
  | equal_temporal_annotationa Over_All At_Start = false
  | equal_temporal_annotationa At_End At_End = true
  | equal_temporal_annotationa Over_All Over_All = true
  | equal_temporal_annotationa At_Start At_Start = true;

val equal_temporal_annotation = {equal = equal_temporal_annotationa} :
  temporal_annotation equal;

datatype ast_temporal_durative_action_body =
  DurativeActionBody of
    (temporal_annotation * term duration_constraint) list *
      (temporal_annotation * term atom formula) list *
      (temporal_annotation * term ast_effect) list;

fun equal_ast_temporal_durative_action_body (DurativeActionBody (x1, x2, x3))
  (DurativeActionBody (y1, y2, y3)) =
  equal_lista
    (equal_prod equal_temporal_annotation
      (equal_duration_constraint equal_term))
    x1 y1 andalso
    (equal_lista
       (equal_prod equal_temporal_annotation
         (equal_formula (equal_atom equal_term)))
       x2 y2 andalso
      equal_lista
        (equal_prod equal_temporal_annotation (equal_ast_effect equal_term)) x3
        y3);

datatype ast_simple_action_body =
  SimpleActionBody of term atom formula * term ast_effect;

fun equal_ast_simple_action_body (SimpleActionBody (x1, x2))
  (SimpleActionBody (y1, y2)) =
  equal_formulaa (equal_atom equal_term) x1 y1 andalso
    equal_ast_effecta equal_term x2 y2;

datatype ast_action_head = ActionHead of string * (variable * typea) list;

datatype ast_temporal_action_schema =
  SimpleActionSchemaa of ast_action_head * ast_simple_action_body |
  DurativeActionSchema of ast_action_head * ast_temporal_durative_action_body;

fun equal_ast_action_head (ActionHead (x1, x2)) (ActionHead (y1, y2)) =
  ((x1 : string) = y1) andalso
    equal_lista (equal_prod equal_variable equal_type) x2 y2;

fun equal_ast_temporal_action_schema (SimpleActionSchemaa (x11, x12))
  (DurativeActionSchema (x21, x22)) = false
  | equal_ast_temporal_action_schema (DurativeActionSchema (x21, x22))
    (SimpleActionSchemaa (x11, x12)) = false
  | equal_ast_temporal_action_schema (DurativeActionSchema (x21, x22))
    (DurativeActionSchema (y21, y22)) =
    equal_ast_action_head x21 y21 andalso
      equal_ast_temporal_durative_action_body x22 y22
  | equal_ast_temporal_action_schema (SimpleActionSchemaa (x11, x12))
    (SimpleActionSchemaa (y11, y12)) =
    equal_ast_action_head x11 y11 andalso equal_ast_simple_action_body x12 y12;

val ceq_ast_temporal_action_schemaa :
  (ast_temporal_action_schema -> ast_temporal_action_schema -> bool) option
  = SOME equal_ast_temporal_action_schema;

val ceq_ast_temporal_action_schema = {ceq = ceq_ast_temporal_action_schemaa} :
  ast_temporal_action_schema ceq;

val set_impl_ast_temporal_action_schemaa :
  (ast_temporal_action_schema, set_impla) phantom
  = Phantom Set_DList;

val set_impl_ast_temporal_action_schema =
  {set_impl = set_impl_ast_temporal_action_schemaa} :
  ast_temporal_action_schema set_impl;

fun comparator_temporal_annotation At_Start At_Start = Eq
  | comparator_temporal_annotation At_Start Over_All = Lta
  | comparator_temporal_annotation At_Start At_End = Lta
  | comparator_temporal_annotation Over_All At_Start = Gt
  | comparator_temporal_annotation Over_All Over_All = Eq
  | comparator_temporal_annotation Over_All At_End = Lta
  | comparator_temporal_annotation At_End At_Start = Gt
  | comparator_temporal_annotation At_End Over_All = Gt
  | comparator_temporal_annotation At_End At_End = Eq;

fun comparator_duration_op EQ EQ = Eq
  | comparator_duration_op EQ LEQ = Lta
  | comparator_duration_op EQ GEQ = Lta
  | comparator_duration_op LEQ EQ = Gt
  | comparator_duration_op LEQ LEQ = Eq
  | comparator_duration_op LEQ GEQ = Lta
  | comparator_duration_op GEQ EQ = Gt
  | comparator_duration_op GEQ LEQ = Gt
  | comparator_duration_op GEQ GEQ = Eq;

fun comparator_duration_constraint comp_e_n_t (DurationConstraint (x, xa))
  (DurationConstraint (y, ya)) =
  (case comparator_duration_op x y
    of Eq => comparator_numeric_expression comp_e_n_t xa ya | Lta => Lta
    | Gt => Gt);

fun comparator_numeric_effect_op Assign Assign = Eq
  | comparator_numeric_effect_op Assign ScaleUp = Lta
  | comparator_numeric_effect_op Assign ScaleDown = Lta
  | comparator_numeric_effect_op Assign Increase = Lta
  | comparator_numeric_effect_op Assign Decrease = Lta
  | comparator_numeric_effect_op ScaleUp Assign = Gt
  | comparator_numeric_effect_op ScaleUp ScaleUp = Eq
  | comparator_numeric_effect_op ScaleUp ScaleDown = Lta
  | comparator_numeric_effect_op ScaleUp Increase = Lta
  | comparator_numeric_effect_op ScaleUp Decrease = Lta
  | comparator_numeric_effect_op ScaleDown Assign = Gt
  | comparator_numeric_effect_op ScaleDown ScaleUp = Gt
  | comparator_numeric_effect_op ScaleDown ScaleDown = Eq
  | comparator_numeric_effect_op ScaleDown Increase = Lta
  | comparator_numeric_effect_op ScaleDown Decrease = Lta
  | comparator_numeric_effect_op Increase Assign = Gt
  | comparator_numeric_effect_op Increase ScaleUp = Gt
  | comparator_numeric_effect_op Increase ScaleDown = Gt
  | comparator_numeric_effect_op Increase Increase = Eq
  | comparator_numeric_effect_op Increase Decrease = Lta
  | comparator_numeric_effect_op Decrease Assign = Gt
  | comparator_numeric_effect_op Decrease ScaleUp = Gt
  | comparator_numeric_effect_op Decrease ScaleDown = Gt
  | comparator_numeric_effect_op Decrease Increase = Gt
  | comparator_numeric_effect_op Decrease Decrease = Eq;

fun comparator_numeric_effect comp_e_n_t (NumericEffect (x, xa, xb))
  (NumericEffect (y, ya, yb)) =
  (case comparator_numeric_effect_op x y
    of Eq =>
      (case comparator_primitive_numeric_expression comp_e_n_t xa ya
        of Eq => comparator_numeric_expression comp_e_n_t xb yb | Lta => Lta
        | Gt => Gt)
    | Lta => Lta | Gt => Gt);

fun comparator_ast_effect comp_e_n_t (Effect (x, xa, xb)) (Effect (y, ya, yb)) =
  (case comparator_list (comparator_formula (comparator_atom comp_e_n_t)) x y
    of Eq =>
      (case comparator_list (comparator_formula (comparator_atom comp_e_n_t)) xa
              ya
        of Eq => comparator_list (comparator_numeric_effect comp_e_n_t) xb yb
        | Lta => Lta | Gt => Gt)
    | Lta => Lta | Gt => Gt);

fun comparator_ast_temporal_durative_action_body
  (DurativeActionBody (x, xa, xb)) (DurativeActionBody (y, ya, yb)) =
  (case comparator_list
          (comparator_prod comparator_temporal_annotation
            (comparator_duration_constraint comparator_term))
          x y
    of Eq =>
      (case comparator_list
              (comparator_prod comparator_temporal_annotation
                (comparator_formula (comparator_atom comparator_term)))
              xa ya
        of Eq =>
          comparator_list
            (comparator_prod comparator_temporal_annotation
              (comparator_ast_effect comparator_term))
            xb yb
        | Lta => Lta | Gt => Gt)
    | Lta => Lta | Gt => Gt);

fun comparator_ast_simple_action_body (SimpleActionBody (x, xa))
  (SimpleActionBody (y, ya)) =
  (case comparator_formula (comparator_atom comparator_term) x y
    of Eq => comparator_ast_effect comparator_term xa ya | Lta => Lta
    | Gt => Gt);

fun comparator_type (Either x) (Either y) =
  comparator_list (comparator_of (equal_literal, linorder_literal)) x y;

fun comparator_ast_action_head (ActionHead (x, xa)) (ActionHead (y, ya)) =
  (case comparator_of (equal_literal, linorder_literal) x y
    of Eq =>
      comparator_list (comparator_prod comparator_variable comparator_type) xa
        ya
    | Lta => Lta | Gt => Gt);

fun comparator_ast_temporal_action_schema (SimpleActionSchemaa (x, xa))
  (SimpleActionSchemaa (y, ya)) =
  (case comparator_ast_action_head x y
    of Eq => comparator_ast_simple_action_body xa ya | Lta => Lta | Gt => Gt)
  | comparator_ast_temporal_action_schema (SimpleActionSchemaa (x, xa))
    (DurativeActionSchema (yb, yc)) = Lta
  | comparator_ast_temporal_action_schema (DurativeActionSchema (x, xa))
    (SimpleActionSchemaa (y, ya)) = Gt
  | comparator_ast_temporal_action_schema (DurativeActionSchema (x, xa))
    (DurativeActionSchema (yb, yc)) =
    (case comparator_ast_action_head x yb
      of Eq => comparator_ast_temporal_durative_action_body xa yc | Lta => Lta
      | Gt => Gt);

val ccompare_ast_temporal_action_schemaa :
  (ast_temporal_action_schema -> ast_temporal_action_schema -> ordera) option
  = SOME comparator_ast_temporal_action_schema;

val ccompare_ast_temporal_action_schema =
  {ccompare = ccompare_ast_temporal_action_schemaa} :
  ast_temporal_action_schema ccompare;

datatype ('b, 'a) alist = Alist of ('b * 'a) list;

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b;

datatype ('a, 'b) mapping = Assoc_List_Mapping of ('a, 'b) alist |
  RBT_Mapping of ('a, 'b) mapping_rbt | Mapping of ('a -> 'b option);

datatype time = Time of inta;

datatype ('a, 'b) hashtable = HashTable of (('a * 'b) list) array * nat;

datatype ('b, 'a) comp_fun_idem = Abs_comp_fun_idem of ('b -> 'a -> 'a);

datatype 'a result = Result of 'a | Error of string list;

datatype 'a semilattice_set = Abs_semilattice_set of ('a -> 'a -> 'a);

datatype predicate_decl = PredDecl of predicate * typea list;

datatype function_decl = FuncDecl of func * typea list;

datatype 'a ast_domain =
  Domain of
    (string * string) list * predicate_decl list * function_decl list *
      (object * typea) list * 'a list;

datatype 'a len_list = LL of nat * 'a list;

datatype 'a snap_action = AtStart of 'a | AtEnd of 'a;

datatype 'a ast_problem =
  Problem of
    'a ast_domain * (object * typea) list * object atom formula list *
      object atom formula;

datatype ('a, 'b) hashmap =
  HashMap of (('a * 'b) list) FArray.IsabelleMapping.ArrayType * nat;

datatype ground_action =
  GroundAction of object atom formula * object ast_effect;

datatype 'a label = Del | Internal of 'a | Bin of 'a | Broad of 'a;

datatype message = ExploredState;

datatype continuous_effect_op = ContinuousIncrease | ContinuousDecrease;

datatype 'a ast_continuous_effect =
  ContinuousEffect of
    continuous_effect_op * 'a primitive_numeric_expression *
      'a numeric_expression;

datatype ast_cont_change_action_body =
  ContChangeActionBody of
    (temporal_annotation * term duration_constraint) list *
      (temporal_annotation * term atom formula) list *
      (temporal_annotation * term ast_effect) list *
      term ast_continuous_effect list;

datatype ast_cont_action_schema =
  SimpleActionSchema of ast_action_head * ast_simple_action_body |
  ContChangeActionSchema of ast_action_head * ast_cont_change_action_body;

datatype ('a, 'b, 'c, 'd) gen_g_impl_ext = Gen_g_impl_ext of 'a * 'b * 'c * 'd;

datatype resulta = Renaming_Failed | Preconds_Unsat | Sat | Unsat;

datatype ('a, 'b, 'c, 'd) sexp = Truea | Notb of ('a, 'b, 'c, 'd) sexp |
  Andb of ('a, 'b, 'c, 'd) sexp * ('a, 'b, 'c, 'd) sexp |
  Orb of ('a, 'b, 'c, 'd) sexp * ('a, 'b, 'c, 'd) sexp |
  Implya of ('a, 'b, 'c, 'd) sexp * ('a, 'b, 'c, 'd) sexp | Eqb of 'c * 'd |
  Leb of 'c * 'd | Ltc of 'c * 'd | Gea of 'c * 'd | Gtb of 'c * 'd |
  Loc of 'a * 'b;

datatype mode = Impl1 | Impl2 | Impl3 | Buechi | Debug;

datatype ('a, 'b, 'c, 'd) formulaa = EX of ('a, 'b, 'c, 'd) sexp |
  EG of ('a, 'b, 'c, 'd) sexp | AX of ('a, 'b, 'c, 'd) sexp |
  AG of ('a, 'b, 'c, 'd) sexp |
  Leadsto of ('a, 'b, 'c, 'd) sexp * ('a, 'b, 'c, 'd) sexp;

datatype 'a state_space =
  Reachable_Set of (('a list * inta list) * (inta dBMEntry list) list) list |
  Buechi_Set of (('a list * inta list) * (inta dBMEntry list * nat) list) list;

fun nth (x :: xs) n =
  (if equal_nata n zero_nata then x else nth xs (minus_nata n one_nata));

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun upt i j = (if less_nat i j then i :: upt (suc i) j else []);

fun zip [] ys = []
  | zip xs [] = []
  | zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys;

fun rBT_Impl_rbt_all p Empty = true
  | rBT_Impl_rbt_all p (Branch (c, l, k, v, r)) =
    p k v andalso (rBT_Impl_rbt_all p l andalso rBT_Impl_rbt_all p r);

fun all A_ xb xc = rBT_Impl_rbt_all xb (impl_ofa A_ xc);

fun ball (A1_, A2_) (RBT_set rbt) p =
  (case ccompare A2_
    of NONE =>
      (raise Fail "Ball RBT_set: ccompare = None")
        (fn _ => ball (A1_, A2_) (RBT_set rbt) p)
    | SOME _ => all A2_ (fn k => fn _ => p k) rbt)
  | ball (A1_, A2_) (DList_set dxs) p =
    (case ceq A1_
      of NONE =>
        (raise Fail "Ball DList_set: ceq = None")
          (fn _ => ball (A1_, A2_) (DList_set dxs) p)
      | SOME _ => dlist_all A1_ p dxs)
  | ball (A1_, A2_) (Set_Monad xs) p = list_all p xs;

fun len A_ a =
  (fn f_ => fn () => f_ (((fn () => Int.fromInt (Array.length a))) ()) ())
    (fn i => (fn () => (nat_of_integer i)));

fun new A_ =
  (fn a => fn b => (fn () => Array.array (Int.toInt a, b))) o integer_of_nat;

fun ntha A_ a n = (fn () => Array.sub (a, Int.toInt (integer_of_nat n)));

fun upd A_ i x a =
  (fn f_ => fn () => f_
    (((fn () => Array.update (a, Int.toInt (integer_of_nat i), x))) ()) ())
    (fn _ => (fn () => a));

fun drop n [] = []
  | drop n (x :: xs) =
    (if equal_nata n zero_nata then x :: xs
      else drop (minus_nata n one_nata) xs);

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun take n [] = []
  | take n (x :: xs) =
    (if equal_nata n zero_nata then []
      else x :: take (minus_nata n one_nata) xs);

fun divide_int k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

fun gcd_integer k l =
  abs (if l = (0 : Int.int) then k
        else gcd_integer l (modulo_integer (abs k) (abs l)));

fun gcd_int (Int_of_integer x) (Int_of_integer y) =
  Int_of_integer (gcd_integer x y);

fun normalize p =
  (if less_int zero_inta (snd p)
    then let
           val a = gcd_int (fst p) (snd p);
         in
           (divide_int (fst p) a, divide_int (snd p) a)
         end
    else (if equal_inta (snd p) zero_inta then (zero_inta, one_inta)
           else let
                  val a = uminus_inta (gcd_int (fst p) (snd p));
                in
                  (divide_int (fst p) a, divide_int (snd p) a)
                end));

fun fract a b = Frct (normalize (a, b));

fun foldb A_ x xc = folda (fn a => fn _ => x a) (impl_ofa A_ xc);

fun fun_upda equal f aa b a = (if equal aa a then b else f a);

fun balance_right a k x (Branch (R, b, s, y, c)) =
  Branch (R, a, k, x, Branch (B, b, s, y, c))
  | balance_right (Branch (B, a, k, x, b)) s y Empty =
    balance (Branch (R, a, k, x, b)) s y Empty
  | balance_right (Branch (B, a, k, x, b)) s y (Branch (B, va, vb, vc, vd)) =
    balance (Branch (R, a, k, x, b)) s y (Branch (B, va, vb, vc, vd))
  | balance_right (Branch (R, a, k, x, Branch (B, b, s, y, c))) t z Empty =
    Branch (R, balance (paint R a) k x b, s, y, Branch (B, c, t, z, Empty))
  | balance_right (Branch (R, a, k, x, Branch (B, b, s, y, c))) t z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, balance (paint R a) k x b, s, y,
        Branch (B, c, t, z, Branch (B, va, vb, vc, vd)))
  | balance_right Empty k x Empty = Empty
  | balance_right (Branch (R, va, vb, vc, Empty)) k x Empty = Empty
  | balance_right (Branch (R, va, vb, vc, Branch (R, ve, vf, vg, vh))) k x Empty
    = Empty
  | balance_right Empty k x (Branch (B, va, vb, vc, vd)) = Empty
  | balance_right (Branch (R, ve, vf, vg, Empty)) k x
    (Branch (B, va, vb, vc, vd)) = Empty
  | balance_right (Branch (R, ve, vf, vg, Branch (R, vi, vj, vk, vl))) k x
    (Branch (B, va, vb, vc, vd)) = Empty;

fun balance_left (Branch (R, a, k, x, b)) s y c =
  Branch (R, Branch (B, a, k, x, b), s, y, c)
  | balance_left Empty k x (Branch (B, a, s, y, b)) =
    balance Empty k x (Branch (R, a, s, y, b))
  | balance_left (Branch (B, va, vb, vc, vd)) k x (Branch (B, a, s, y, b)) =
    balance (Branch (B, va, vb, vc, vd)) k x (Branch (R, a, s, y, b))
  | balance_left Empty k x (Branch (R, Branch (B, a, s, y, b), t, z, c)) =
    Branch (R, Branch (B, Empty, k, x, a), s, y, balance b t z (paint R c))
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Branch (B, a, s, y, b), t, z, c)) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), k, x, a), s, y,
        balance b t z (paint R c))
  | balance_left Empty k x Empty = Empty
  | balance_left Empty k x (Branch (R, Empty, vb, vc, vd)) = Empty
  | balance_left Empty k x (Branch (R, Branch (R, ve, vf, vg, vh), vb, vc, vd))
    = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x Empty = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Empty, vf, vg, vh)) = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Branch (R, vi, vj, vk, vl), vf, vg, vh)) = Empty;

fun combine Empty x = x
  | combine (Branch (v, va, vb, vc, vd)) Empty = Branch (v, va, vb, vc, vd)
  | combine (Branch (R, a, k, x, b)) (Branch (R, c, s, y, d)) =
    (case combine b c
      of Empty => Branch (R, a, k, x, Branch (R, Empty, s, y, d))
      | Branch (R, b2, t, z, c2) =>
        Branch (R, Branch (R, a, k, x, b2), t, z, Branch (R, c2, s, y, d))
      | Branch (B, b2, t, z, c2) =>
        Branch (R, a, k, x, Branch (R, Branch (B, b2, t, z, c2), s, y, d)))
  | combine (Branch (B, a, k, x, b)) (Branch (B, c, s, y, d)) =
    (case combine b c
      of Empty => balance_left a k x (Branch (B, Empty, s, y, d))
      | Branch (R, b2, t, z, c2) =>
        Branch (R, Branch (B, a, k, x, b2), t, z, Branch (B, c2, s, y, d))
      | Branch (B, b2, t, z, c2) =>
        balance_left a k x (Branch (B, Branch (B, b2, t, z, c2), s, y, d)))
  | combine (Branch (B, va, vb, vc, vd)) (Branch (R, b, k, x, c)) =
    Branch (R, combine (Branch (B, va, vb, vc, vd)) b, k, x, c)
  | combine (Branch (R, a, k, x, b)) (Branch (B, va, vb, vc, vd)) =
    Branch (R, a, k, x, combine b (Branch (B, va, vb, vc, vd)));

fun rbt_comp_del c x Empty = Empty
  | rbt_comp_del c x (Branch (uu, a, y, s, b)) =
    (case c x y of Eq => combine a b | Lta => rbt_comp_del_from_left c x a y s b
      | Gt => rbt_comp_del_from_right c x a y s b)
and rbt_comp_del_from_left c x (Branch (B, lt, z, v, rt)) y s b =
  balance_left (rbt_comp_del c x (Branch (B, lt, z, v, rt))) y s b
  | rbt_comp_del_from_left c x Empty y s b =
    Branch (R, rbt_comp_del c x Empty, y, s, b)
  | rbt_comp_del_from_left c x (Branch (R, va, vb, vc, vd)) y s b =
    Branch (R, rbt_comp_del c x (Branch (R, va, vb, vc, vd)), y, s, b)
and rbt_comp_del_from_right c x a y s (Branch (B, lt, z, v, rt)) =
  balance_right a y s (rbt_comp_del c x (Branch (B, lt, z, v, rt)))
  | rbt_comp_del_from_right c x a y s Empty =
    Branch (R, a, y, s, rbt_comp_del c x Empty)
  | rbt_comp_del_from_right c x a y s (Branch (R, va, vb, vc, vd)) =
    Branch (R, a, y, s, rbt_comp_del c x (Branch (R, va, vb, vc, vd)));

fun rbt_comp_delete c k t = paint B (rbt_comp_del c k t);

fun delete A_ xb xc =
  Mapping_RBTa (rbt_comp_delete (the (ccompare A_)) xb (impl_ofa A_ xc));

fun list_remove1 equal x [] = []
  | list_remove1 equal x (y :: xs) =
    (if equal x y then xs else y :: list_remove1 equal x xs);

fun removea A_ xb xc =
  Abs_dlist (list_remove1 (the (ceq A_)) xb (list_of_dlist A_ xc));

fun insert (A1_, A2_) xa (Complement x) = Complement (remove (A1_, A2_) xa x)
  | insert (A1_, A2_) x (RBT_set rbt) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "insert RBT_set: ccompare = None")
          (fn _ => insert (A1_, A2_) x (RBT_set rbt))
      | SOME _ => RBT_set (insertb A2_ x () rbt))
  | insert (A1_, A2_) x (DList_set dxs) =
    (case ceq A1_
      of NONE =>
        (raise Fail "insert DList_set: ceq = None")
          (fn _ => insert (A1_, A2_) x (DList_set dxs))
      | SOME _ => DList_set (inserta A1_ x dxs))
  | insert (A1_, A2_) x (Set_Monad xs) = Set_Monad (x :: xs)
  | insert (A1_, A2_) x (Collect_set a) =
    (case ceq A1_
      of NONE =>
        (raise Fail "insert Collect_set: ceq = None")
          (fn _ => insert (A1_, A2_) x (Collect_set a))
      | SOME eq => Collect_set (fun_upda eq a x true))
and remove (A1_, A2_) x (Complement a) = Complement (insert (A1_, A2_) x a)
  | remove (A1_, A2_) x (RBT_set rbt) =
    (case ccompare A2_
      of NONE =>
        (raise Fail "remove RBT_set: ccompare = None")
          (fn _ => remove (A1_, A2_) x (RBT_set rbt))
      | SOME _ => RBT_set (delete A2_ x rbt))
  | remove (A1_, A2_) x (DList_set dxs) =
    (case ceq A1_
      of NONE =>
        (raise Fail "remove DList_set: ceq = None")
          (fn _ => remove (A1_, A2_) x (DList_set dxs))
      | SOME _ => DList_set (removea A1_ x dxs))
  | remove (A1_, A2_) x (Collect_set a) =
    (case ceq A1_
      of NONE =>
        (raise Fail "remove Collect: ceq = None")
          (fn _ => remove (A1_, A2_) x (Collect_set a))
      | SOME eq => Collect_set (fun_upda eq a x false));

fun image (A1_, A2_) (B1_, B2_, B3_) h (RBT_set rbt) =
  (case ccompare A2_
    of NONE =>
      (raise Fail "image RBT_set: ccompare = None")
        (fn _ => image (A1_, A2_) (B1_, B2_, B3_) h (RBT_set rbt))
    | SOME _ => foldb A2_ (insert (B1_, B2_) o h) rbt (bot_set (B1_, B2_, B3_)))
  | image (A1_, A2_) (B1_, B2_, B3_) g (DList_set dxs) =
    (case ceq A1_
      of NONE =>
        (raise Fail "image DList_set: ceq = None")
          (fn _ => image (A1_, A2_) (B1_, B2_, B3_) g (DList_set dxs))
      | SOME _ =>
        foldc A1_ (insert (B1_, B2_) o g) dxs (bot_set (B1_, B2_, B3_)))
  | image (A1_, A2_) (B1_, B2_, B3_) f (Complement (Complement b)) =
    image (A1_, A2_) (B1_, B2_, B3_) f b
  | image (A1_, A2_) (B1_, B2_, B3_) f (Collect_set a) =
    (raise Fail "image Collect_set")
      (fn _ => image (A1_, A2_) (B1_, B2_, B3_) f (Collect_set a))
  | image (A1_, A2_) (B1_, B2_, B3_) f (Set_Monad xs) = Set_Monad (map f xs);

fun make A_ n f =
  (fn () => Array.tabulate (Int.toInt (integer_of_nat n),
    (f o nat_of_integer) o Int.fromInt));

fun inj_on (A1_, A2_, A3_) B_ f a =
  ball (A1_, A2_) a
    (fn x =>
      ball (A1_, A2_) a
        (fn y => (if eq B_ (f x) (f y) then eq A3_ x y else true)));

fun sub asa n =
  (Vector.sub o (fn (a, b) => (a, Int.toInt b))) (asa, integer_of_nat n);

fun map_of A_ [] k = NONE
  | map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k);

fun of_int a = Frct (a, one_inta);

fun fun_upd A_ f a b = (fn x => (if eq A_ x a then b else f x));

fun ll_fuel (LL (x1, x2)) = x1;

fun bind m f = (case m of Inl a => Inl a | Inr a => f a);

fun ensure_cparser p =
  (fn ts =>
    bind (p ts)
      (fn (x, tsa) =>
        (if less_nat (ll_fuel tsa) (ll_fuel ts) then Inr (x, tsa)
          else Inl (fn _ =>
                     shows_prec_list show_char zero_nata
                       [Chara (false, false, true, false, false, false, true,
                                false),
                         Chara (true, false, false, true, true, true, true,
                                 false),
                         Chara (false, true, true, true, false, true, true,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (true, false, true, true, false, true, true,
                                 false),
                         Chara (true, false, false, true, false, true, true,
                                 false),
                         Chara (true, true, false, false, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (false, false, false, false, true, true, true,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (false, true, false, false, true, true, true,
                                 false),
                         Chara (true, true, false, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (false, true, false, false, true, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (true, true, false, false, false, true, true,
                                 false),
                         Chara (false, false, false, true, false, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (true, true, false, false, false, true, true,
                                 false),
                         Chara (true, true, false, true, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (false, true, true, false, false, true, true,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (true, false, false, true, false, true, true,
                                 false),
                         Chara (false, false, true, true, false, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (false, false, true, false, false, true, true,
                                 false)]))));

fun sum_join (Inl x) = x
  | sum_join (Inr x) = x;

fun return x = (fn ts => Inr (x, ts));

fun ensure_parser p =
  (fn ts =>
    bind (p ts)
      (fn (x, tsa) =>
        (if less_eq_nat (ll_fuel tsa) (ll_fuel ts) then Inr (x, tsa)
          else Inl (fn _ =>
                     shows_prec_list show_char zero_nata
                       [Chara (false, false, true, false, false, false, true,
                                false),
                         Chara (true, false, false, true, true, true, true,
                                 false),
                         Chara (false, true, true, true, false, true, true,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (true, false, true, true, false, true, true,
                                 false),
                         Chara (true, false, false, true, false, true, true,
                                 false),
                         Chara (true, true, false, false, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (false, false, false, false, true, true, true,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (false, true, false, false, true, true, true,
                                 false),
                         Chara (true, true, false, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (false, true, false, false, true, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (true, true, false, false, false, true, true,
                                 false),
                         Chara (false, false, false, true, false, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (true, true, false, false, false, true, true,
                                 false),
                         Chara (true, true, false, true, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (false, true, true, false, false, true, true,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (true, false, false, true, false, true, true,
                                 false),
                         Chara (false, false, true, true, false, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (false, false, true, false, false, true, true,
                                 false)]))));

fun bindb m f =
  (fn ts => bind (ensure_parser m ts) (fn (x, a) => ensure_parser (f x) a));

fun catch_error m f = (case m of Inl a => f a | Inr a => Inr a);

fun alt p1 p2 l =
  catch_error (bind (p1 l) (fn (r, la) => Inr (Inl r, la)))
    (fn e1 =>
      catch_error (bind (p2 l) (fn (r, la) => Inr (Inr r, la)))
        (fn e2 =>
          Inl (fn _ =>
                e1 () o
                  shows_prec_list show_char zero_nata
                    [Chara (false, true, false, true, false, false, false,
                             false),
                      Chara (false, false, false, false, false, true, false,
                              false),
                      Chara (false, false, false, false, false, true, false,
                              false),
                      Chara (false, false, true, true, true, true, true, false),
                      Chara (false, false, false, false, false, true, false,
                              false)] o
                  e2 ())));

fun repeat p l =
  bindb (alt (bindb (ensure_cparser p)
               (fn a => bindb (repeat p) (fn b => return (a :: b))))
          (return []))
    (fn x => return (sum_join x)) l;

fun ll_list (LL (x1, x2)) = x2;

fun get_tokens x = (fn ll => Inr (ll_list ll, ll)) x;

fun error_aux e = (fn _ => Inl e);

fun shows_quote s =
  shows_prec_char zero_nata
    (Chara (true, true, true, false, false, true, false, false)) o
    s o
    shows_prec_char zero_nata
      (Chara (true, true, true, false, false, true, false, false));

fun err_expecting_aux A_ msg =
  bindb get_tokens
    (fn ts =>
      error_aux
        (fn _ =>
          shows_string
            [Chara (true, false, true, false, false, true, true, false),
              Chara (false, false, false, true, true, true, true, false),
              Chara (false, false, false, false, true, true, true, false),
              Chara (true, false, true, false, false, true, true, false),
              Chara (true, true, false, false, false, true, true, false),
              Chara (false, false, true, false, true, true, true, false),
              Chara (true, false, false, true, false, true, true, false),
              Chara (false, true, true, true, false, true, true, false),
              Chara (true, true, true, false, false, true, true, false),
              Chara (false, false, false, false, false, true, false, false)] o
            msg () o
            shows_string
              [Chara (false, false, true, true, false, true, false, false),
                Chara (false, false, false, false, false, true, false, false),
                Chara (false, true, false, false, false, true, true, false),
                Chara (true, false, true, false, true, true, true, false),
                Chara (false, false, true, false, true, true, true, false),
                Chara (false, false, false, false, false, true, false, false),
                Chara (false, true, true, false, false, true, true, false),
                Chara (true, true, true, true, false, true, true, false),
                Chara (true, false, true, false, true, true, true, false),
                Chara (false, true, true, true, false, true, true, false),
                Chara (false, false, true, false, false, true, true, false),
                Chara (false, true, false, true, true, true, false, false),
                Chara (false, false, false, false, false, true, false, false)] o
            shows_quote
              (shows_prec_list A_ zero_nata
                (take (nat_of_integer (100 : Int.int)) ts))));

fun get ll =
  let
    val LL (nat, lista) = ll;
  in
    (if equal_nata nat zero_nata
      then Inl (fn _ =>
                 shows_string
                   [Chara (true, false, true, false, false, false, true, false),
                     Chara (false, false, false, true, true, true, true, false),
                     Chara (false, false, false, false, true, true, true,
                             false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (true, true, false, false, false, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (true, true, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, false, true, true, false, true, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, false, false, false, true, true, true,
                             false),
                     Chara (true, false, true, false, true, true, true, false),
                     Chara (false, false, true, false, true, true, true,
                             false)])
      else (case lista
             of [] =>
               Inl (fn _ =>
                     shows_string
                       [Chara (true, false, true, false, false, false, true,
                                false),
                         Chara (false, false, false, true, true, true, true,
                                 false),
                         Chara (false, false, false, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (true, true, false, false, false, true, true,
                                 false),
                         Chara (false, false, true, false, true, true, true,
                                 false),
                         Chara (true, false, false, true, false, true, true,
                                 false),
                         Chara (false, true, true, true, false, true, true,
                                 false),
                         Chara (true, true, true, false, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (true, false, true, true, false, true, true,
                                 false),
                         Chara (true, true, true, true, false, true, true,
                                 false),
                         Chara (false, true, false, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (true, false, false, true, false, true, true,
                                 false),
                         Chara (false, true, true, true, false, true, true,
                                 false),
                         Chara (false, false, false, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, true, true, true,
                                 false),
                         Chara (false, false, true, false, true, true, true,
                                 false)])
             | x :: xs => Inr (x, LL (minus_nata nat one_nata, xs))))
  end;

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun any (A1_, A2_) ts =
  bindb get
    (fn t =>
      (if membera A1_ ts t then return t
        else err_expecting_aux A2_
               (fn _ =>
                 shows_string
                   [Chara (true, true, true, true, false, false, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, true, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false)] o
                   shows_prec_list A2_ zero_nata ts)));

fun lx_ws x =
  repeat
    (any (equal_char, show_char)
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, false, true, false, false, false, false),
        Chara (true, false, false, true, false, false, false, false),
        Chara (true, false, true, true, false, false, false, false)])
    x;

fun update A_ k v [] = [(k, v)]
  | update A_ k v (p :: ps) =
    (if eq A_ (fst p) k then (k, v) :: ps else p :: update A_ k v ps);

fun fold_map f [] = (fn () => [])
  | fold_map f (x :: xs) =
    (fn f_ => fn () => f_ ((f x) ()) ())
      (fn y =>
        (fn f_ => fn () => f_ ((fold_map f xs) ()) ())
          (fn ys => (fn () => (y :: ys))));

fun freeze A_ a =
  (fn f_ => fn () => f_ ((len A_ a) ()) ())
    (fn n => fold_map (ntha A_ a) (upt zero_nata n));

val empty : ('a, 'b) alist = Alist [];

fun hda (x21 :: x22) = x21;

fun hd A_ xa = hda (list_of_dlist A_ xa);

fun tla [] = []
  | tla (x21 :: x22) = x22;

fun tl A_ xa = Abs_dlist (tla (list_of_dlist A_ xa));

fun foldli [] c f sigma = sigma
  | foldli (x :: xs) c f sigma =
    (if c sigma then foldli xs c f (f x sigma) else sigma);

fun exactly (A1_, A2_) ts =
  bindb (alt (foldr
               (fn t => fn p =>
                 bindb get
                   (fn x =>
                     (if eq A1_ x t then bindb p (fn xa => return (x :: xa))
                       else error_aux (fn _ => id))))
               ts (return []))
          (err_expecting_aux A2_
            (fn _ =>
              shows_string
                [Chara (true, false, true, false, false, false, true, false),
                  Chara (false, false, false, true, true, true, true, false),
                  Chara (true, false, false, false, false, true, true, false),
                  Chara (true, true, false, false, false, true, true, false),
                  Chara (false, false, true, false, true, true, true, false),
                  Chara (false, false, true, true, false, true, true, false),
                  Chara (true, false, false, true, true, true, true, false),
                  Chara (false, false, false, false, false, true, false,
                          false)] o
                shows_prec_list A2_ zero_nata ts)))
    (fn x => return (sum_join x));

fun of_bool A_ false = zero (zero_zero_neq_one A_)
  | of_bool A_ true = one (one_zero_neq_one A_);

fun integer_of_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
  ((((((of_bool zero_neq_one_integer b7 * (2 : Int.int) +
         of_bool zero_neq_one_integer b6) *
         (2 : Int.int) +
        of_bool zero_neq_one_integer b5) *
        (2 : Int.int) +
       of_bool zero_neq_one_integer b4) *
       (2 : Int.int) +
      of_bool zero_neq_one_integer b3) *
      (2 : Int.int) +
     of_bool zero_neq_one_integer b2) *
     (2 : Int.int) +
    of_bool zero_neq_one_integer b1) *
    (2 : Int.int) +
    of_bool zero_neq_one_integer b0;

fun nat_of_char c = Nat (integer_of_char c);

fun range (A1_, A2_) a b =
  bindb get
    (fn x =>
      (if less_eq ((ord_preorder o preorder_order o order_linorder) A1_) a
            x andalso
            less_eq ((ord_preorder o preorder_order o order_linorder) A1_) x b
        then return x
        else err_expecting_aux A2_
               (fn _ =>
                 shows_string
                   [Chara (false, false, true, false, true, false, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (true, true, false, true, false, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (true, true, true, false, false, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false)] o
                   shows_prec A2_ zero_nata a o
                   shows_string
                     [Chara (false, false, false, false, false, true, false,
                              false),
                       Chara (true, false, true, true, false, true, false,
                               false),
                       Chara (false, false, false, false, false, true, false,
                               false)] o
                   shows_prec A2_ zero_nata b)));

fun lx_digit x =
  range (linorder_char, show_char)
    (Chara (false, false, false, false, true, true, false, false))
    (Chara (true, false, false, true, true, true, false, false)) x;

fun lx_nat_aux acc l =
  bindb (alt (bindb lx_digit
               (fn x =>
                 lx_nat_aux
                   (plus_nata
                     (times_nata (nat_of_integer (10 : Int.int)) acc)
                     (minus_nata (nat_of_char x)
                       (nat_of_char
                         (Chara
                           (false, false, false, false, true, true, false,
                             false)))))))
          (return acc))
    (fn x => return (sum_join x)) l;

fun lx_nat x =
  bindb lx_digit
    (fn xa =>
      lx_nat_aux
        (minus_nata (nat_of_char xa)
          (nat_of_char
            (Chara (false, false, false, false, true, true, false, false)))))
    x;

fun lx_int x =
  bindb (alt (bindb
               (exactly (equal_char, show_char)
                 [Chara (true, false, true, true, false, true, false, false)])
               (fn _ =>
                 bindb lx_nat
                   (fn xa => return ((uminus_inta o int_of_nat) xa))))
          (bindb lx_nat (fn xa => return (int_of_nat xa))))
    (fn xa => return (sum_join xa)) x;

fun gen_token ws p = bindb ws (fn _ => p);

fun tk_div x =
  gen_token lx_ws
    (exactly (equal_char, show_char)
      [Chara (true, true, true, true, false, true, false, false)])
    x;

fun extract p [] = NONE
  | extract p (x :: xs) =
    (if p x then SOME ([], (x, xs))
      else (case extract p xs of NONE => NONE
             | SOME (ys, (y, zs)) => SOME (x :: ys, (y, zs))));

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if membera A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun uncurry f = (fn (a, b) => f a b);

fun is_emptya A_ xa =
  (case impl_ofa A_ xa of Empty => true | Branch (_, _, _, _, _) => false);

fun exhaustive_above_fusion proper_interval g y s =
  (if has_next g s
    then let
           val (x, sa) = next g s;
         in
           not (proper_interval (SOME y) (SOME x)) andalso
             exhaustive_above_fusion proper_interval g x sa
         end
    else not (proper_interval (SOME y) NONE));

fun exhaustive_fusion proper_interval g s =
  has_next g s andalso
    let
      val (x, sa) = next g s;
    in
      not (proper_interval NONE (SOME x)) andalso
        exhaustive_above_fusion proper_interval g x sa
    end;

fun list_remdups equal [] = []
  | list_remdups equal (x :: xs) =
    (if list_member equal xs x then list_remdups equal xs
      else x :: list_remdups equal xs);

fun length A_ xa = size_list (list_of_dlist A_ xa);

fun card (A1_, A2_, A3_) (Complement a) =
  let
    val aa = card (A1_, A2_, A3_) a;
    val s = of_phantom (card_UNIV A1_);
  in
    (if less_nat zero_nata s then minus_nata s aa
      else (if finite (finite_UNIV_card_UNIV A1_, A2_, A3_) a then zero_nata
             else (raise Fail "card Complement: infinite")
                    (fn _ => card (A1_, A2_, A3_) (Complement a))))
  end
  | card (A1_, A2_, A3_) (Set_Monad xs) =
    (case ceq A2_
      of NONE =>
        (raise Fail "card Set_Monad: ceq = None")
          (fn _ => card (A1_, A2_, A3_) (Set_Monad xs))
      | SOME eq => size_list (list_remdups eq xs))
  | card (A1_, A2_, A3_) (RBT_set rbt) =
    (case ccompare A3_
      of NONE =>
        (raise Fail "card RBT_set: ccompare = None")
          (fn _ => card (A1_, A2_, A3_) (RBT_set rbt))
      | SOME _ => size_list (keysa A3_ rbt))
  | card (A1_, A2_, A3_) (DList_set dxs) =
    (case ceq A2_
      of NONE =>
        (raise Fail "card DList_set: ceq = None")
          (fn _ => card (A1_, A2_, A3_) (DList_set dxs))
      | SOME _ => length A2_ dxs);

fun is_UNIV (A1_, A2_, A3_) (RBT_set rbt) =
  (case ccompare (ccompare_cproper_interval A3_)
    of NONE =>
      (raise Fail "is_UNIV RBT_set: ccompare = None")
        (fn _ => is_UNIV (A1_, A2_, A3_) (RBT_set rbt))
    | SOME _ =>
      of_phantom (finite_UNIV (finite_UNIV_card_UNIV A1_)) andalso
        exhaustive_fusion (cproper_interval A3_) rbt_keys_generator
          (init (ccompare_cproper_interval A3_) rbt))
  | is_UNIV (A1_, A2_, A3_) a =
    let
      val aa = of_phantom (card_UNIV A1_);
      val b = card (A1_, A2_, ccompare_cproper_interval A3_) a;
    in
      (if less_nat zero_nata aa then equal_nata aa b
        else (if less_nat zero_nata b then false
               else (raise Fail "is_UNIV called on infinite type and set")
                      (fn _ => is_UNIV (A1_, A2_, A3_) a)))
    end;

fun nulla A_ xa = null (list_of_dlist A_ xa);

fun is_empty (A1_, A2_, A3_) (Complement a) = is_UNIV (A1_, A2_, A3_) a
  | is_empty (A1_, A2_, A3_) (RBT_set rbt) =
    (case ccompare (ccompare_cproper_interval A3_)
      of NONE =>
        (raise Fail "is_empty RBT_set: ccompare = None")
          (fn _ => is_empty (A1_, A2_, A3_) (RBT_set rbt))
      | SOME _ => is_emptya (ccompare_cproper_interval A3_) rbt)
  | is_empty (A1_, A2_, A3_) (DList_set dxs) =
    (case ceq A2_
      of NONE =>
        (raise Fail "is_empty DList_set: ceq = None")
          (fn _ => is_empty (A1_, A2_, A3_) (DList_set dxs))
      | SOME _ => nulla A2_ dxs)
  | is_empty (A1_, A2_, A3_) (Set_Monad xs) = null xs;

fun impl_of (Alist x) = x;

fun lookup A_ xa = map_of A_ (impl_of xa);

fun updatea A_ xc xd xe = Alist (update A_ xc xd (impl_of xe));

fun tk_plus x =
  gen_token lx_ws
    (exactly (equal_char, show_char)
      [Chara (true, true, false, true, false, true, false, false)])
    x;

fun set_aux (A1_, A2_) Set_Monada = Set_Monad
  | set_aux (A1_, A2_) Set_Choose =
    (case ccompare A2_
      of NONE =>
        (case ceq A1_ of NONE => Set_Monad
          | SOME _ =>
            foldl (fn s => fn x => insert (A1_, A2_) x s)
              (DList_set (emptyb A1_)))
      | SOME _ =>
        foldl (fn s => fn x => insert (A1_, A2_) x s) (RBT_set (emptyc A2_)))
  | set_aux (A1_, A2_) impl =
    foldl (fn s => fn x => insert (A1_, A2_) x s) (set_empty (A1_, A2_) impl);

fun set (A1_, A2_, A3_) xs = set_aux (A1_, A2_) (of_phantom (set_impl A3_)) xs;

fun mapping_empty_choose A_ =
  (case ccompare A_ of NONE => Assoc_List_Mapping empty
    | SOME _ => RBT_Mapping (emptyc A_));

fun mapping_empty A_ Mapping_RBT = RBT_Mapping (emptyc A_)
  | mapping_empty A_ Mapping_Assoc_List = Assoc_List_Mapping empty
  | mapping_empty A_ Mapping_Mapping = Mapping (fn _ => NONE)
  | mapping_empty A_ Mapping_Choose = mapping_empty_choose A_;

fun emptya (A1_, A2_) = mapping_empty A1_ (of_phantom (mapping_impl A2_));

fun bigOr [] = Bot
  | bigOr (f :: fs) = Or (f, bigOr fs);

fun tk_minus x =
  gen_token lx_ws
    (exactly (equal_char, show_char)
      [Chara (true, false, true, true, false, true, false, false)])
    x;

fun tk_times x =
  gen_token lx_ws
    (exactly (equal_char, show_char)
      [Chara (false, true, false, true, false, true, false, false)])
    x;

fun replicate n x =
  (if equal_nata n zero_nata then []
    else x :: replicate (minus_nata n one_nata) x);

fun lookupa (A1_, A2_) (RBT_Mapping t) = lookupb A1_ t
  | lookupa (A1_, A2_) (Assoc_List_Mapping al) = lookup A2_ al;

fun updateb (A1_, A2_) k v (RBT_Mapping t) =
  (case ccompare A1_
    of NONE =>
      (raise Fail "update RBT_Mapping: ccompare = None")
        (fn _ => updateb (A1_, A2_) k v (RBT_Mapping t))
    | SOME _ => RBT_Mapping (insertb A1_ k v t))
  | updateb (A1_, A2_) k v (Assoc_List_Mapping al) =
    Assoc_List_Mapping (updatea A2_ k v al)
  | updateb (A1_, A2_) k v (Mapping m) = Mapping (fun_upd A2_ m k (SOME v));

fun rBT_Impl_fold1 f Empty = (raise Fail "undefined")
  | rBT_Impl_fold1 f (Branch (c, Empty, k, v, r)) =
    folda (fn ka => fn _ => f ka) r k
  | rBT_Impl_fold1 f (Branch (ca, Branch (c, l, ka, va, ra), k, v, r)) =
    folda (fn kb => fn _ => f kb) r
      (f k (rBT_Impl_fold1 f (Branch (c, l, ka, va, ra))));

fun fold1 A_ x xc = rBT_Impl_fold1 x (impl_ofa A_ xc);

fun filter_comp_minus c t1 t2 =
  filter (fn (k, _) => is_none (rbt_comp_lookup c t2 k)) (entries t1);

fun small_rbt t = less_nat (bheight t) (nat_of_integer (4 : Int.int));

fun comp_minus c t1 t2 =
  (if small_rbt t2 then folda (fn k => fn _ => rbt_comp_delete c k) t2 t1
    else (if small_rbt t1 then rbtreeify (filter_comp_minus c t1 t2)
           else (case t2 of Empty => t1
                  | Branch (_, l2, a, _, r2) =>
                    let
                      val (l1, (_, r1)) = rbt_split_comp c t1 a;
                    in
                      rbt_join2 (comp_minus c l1 l2) (comp_minus c r1 r2)
                    end)));

fun rbt_comp_minus c t1 t2 = paint B (comp_minus c t1 t2);

fun minus A_ xb xc =
  Mapping_RBTa
    (rbt_comp_minus (the (ccompare A_)) (impl_ofa A_ xb) (impl_ofa A_ xc));

fun implode cs = Str_Literal.literal_of_asciis (map integer_of_char cs);

fun v_dbm (A1_, A2_, A3_) B_ n =
  (fn (i, j) =>
    (if eq A2_ i j orelse
          (eq A2_ i (zero A1_) andalso less A3_ (zero A1_) j orelse
            (less A3_ n i orelse less A3_ n j))
      then zero_DBMEntrya B_ else INF));

fun bigAnd [] = Not Bot
  | bigAnd (f :: fs) = And (f, bigAnd fs);

fun tk_lparen x =
  gen_token lx_ws
    (exactly (equal_char, show_char)
      [Chara (false, false, false, true, false, true, false, false)])
    x;

fun tk_rparen x =
  gen_token lx_ws
    (exactly (equal_char, show_char)
      [Chara (true, false, false, true, false, true, false, false)])
    x;

fun default (A1_, A2_) k v m =
  (if not (is_none (lookupa (A1_, A2_) m k)) then m
    else updateb (A1_, A2_) k v m);

fun cODE_ABORT _ = raise Fail "Misc.CODE_ABORT";

fun gen_pick it s =
  the (it s (fn a => (case a of NONE => true | SOME _ => false))
         (fn x => fn _ => SOME x)
        NONE);

fun bracket_close x =
  bindb lx_ws
    (fn _ =>
      exactly (equal_char, show_char)
        [Chara (true, false, true, true, true, false, true, false)])
    x;

fun bracket_open x =
  bindb lx_ws
    (fn _ =>
      exactly (equal_char, show_char)
        [Chara (true, true, false, true, true, false, true, false)])
    x;

fun chainL1 a f =
  bindb a
    (fn x =>
      bindb (repeat
              (bindb f (fn aa => bindb a (fn b => return (fn ab => aa ab b)))))
        (fn xs => return (foldl (fn aa => fn fa => fa aa) x xs)));

fun comma x =
  bindb lx_ws
    (fn _ =>
      exactly (equal_char, show_char)
        [Chara (false, false, true, true, false, true, false, false)])
    x;

fun parse_list a =
  chainL1 (bindb a (fn x => return [x]))
    (bindb comma (fn _ => return (fn aa => fn b => aa @ b)));

fun brace_close x =
  bindb lx_ws
    (fn _ =>
      exactly (equal_char, show_char)
        [Chara (true, false, true, true, true, true, true, false)])
    x;

fun json_character x =
  bindb get
    (fn xa =>
      (if not (membera equal_char
                [Chara (false, true, false, false, false, true, false, false),
                  Chara (false, true, false, false, true, false, false, true),
                  Chara (false, true, false, true, false, false, false, false)]
                xa)
        then return xa
        else err_expecting_aux show_char
               (fn _ =>
                 shows_string
                   [Chara (false, true, false, true, false, false, true, false),
                     Chara (true, true, false, false, true, false, true, false),
                     Chara (true, true, true, true, false, false, true, false),
                     Chara (false, true, true, true, false, false, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, true, false, false, true, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (true, true, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, true, false, false, false, true, true, false),
                     Chara (false, false, false, true, false, true, true,
                             false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (true, true, false, false, false, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, true, false, false, true, true, true,
                             false)])))
    x;

fun identifier x =
  bindb (exactly (equal_char, show_char)
          [Chara (false, true, false, false, false, true, false, false)])
    (fn _ =>
      bindb json_character
        (fn xa =>
          bindb (repeat json_character)
            (fn xaa =>
              bindb (exactly (equal_char, show_char)
                      [Chara (false, true, false, false, false, true, false,
                               false)])
                (fn _ => return (xa :: xaa)))))
    x;

fun brace_open x =
  bindb lx_ws
    (fn _ =>
      exactly (equal_char, show_char)
        [Chara (true, true, false, true, true, true, true, false)])
    x;

fun colon x =
  bindb lx_ws
    (fn _ =>
      exactly (equal_char, show_char)
        [Chara (false, true, false, true, true, true, false, false)])
    x;

fun json_string x =
  bindb (exactly (equal_char, show_char)
          [Chara (false, true, false, false, false, true, false, false)])
    (fn _ =>
      bindb (repeat json_character)
        (fn a =>
          bindb (exactly (equal_char, show_char)
                  [Chara (false, true, false, false, false, true, false,
                           false)])
            (fn _ => return a)))
    x;

fun nats_to_nat x [] = x
  | nats_to_nat x (n :: ns) =
    nats_to_nat (plus_nata (times_nata (nat_of_integer (10 : Int.int)) x) n)
      ns;

fun lx_rat x =
  bindb lx_int
    (fn xa =>
      bindb (exactly (equal_char, show_char)
              [Chara (false, true, true, true, false, true, false, false)])
        (fn _ =>
          bindb lx_digit
            (fn xaa =>
              bindb (repeat
                      (bindb lx_digit
                        (fn xb =>
                          return
                            (minus_nata (nat_of_char xb)
                              (nat_of_char
                                (Chara
                                  (false, false, false, false, true, true,
                                    false, false)))))))
                (fn xb =>
                  return
                    (if less_eq_int zero_inta xa
                      then Rata (true, xa,
                                  (int_of_nat o nats_to_nat zero_nata)
                                    (minus_nata (nat_of_char xaa)
                                       (nat_of_char
 (Chara (false, false, false, false, true, true, false, false))) ::
                                      xb))
                      else Rata (false, xa,
                                  (int_of_nat o nats_to_nat zero_nata)
                                    (minus_nata (nat_of_char xaa)
                                       (nat_of_char
 (Chara (false, false, false, false, true, true, false, false))) ::
                                      xb)))))))
    x;

fun atom x =
  bindb lx_ws
    (fn _ =>
      bindb (alt (bindb json_string (fn xa => return (Stringa xa)))
              (bindb
                (alt (bindb lx_rat (fn xa => return (Rat xa)))
                  (bindb
                    (alt (bindb lx_nat (fn xa => return (Nata xa)))
                      (bindb
                        (alt (bindb lx_int (fn xa => return (Int xa)))
                          (bindb
                            (alt (bindb
                                   (exactly (equal_char, show_char)
                                     [Chara
(false, false, true, false, true, true, true, false),
                                       Chara
 (false, true, false, false, true, true, true, false),
                                       Chara
 (true, false, true, false, true, true, true, false),
                                       Chara
 (true, false, true, false, false, true, true, false)])
                                   (fn _ => return (Boolean true)))
                              (bindb
                                (alt (bindb
                                       (exactly (equal_char, show_char)
 [Chara (false, true, true, false, false, true, true, false),
   Chara (true, false, false, false, false, true, true, false),
   Chara (false, false, true, true, false, true, true, false),
   Chara (true, true, false, false, true, true, true, false),
   Chara (true, false, true, false, false, true, true, false)])
                                       (fn _ => return (Boolean false)))
                                  (bindb
                                    (exactly (equal_char, show_char)
                                      [Chara
 (false, true, true, true, false, true, true, false),
Chara (true, false, true, false, true, true, true, false),
Chara (false, false, true, true, false, true, true, false),
Chara (false, false, true, true, false, true, true, false)])
                                    (fn _ => return Null)))
                                (fn xa => return (sum_join xa))))
                            (fn xa => return (sum_join xa))))
                        (fn xa => return (sum_join xa))))
                    (fn xa => return (sum_join xa))))
                (fn xa => return (sum_join xa))))
        (fn xa => return (sum_join xa)))
    x;

fun seq l =
  bindb bracket_open
    (fn _ =>
      bindb (alt (parse_list json) (bindb lx_ws (fn _ => return [])))
        (fn x => bindb bracket_close (fn _ => return (Arraya (sum_join x)))))
    l
and json l =
  bindb (alt atom (bindb (alt seq dict) (fn x => return (sum_join x))))
    (fn x => return (sum_join x)) l
and dict l =
  bindb brace_open
    (fn _ =>
      bindb (alt (parse_list
                   (bindb lx_ws
                     (fn _ =>
                       bindb identifier
                         (fn a =>
                           bindb colon
                             (fn _ => bindb json (fn b => return (a, b)))))))
              (bindb lx_ws (fn _ => return [])))
        (fn x => bindb brace_close (fn _ => return (Object (sum_join x)))))
    l;

fun list_update [] i y = []
  | list_update (x :: xs) i y =
    (if equal_nata i zero_nata then y :: xs
      else x :: list_update xs (minus_nata i one_nata) y);

fun find_index uu [] = zero_nata
  | find_index p (x :: xs) =
    (if p x then zero_nata else plus_nata (find_index p xs) one_nata);

fun index A_ xs = (fn a => find_index (fn x => eq A_ x a) xs);

fun of_alist (A1_, A2_, A3_) xs =
  foldr (fn (a, b) => updateb (A1_, A2_) a b) xs (emptya (A1_, A3_));

fun max_sls A_ =
  Abs_semilattice_set
    (max ((ord_preorder o preorder_order o order_linorder) A_));

fun sup_cfi A_ =
  Abs_comp_fun_idem (sup ((sup_semilattice_sup o semilattice_sup_lattice) A_));

fun check b e = (if b then Inr () else Inl e);

fun ht_new_sz (A1_, A2_) B_ n =
  let
    val l = replicate n [];
  in
    (fn f_ => fn () => f_ (((fn () => Array.fromList l)) ()) ())
      (fn a => (fn () => (HashTable (a, zero_nata))))
  end;

fun ht_new (A1_, A2_) B_ = ht_new_sz (A1_, A2_) B_ (def_hashmap_size A1_ Type);

fun nat_of_uint32 x =
  nat_of_integer (Int.fromLarge (Word32.toLargeInt x) : Int.int);

fun nat_of_hashcode x = nat_of_uint32 x;

fun bounded_hashcode_nat A_ n x =
  modulo_nat (nat_of_hashcode (hashcode A_ x)) n;

fun the_array (HashTable (a, uu)) = a;

fun ls_update A_ k v [] = ([(k, v)], false)
  | ls_update A_ k v ((l, w) :: ls) =
    (if eq A_ k l then ((k, v) :: ls, true)
      else let
             val r = ls_update A_ k v ls;
           in
             ((l, w) :: fst r, snd r)
           end);

fun the_size (HashTable (uu, n)) = n;

fun ht_upd (A1_, A2_, A3_) B_ k v ht =
  (fn f_ => fn () => f_ ((len (heap_list (heap_prod A3_ B_)) (the_array ht)) ())
    ())
    (fn m =>
      let
        val i = bounded_hashcode_nat A2_ m k;
      in
        (fn f_ => fn () => f_
          ((ntha (heap_list (heap_prod A3_ B_)) (the_array ht) i) ()) ())
          (fn l =>
            let
              val la = ls_update A1_ k v l;
            in
              (fn f_ => fn () => f_
                ((upd (heap_list (heap_prod A3_ B_)) i (fst la) (the_array ht))
                ()) ())
                (fn _ =>
                  let
                    val n = (if snd la then the_size ht else suc (the_size ht));
                  in
                    (fn () => (HashTable (the_array ht, n)))
                  end)
            end)
      end);

fun map_entry (A1_, A2_) k f m =
  (case lookupa (A1_, A2_) m k of NONE => m
    | SOME v => updateb (A1_, A2_) k (f v) m);

fun map_default b f a = (case f a of NONE => b | SOME ba => ba);

fun ht_insls (A1_, A2_, A3_) B_ [] ht = (fn () => ht)
  | ht_insls (A1_, A2_, A3_) B_ ((k, v) :: l) ht =
    (fn f_ => fn () => f_ ((ht_upd (A1_, A2_, A3_) B_ k v ht) ()) ())
      (ht_insls (A1_, A2_, A3_) B_ l);

fun ht_copy (A1_, A2_, A3_) B_ n src dst =
  (if equal_nata n zero_nata then (fn () => dst)
    else (fn f_ => fn () => f_
           ((ntha (heap_list (heap_prod A3_ B_)) (the_array src)
              (minus_nata n one_nata))
           ()) ())
           (fn l =>
             (fn f_ => fn () => f_ ((ht_insls (A1_, A2_, A3_) B_ l dst) ()) ())
               (ht_copy (A1_, A2_, A3_) B_ (minus_nata n one_nata) src)));

fun product_lists [] = [[]]
  | product_lists (xs :: xss) =
    maps (fn x => map (fn a => x :: a) (product_lists xss)) xs;

fun partition_rev p (yes, no) [] = (yes, no)
  | partition_rev p (yes, no) (x :: xs) =
    partition_rev p (if p x then (x :: yes, no) else (yes, x :: no)) xs;

fun semilattice_set_apply (Abs_semilattice_set x) = x;

fun set_fold1 (A1_, A2_, A3_) f (RBT_set rbt) =
  (case ccompare A2_
    of NONE =>
      (raise Fail "set_fold1 RBT_set: ccompare = None")
        (fn _ => set_fold1 (A1_, A2_, A3_) f (RBT_set rbt))
    | SOME _ =>
      (if is_emptya A2_ rbt
        then (raise Fail "set_fold1 RBT_set: empty set")
               (fn _ => set_fold1 (A1_, A2_, A3_) f (RBT_set rbt))
        else fold1 A2_ (semilattice_set_apply f) rbt))
  | set_fold1 (A1_, A2_, A3_) f (DList_set dxs) =
    (case ceq A1_
      of NONE =>
        (raise Fail "set_fold1 DList_set: ceq = None")
          (fn _ => set_fold1 (A1_, A2_, A3_) f (DList_set dxs))
      | SOME _ =>
        (if nulla A1_ dxs
          then (raise Fail "set_fold1 DList_set: empty set")
                 (fn _ => set_fold1 (A1_, A2_, A3_) f (DList_set dxs))
          else foldc A1_ (semilattice_set_apply f) (tl A1_ dxs) (hd A1_ dxs)))
  | set_fold1 (A1_, A2_, A3_) f (Set_Monad (x :: xs)) =
    fold (semilattice_set_apply f) xs x
  | set_fold1 (A1_, A2_, A3_) f (Collect_set p) =
    (raise Fail "set_fold1: Collect_set")
      (fn _ => set_fold1 (A1_, A2_, A3_) f (Collect_set p))
  | set_fold1 (A1_, A2_, A3_) f (Complement a) =
    (raise Fail "set_fold1: Complement")
      (fn _ => set_fold1 (A1_, A2_, A3_) f (Complement a));

fun app f a = f a;

fun forallM f [] = Inr ()
  | forallM f (x :: xs) =
    bind (catch_error (f x) (fn xa => Inl (x, xa))) (fn _ => forallM f xs);

fun hm_isEmpty ht = (fn () => (equal_nata (the_size ht) zero_nata));

fun list_all2 p [] ys = null ys
  | list_all2 p xs [] = null xs
  | list_all2 p (x :: xs) (y :: ys) = p x y andalso list_all2 p xs ys;

fun map_defaulta (A1_, A2_) k v f m =
  map_entry (A1_, A2_) k f (default (A1_, A2_) k v m);

fun is_integer_code q = equal_inta (snd (quotient_of q)) one_inta;

fun is_integer q = is_integer_code q;

fun array_get a = FArray.IsabelleMapping.array_get a o integer_of_nat;

fun array_set a = FArray.IsabelleMapping.array_set a o integer_of_nat;

fun new_array v = FArray.IsabelleMapping.new_array v o integer_of_nat;

fun ls_delete A_ k [] = ([], false)
  | ls_delete A_ k ((l, w) :: ls) =
    (if eq A_ k l then (ls, true) else let
 val r = ls_delete A_ k ls;
                                       in
 ((l, w) :: fst r, snd r)
                                       end);

fun ht_delete (A1_, A2_, A3_) B_ k ht =
  (fn f_ => fn () => f_ ((len (heap_list (heap_prod A3_ B_)) (the_array ht)) ())
    ())
    (fn m =>
      let
        val i = bounded_hashcode_nat A2_ m k;
      in
        (fn f_ => fn () => f_
          ((ntha (heap_list (heap_prod A3_ B_)) (the_array ht) i) ()) ())
          (fn l =>
            let
              val la = ls_delete A1_ k l;
            in
              (fn f_ => fn () => f_
                ((upd (heap_list (heap_prod A3_ B_)) i (fst la) (the_array ht))
                ()) ())
                (fn _ =>
                  let
                    val n =
                      (if snd la then minus_nata (the_size ht) one_nata
                        else the_size ht);
                  in
                    (fn () => (HashTable (the_array ht, n)))
                  end)
            end)
      end);

fun ls_lookup A_ x [] = NONE
  | ls_lookup A_ x ((k, v) :: l) =
    (if eq A_ x k then SOME v else ls_lookup A_ x l);

fun ht_lookup (A1_, A2_, A3_) B_ x ht =
  (fn f_ => fn () => f_ ((len (heap_list (heap_prod A3_ B_)) (the_array ht)) ())
    ())
    (fn m =>
      let
        val i = bounded_hashcode_nat A2_ m x;
      in
        (fn f_ => fn () => f_
          ((ntha (heap_list (heap_prod A3_ B_)) (the_array ht) i) ()) ())
          (fn l => (fn () => (ls_lookup A1_ x l)))
      end);

fun ht_rehash (A1_, A2_, A3_) B_ ht =
  (fn f_ => fn () => f_ ((len (heap_list (heap_prod A3_ B_)) (the_array ht)) ())
    ())
    (fn n =>
      (fn f_ => fn () => f_
        ((ht_new_sz (A2_, A3_) B_
           (times_nata (nat_of_integer (2 : Int.int)) n))
        ()) ())
        (ht_copy (A1_, A2_, A3_) B_ n ht));

val load_factor : nat = nat_of_integer (75 : Int.int);

fun ht_update (A1_, A2_, A3_) B_ k v ht =
  (fn f_ => fn () => f_ ((len (heap_list (heap_prod A3_ B_)) (the_array ht)) ())
    ())
    (fn m =>
      (fn f_ => fn () => f_
        ((if less_eq_nat (times_nata m load_factor)
               (times_nata (the_size ht) (nat_of_integer (100 : Int.int)))
           then ht_rehash (A1_, A2_, A3_) B_ ht else (fn () => ht))
        ()) ())
        (ht_upd (A1_, A2_, A3_) B_ k v));

fun op_list_tl x = tla x;

fun map_act f (In x1) = In (f x1)
  | map_act f (Out x2) = Out (f x2)
  | map_act f (Sil x3) = Sil (f x3);

fun set_act (A1_, A2_, A3_) (In x1) =
  insert (A1_, A2_) x1 (bot_set (A1_, A2_, A3_))
  | set_act (A1_, A2_, A3_) (Out x2) =
    insert (A1_, A2_) x2 (bot_set (A1_, A2_, A3_))
  | set_act (A1_, A2_, A3_) (Sil x3) =
    insert (A1_, A2_) x3 (bot_set (A1_, A2_, A3_));

fun time_it s f = let
                    val _ = Timing.start_timer ();
                    val r = f ();
                    val _ = Timing.save_time s;
                  in
                    r
                  end;

fun array_copy A_ a =
  (fn a => fn () =>
  if Array.length a = 0
  then Array.fromList []
  else
    let
      val x = Array.sub(a, 0)
      val n = Array.array (Array.length a, x)
      val _ = Array.copy {src=a,dst=n,di=0}
    in n end
) a;

fun array_grow a = FArray.IsabelleMapping.array_grow a o integer_of_nat;

fun binda m f = (case m of Result a => f a | Error a => Error a);

fun hm_it_adjust (A1_, A2_) B_ v ht =
  (if equal_nata v zero_nata then (fn () => zero_nata)
    else (fn f_ => fn () => f_
           ((ntha (heap_list (heap_prod A2_ B_)) (the_array ht)
              (suc (minus_nata v one_nata)))
           ()) ())
           (fn a =>
             (case a
               of [] =>
                 hm_it_adjust (A1_, A2_) B_
                   (minus_nata (suc (minus_nata v one_nata)) one_nata) ht
               | _ :: _ => (fn () => (suc (minus_nata v one_nata))))));

fun op_list_rev x = rev x;

fun psubst params args =
  the o map_of equal_variable (zip (map fst params) args);

fun parameters (ActionHead (x1, x2)) = x2;

fun subst_term psubst (VAR x) = psubst x
  | subst_term psubst (CONST c) = c;

fun tsubst h args = subst_term (psubst (parameters h) args);

fun map_index n f [] = []
  | map_index n f (x :: xs) = f n x :: map_index (suc n) f xs;

fun quicksort_by_rel r sl [] = sl
  | quicksort_by_rel r sl (x :: xs) =
    let
      val (xs_s, xs_b) = partition_rev (fn y => r y x) ([], []) xs;
    in
      quicksort_by_rel r (x :: quicksort_by_rel r sl xs_b) xs_s
    end;

fun pred_act (A1_, A2_, A3_) =
  (fn p => fn x => ball (A1_, A2_) (set_act (A1_, A2_, A3_) x) p);

fun eoi A_ =
  bindb get_tokens
    (fn tks =>
      (if null tks then return ()
        else err_expecting_aux A_
               (fn _ =>
                 shows_string
                   [Chara (true, false, true, false, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, false, true, false, false, true, true,
                             false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, true, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, false, false, false, true, true, true,
                             false),
                     Chara (true, false, true, false, true, true, true, false),
                     Chara (false, false, true, false, true, true, true,
                             false)])));

fun pR_CONST x = x;

fun comp_fun_idem_apply (Abs_comp_fun_idem x) = x;

fun set_fold_cfi (A1_, A2_) f b (RBT_set rbt) =
  (case ccompare A2_
    of NONE =>
      (raise Fail "set_fold_cfi RBT_set: ccompare = None")
        (fn _ => set_fold_cfi (A1_, A2_) f b (RBT_set rbt))
    | SOME _ => foldb A2_ (comp_fun_idem_apply f) rbt b)
  | set_fold_cfi (A1_, A2_) f b (DList_set dxs) =
    (case ceq A1_
      of NONE =>
        (raise Fail "set_fold_cfi DList_set: ceq = None")
          (fn _ => set_fold_cfi (A1_, A2_) f b (DList_set dxs))
      | SOME _ => foldc A1_ (comp_fun_idem_apply f) dxs b)
  | set_fold_cfi (A1_, A2_) f b (Set_Monad xs) =
    fold (comp_fun_idem_apply f) xs b
  | set_fold_cfi (A1_, A2_) f b (Collect_set p) =
    (raise Fail "set_fold_cfi not supported on Collect_set")
      (fn _ => set_fold_cfi (A1_, A2_) f b (Collect_set p))
  | set_fold_cfi (A1_, A2_) f b (Complement a) =
    (raise Fail "set_fold_cfi not supported on Complement")
      (fn _ => set_fold_cfi (A1_, A2_) f b (Complement a));

fun atoms (A1_, A2_, A3_) (Atom x1) =
  insert (A1_, A2_) x1 (bot_set (A1_, A2_, A3_))
  | atoms (A1_, A2_, A3_) Bot = bot_set (A1_, A2_, A3_)
  | atoms (A1_, A2_, A3_) (Not x3) = atoms (A1_, A2_, A3_) x3
  | atoms (A1_, A2_, A3_) (And (x41, x42)) =
    sup_seta (A1_, A2_) (atoms (A1_, A2_, A3_) x41) (atoms (A1_, A2_, A3_) x42)
  | atoms (A1_, A2_, A3_) (Or (x51, x52)) =
    sup_seta (A1_, A2_) (atoms (A1_, A2_, A3_) x51) (atoms (A1_, A2_, A3_) x52)
  | atoms (A1_, A2_, A3_) (Imp (x61, x62)) =
    sup_seta (A1_, A2_) (atoms (A1_, A2_, A3_) x61) (atoms (A1_, A2_, A3_) x62);

fun op_map_lookup x = (fn k => fn m => m k) x;

fun lookup_default (B1_, B2_) d m k =
  (case lookupa (B1_, B2_) m k of NONE => d | SOME v => v);

fun swap p = (snd p, fst p);

fun whilea b c s = (if b s then whilea b c (c s) else s);

fun array_length x = (nat_of_integer o FArray.IsabelleMapping.array_length) x;

fun array_shrink a = FArray.IsabelleMapping.array_shrink a o integer_of_nat;

fun assert b m = (if b then Result () else Error [m]);

val op_list_empty : 'a list = [];

fun as_get s i = let
                   val (a, _) = s;
                 in
                   array_get a i
                 end;

fun as_shrink s =
  let
    val (a, n) = s;
    val aa =
      (if less_eq_nat (times_nata (nat_of_integer (128 : Int.int)) n)
            (array_length a) andalso
            less_nat (nat_of_integer (4 : Int.int)) n
        then array_shrink a n else a);
  in
    (aa, n)
  end;

fun as_pop s = let
                 val (a, n) = s;
               in
                 as_shrink (a, minus_nata n one_nata)
               end;

fun as_set s i x = let
                     val (a, b) = s;
                   in
                     (array_set a i x, b)
                   end;

fun as_top s = let
                 val (a, n) = s;
               in
                 array_get a (minus_nata n one_nata)
               end;

fun hm_it_next_key (A1_, A2_) B_ ht =
  (fn f_ => fn () => f_ ((len (heap_list (heap_prod A2_ B_)) (the_array ht)) ())
    ())
    (fn n =>
      (if equal_nata n zero_nata then (raise Fail "Map is empty!")
        else (fn f_ => fn () => f_
               ((hm_it_adjust (A1_, A2_) B_ (minus_nata n one_nata) ht) ()) ())
               (fn i =>
                 (fn f_ => fn () => f_
                   ((ntha (heap_list (heap_prod A2_ B_)) (the_array ht) i) ())
                   ())
                   (fn a =>
                     (case a of [] => (raise Fail "Map is empty!")
                       | x :: _ => (fn () => (fst x)))))));

fun min A_ a b = (if less_eq A_ a b then a else b);

fun power A_ a n =
  (if equal_nata n zero_nata then one (one_power A_)
    else times (times_power A_) a (power A_ a (minus_nata n one_nata)));

fun trace m x = let
                  val _ = (fn x => Tracing.count_up ()) m;
                in
                  x
                end;

fun tracea x = trace ExploredState x;

val tRACE_impl : (unit -> unit) = (fn () => (tracea ()));

fun heap_WHILET b f s =
  (fn f_ => fn () => f_ ((b s) ()) ())
    (fn bv =>
      (if bv then (fn f_ => fn () => f_ ((f s) ()) ()) (heap_WHILET b f)
        else (fn () => s)));

fun imp_nfoldli [] c f s = (fn () => s)
  | imp_nfoldli (x :: ls) c f s =
    (fn f_ => fn () => f_ ((c s) ()) ())
      (fn b =>
        (if b then (fn f_ => fn () => f_ ((f x s) ()) ()) (imp_nfoldli ls c f)
          else (fn () => s)));

fun lso_bex_impl pi li =
  imp_nfoldli li (fn sigma => (fn () => (not sigma))) (fn xa => fn _ => pi xa)
    false;

fun op_list_is_empty x = null x;

fun op_list_prepend x = (fn a => x :: a);

fun hms_extract lookup delete k m =
  (fn f_ => fn () => f_ ((lookup k m) ()) ())
    (fn a =>
      (case a of NONE => (fn () => (NONE, m))
        | SOME v =>
          (fn f_ => fn () => f_ ((delete k m) ()) ())
            (fn ma => (fn () => (SOME v, ma)))));

fun pw_impl A_ (B1_, B2_, B3_) keyi copyi tracei lei a_0i fi succsi emptyi =
  (fn f_ => fn () => f_ (a_0i ()) ())
    (fn x =>
      (fn f_ => fn () => f_ ((emptyi x) ()) ())
        (fn xa =>
          (fn f_ => fn () => f_ (a_0i ()) ())
            (fn xaa =>
              (fn f_ => fn () => f_ ((fi xaa) ()) ())
                (fn xab =>
                  (fn f_ => fn () => f_
                    ((if not xa andalso xab
                       then (fn f_ => fn () => f_
                              ((ht_new (B2_, B3_) (heap_list A_)) ()) ())
                              (fn x_b => (fn () => (true, x_b)))
                       else (fn f_ => fn () => f_ (a_0i ()) ())
                              (fn xb =>
                                (fn f_ => fn () => f_ ((emptyi xb) ()) ())
                                  (fn x_a =>
                                    (if x_a
                                      then (fn f_ => fn () => f_
     ((ht_new (B2_, B3_) (heap_list A_)) ()) ())
     (fn x_c => (fn () => (false, x_c)))
                                      else (fn f_ => fn () => f_ (a_0i ()) ())
     (fn xc =>
       (fn f_ => fn () => f_ ((keyi xc) ()) ())
         (fn xd =>
           (fn f_ => fn () => f_ (a_0i ()) ())
             (fn xac =>
               (fn f_ => fn () => f_ ((ht_new (B2_, B3_) (heap_list A_)) ()) ())
                 (fn xba =>
                   (fn f_ => fn () => f_
                     ((ht_update (B1_, B2_, B3_) (heap_list A_) xd [xac] xba)
                     ()) ())
                     (fn xe =>
                       (fn f_ => fn () => f_ (a_0i ()) ())
                         (fn xad =>
                           (fn f_ => fn () => f_
                             ((heap_WHILET
                                (fn (_, (a1b, a2b)) =>
                                  (fn () =>
                                    (not a2b andalso
                                      not (op_list_is_empty a1b))))
                                (fn (a1a, (a1b, a2b)) =>
                                  let
                                    val (a1c, a2c) =
                                      (case a1b
of [] => cODE_ABORT (fn _ => (hda a1b, tla a1b)) | a :: b => (a, b));
                                  in
                                    (fn f_ => fn () => f_ ((emptyi a1c) ()) ())
                                      (fn x_e =>
(if x_e then (fn () => (a1a, (a2c, a2b)))
  else (fn f_ => fn () => f_ (tRACE_impl ()) ())
         (fn _ =>
           (fn f_ => fn () => f_
             ((tracei
                 [Chara (true, false, true, false, false, false, true, false),
                   Chara (false, false, false, true, true, true, true, false),
                   Chara (false, false, false, false, true, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, true, false, false, true, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false)]
                a1c)
             ()) ())
             (fn _ =>
               (fn f_ => fn () => f_ ((succsi a1c) ()) ())
                 (fn x_h =>
                   imp_nfoldli x_h (fn (_, (_, b)) => (fn () => (not b)))
                     (fn xl => fn (a1d, (a1e, _)) =>
                       (fn f_ => fn () => f_ ((emptyi xl) ()) ())
                         (fn x_k =>
                           (if x_k
                             then (fn f_ => fn () => f_
                                    ((tracei
[Chara (true, false, true, false, false, false, true, false),
  Chara (true, false, true, true, false, true, true, false),
  Chara (false, false, false, false, true, true, true, false),
  Chara (false, false, true, false, true, true, true, false),
  Chara (true, false, false, true, true, true, true, false)]
                                       xl)
                                    ()) ())
                                    (fn _ => (fn () => (a1d, (a1e, false))))
                             else (fn f_ => fn () => f_ ((fi xl) ()) ())
                                    (fn x_l =>
                                      (if x_l
then (fn f_ => fn () => f_
       ((tracei
           [Chara (false, true, true, false, false, false, true, false),
             Chara (true, false, false, true, false, true, true, false),
             Chara (false, true, true, true, false, true, true, false),
             Chara (true, false, false, false, false, true, true, false),
             Chara (false, false, true, true, false, true, true, false)]
          xl)
       ()) ())
       (fn _ => (fn () => (a1d, (a1e, true))))
else (fn f_ => fn () => f_ ((keyi xl) ()) ())
       (fn x_m =>
         (fn f_ => fn () => f_
           ((hms_extract (ht_lookup (B1_, B2_, B3_) (heap_list A_))
              (ht_delete (B1_, B2_, B3_) (heap_list A_)) x_m a1d)
           ()) ())
           (fn a =>
             (case a
               of (NONE, a2f) =>
                 (fn f_ => fn () => f_
                   ((tracei
                       [Chara (true, false, false, false, false, false, true,
                                false),
                         Chara (false, false, true, false, false, true, true,
                                 false),
                         Chara (false, false, true, false, false, true, true,
                                 false)]
                      xl)
                   ()) ())
                   (fn _ =>
                     (fn f_ => fn () => f_ ((copyi xl) ()) ())
                       (fn xf =>
                         (fn f_ => fn () => f_
                           ((ht_update (B1_, B2_, B3_) (heap_list A_) x_m [xf]
                              a2f)
                           ()) ())
                           (fn x_r =>
                             (fn () =>
                               (x_r, (op_list_prepend xl a1e, false))))))
               | (SOME x_q, a2f) =>
                 (fn f_ => fn () => f_ ((lso_bex_impl (lei xl) x_q) ()) ())
                   (fn x_r =>
                     (if x_r
                       then (fn f_ => fn () => f_
                              ((tracei
                                  [Chara (true, true, false, false, true, false,
   true, false),
                                    Chara (true, false, true, false, true, true,
    true, false),
                                    Chara (false, true, false, false, false,
    true, true, false),
                                    Chara (true, true, false, false, true, true,
    true, false),
                                    Chara (true, false, true, false, true, true,
    true, false),
                                    Chara (true, false, true, true, false, true,
    true, false),
                                    Chara (true, false, true, false, false,
    true, true, false),
                                    Chara (false, false, true, false, false,
    true, true, false)]
                                 xl)
                              ()) ())
                              (fn _ =>
                                (fn f_ => fn () => f_
                                  ((ht_update (B1_, B2_, B3_) (heap_list A_) x_m
                                     x_q a2f)
                                  ()) ())
                                  (fn x_t => (fn () => (x_t, (a1e, false)))))
                       else (fn f_ => fn () => f_
                              ((tracei
                                  [Chara (true, false, false, false, false,
   false, true, false),
                                    Chara (false, false, true, false, false,
    true, true, false),
                                    Chara (false, false, true, false, false,
    true, true, false)]
                                 xl)
                              ()) ())
                              (fn _ =>
                                (fn f_ => fn () => f_ ((copyi xl) ()) ())
                                  (fn xf =>
                                    (fn f_ => fn () => f_
                                      ((ht_update (B1_, B2_, B3_) (heap_list A_)
 x_m (xf :: x_q) a2f)
                                      ()) ())
                                      (fn x_t =>
(fn () => (x_t, (op_list_prepend xl a1e, false))))))))))))))))
                     (a1a, (a2c, false)))))))
                                  end)
                                (xe, (op_list_prepend xad [], false)))
                             ()) ())
                             (fn (a1a, (_, a2b)) =>
                               (fn () => (a2b, a1a)))))))))))))
                    ()) ())
                    (fn (a1, _) => (fn () => a1))))));

fun imp_for_int_innera i u f s =
  (if u <= i then (fn () => s)
    else (fn f_ => fn () => f_ ((f i s) ()) ())
           (imp_for_int_innera (i + (1 : Int.int)) u f));

fun imp_for_inta i u f s =
  imp_for_int_innera (integer_of_nat i) (integer_of_nat u) (f o nat_of_integer)
    s;

fun mtx_tabulate (A1_, A2_, A3_) (B1_, B2_) n m c =
  (fn f_ => fn () => f_ ((new B2_ (times_nata n m) (zero B1_)) ()) ())
    (fn ma =>
      (fn f_ => fn () => f_
        ((imp_for_inta zero_nata (times_nata n m)
           (fn k => fn (i, (j, maa)) =>
             (fn f_ => fn () => f_ ((upd B2_ k (c (i, j)) maa) ()) ())
               (fn _ =>
                 let
                   val ja = plus_nata j one_nata;
                 in
                   (if less_nat ja m then (fn () => (i, (ja, maa)))
                     else (fn () => (plus A2_ i (one A1_), (zero_nata, maa))))
                 end))
           (zero A3_, (zero_nata, ma)))
        ()) ())
        (fn (_, (_, a)) => (fn () => a)));

fun v_dbm_impl (A1_, A2_) n =
  mtx_tabulate (one_nat, plus_nat, zero_nat)
    (zero_DBMEntry
       ((zero_monoid_add o monoid_add_comm_monoid_add o
          comm_monoid_add_ordered_comm_monoid_add o
          ordered_comm_monoid_add_linordered_ab_monoid_add o
          linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
         A1_),
      heap_DBMEntry A2_)
    (suc n) (suc n)
    (v_dbm (zero_nat, equal_nat, ord_nat)
      ((zero_monoid_add o monoid_add_comm_monoid_add o
         comm_monoid_add_ordered_comm_monoid_add o
         ordered_comm_monoid_add_linordered_ab_monoid_add o
         linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
        A1_)
      n);

fun combine2_gen comb (Error e1) (Error e2) = Error (e1 @ e2)
  | combine2_gen comb (Error e) (Result uu) = Error e
  | combine2_gen comb (Result uv) (Error e) = Error e
  | combine2_gen comb (Result a) (Result b) = comb a b;

fun combinea [] = Result []
  | combinea (x :: xs) =
    combine2_gen (fn xa => fn xsa => Result (xa :: xsa)) x (combinea xs);

fun err_msg m (Error es) = Error (m :: es)
  | err_msg m (Result v) = Result v;

fun is_pos_lit Bot = true
  | is_pos_lit (Not Bot) = true
  | is_pos_lit (Atom (PredAtm (n, args))) = true
  | is_pos_lit (Not (Atom (PredAtm (n, args)))) = false
  | is_pos_lit (Atom (EqAtm (a, b))) = true
  | is_pos_lit (Not (Atom (EqAtm (a, b)))) = true
  | is_pos_lit (Atom (NumericEqAtm (va, vb))) = false
  | is_pos_lit (Atom (NumericLessAtm (va, vb))) = false
  | is_pos_lit (Atom (NumericLEAtm (va, vb))) = false
  | is_pos_lit (Atom (NumericGreaterAtm (va, vb))) = false
  | is_pos_lit (Atom (NumericGEAtm (va, vb))) = false
  | is_pos_lit (Not (Atom (NumericEqAtm (v, vb)))) = false
  | is_pos_lit (Not (Atom (NumericLessAtm (v, vb)))) = false
  | is_pos_lit (Not (Atom (NumericLEAtm (v, vb)))) = false
  | is_pos_lit (Not (Atom (NumericGreaterAtm (v, vb)))) = false
  | is_pos_lit (Not (Atom (NumericGEAtm (v, vb)))) = false
  | is_pos_lit (Not (Not va)) = false
  | is_pos_lit (Not (And (va, vb))) = false
  | is_pos_lit (Not (Or (va, vb))) = false
  | is_pos_lit (Not (Imp (va, vb))) = false
  | is_pos_lit (And (v, va)) = false
  | is_pos_lit (Or (v, va)) = false
  | is_pos_lit (Imp (v, va)) = false;

fun hms_lookup lookup copy k m =
  (fn f_ => fn () => f_ ((lookup k m) ()) ())
    (fn a =>
      (case a of NONE => (fn () => NONE)
        | SOME v =>
          (fn f_ => fn () => f_ ((copy v) ()) ())
            (fn va => (fn () => (SOME va)))));

fun op_list_concat x = (fn a => x @ a);

fun as_push s x =
  let
    val (a, n) = s;
    val aa =
      (if equal_nata n (array_length a)
        then array_grow a
               (max ord_nat (nat_of_integer (4 : Int.int))
                 (times_nata (nat_of_integer (2 : Int.int)) n))
               x
        else a);
    val ab = array_set aa n x;
  in
    (ab, plus_nata n one_nata)
  end;

fun as_take m s = let
                    val (a, n) = s;
                  in
                    (if less_nat m n then as_shrink (a, m) else (a, n))
                  end;

fun rev_append [] ac = ac
  | rev_append (x :: xs) ac = rev_append xs (x :: ac);

fun ran_of_map_impl (A1_, A2_, A3_) B_ =
  (fn xi =>
    (fn f_ => fn () => f_
      ((heap_WHILET
         (fn (_, a2) =>
           (fn f_ => fn () => f_ ((hm_isEmpty a2) ()) ())
             (fn x_a => (fn () => (not x_a))))
         (fn (a1, a2) =>
           (fn f_ => fn () => f_ ((hm_it_next_key (A2_, A3_) B_ a2) ()) ())
             (fn x_a =>
               (fn f_ => fn () => f_
                 ((hms_extract (ht_lookup (A1_, A2_, A3_) B_)
                    (ht_delete (A1_, A2_, A3_) B_) x_a a2)
                 ()) ())
                 (fn (a1a, b) => (fn () => (the a1a :: a1, b)))))
         ([], xi))
      ()) ())
      (fn (a1, _) => (fn () => a1)));

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun name (Func x) = x;

fun combine2 x = combine2_gen (fn a => fn b => Result (a, b)) x;

fun is_pos_conj (And (f, g)) = is_pos_lit f andalso is_pos_conj g
  | is_pos_conj (Atom v) = is_pos_lit (Atom v)
  | is_pos_conj Bot = is_pos_lit Bot
  | is_pos_conj (Not v) = is_pos_lit (Not v)
  | is_pos_conj (Or (v, va)) = is_pos_lit (Or (v, va))
  | is_pos_conj (Imp (v, va)) = is_pos_lit (Imp (v, va));

fun mtx_get A_ m mtx e = ntha A_ mtx (plus_nata (times_nata (fst e) m) (snd e));

fun mtx_set A_ m mtx e v =
  upd A_ (plus_nata (times_nata (fst e) m) (snd e)) v mtx;

fun idx_iteratei_aux get sz i l c f sigma =
  (if equal_nata i zero_nata orelse not (c sigma) then sigma
    else idx_iteratei_aux get sz (minus_nata i one_nata) l c f
           (f (get l (minus_nata sz i)) sigma));

fun idx_iteratei get sz l c f sigma =
  idx_iteratei_aux get (sz l) (sz l) l c f sigma;

fun as_empty B_ uu = (FArray.IsabelleMapping.array_of_list [], zero B_);

fun leadsto_impl_0 A_ (B1_, B2_, B3_) copyia succsia leia keyia x =
  let
    val (a1, (a1a, a2a)) = x;
  in
    (fn f_ => fn () => f_ ((keyia a2a) ()) ())
      (fn xa =>
        (fn f_ => fn () => f_
          ((hms_extract (ht_lookup (B1_, B2_, B3_) (heap_list A_))
             (ht_delete (B1_, B2_, B3_) (heap_list A_)) xa a1a)
          ()) ())
          (fn xaa =>
            (fn f_ => fn () => f_
              ((case xaa of (NONE, a2b) => (fn () => (a2b, false))
                 | (SOME x_c, a2b) =>
                   (fn f_ => fn () => f_
                     ((imp_nfoldli x_c (fn sigma => (fn () => (not sigma)))
                        (fn xe => fn sigma =>
                          (fn f_ => fn () => f_ ((leia xe a2a) ()) ())
                            (fn x_f => (fn () => (x_f orelse sigma))))
                        false)
                     ()) ())
                     (fn x_d =>
                       (fn f_ => fn () => f_
                         ((ht_update (B1_, B2_, B3_) (heap_list A_) xa x_c a2b)
                         ()) ())
                         (fn x_e => (fn () => (x_e, x_d)))))
              ()) ())
              (fn a =>
                (case a of (a1b, true) => (fn () => (a1, (a1b, true)))
                  | (a1b, false) =>
                    (fn f_ => fn () => f_ ((keyia a2a) ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_
                          ((hms_extract
                             (ht_lookup (B1_, B2_, B3_) (heap_list A_))
                             (ht_delete (B1_, B2_, B3_) (heap_list A_)) xb a1)
                          ()) ())
                          (fn xab =>
                            (fn f_ => fn () => f_
                              ((case xab
                                 of (NONE, a2c) => (fn () => (a2c, false))
                                 | (SOME x_e, a2c) =>
                                   (fn f_ => fn () => f_
                                     ((lso_bex_impl (leia a2a) x_e) ()) ())
                                     (fn x_f =>
                                       (fn f_ => fn () => f_
 ((ht_update (B1_, B2_, B3_) (heap_list A_) xb x_e a2c) ()) ())
 (fn x_g => (fn () => (x_g, x_f)))))
                              ()) ())
                              (fn aa =>
                                (case aa
                                  of (a1c, true) =>
                                    (fn () => (a1c, (a1b, false)))
                                  | (a1c, false) =>
                                    (fn f_ => fn () => f_ ((copyia a2a) ()) ())
                                      (fn xc =>
(fn f_ => fn () => f_ ((keyia xc) ()) ())
  (fn xd =>
    (fn f_ => fn () => f_
      ((hms_extract (ht_lookup (B1_, B2_, B3_) (heap_list A_))
         (ht_delete (B1_, B2_, B3_) (heap_list A_)) xd a1b)
      ()) ())
      (fn xac =>
        (fn f_ => fn () => f_
          ((case xac
             of (NONE, a2d) =>
               (fn f_ => fn () => f_ ((copyia a2a) ()) ())
                 (fn xad =>
                   (fn f_ => fn () => f_
                     ((ht_update (B1_, B2_, B3_) (heap_list A_) xd
                        (op_list_prepend xad []) a2d)
                     ()) ())
                     (fn x_h => (fn () => ((), x_h))))
             | (SOME x_g, a2d) =>
               (fn f_ => fn () => f_ ((copyia a2a) ()) ())
                 (fn xad =>
                   (fn f_ => fn () => f_
                     ((ht_update (B1_, B2_, B3_) (heap_list A_) xd
                        (op_list_prepend xad x_g) a2d)
                     ()) ())
                     (fn x_i => (fn () => ((), x_i)))))
          ()) ())
          (fn (_, a2d) =>
            (fn f_ => fn () => f_ ((succsia a2a) ()) ())
              (fn xe =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli xe (fn (_, (_, b)) => (fn () => (not b)))
                     (fn xi => fn (a1e, (a1f, _)) =>
                       leadsto_impl_0 A_ (B1_, B2_, B3_) copyia succsia leia
                         keyia (a1e, (a1f, xi)))
                     (a1c, (a2d, false)))
                  ()) ())
                  (fn (a1e, (a1f, a2f)) =>
                    (fn f_ => fn () => f_ ((copyia a2a) ()) ())
                      (fn xf =>
                        (fn f_ => fn () => f_ ((keyia xf) ()) ())
                          (fn xg =>
                            (fn f_ => fn () => f_
                              ((hms_extract
                                 (ht_lookup (B1_, B2_, B3_) (heap_list A_))
                                 (ht_delete (B1_, B2_, B3_) (heap_list A_)) xg
                                 a1f)
                              ()) ())
                              (fn xad =>
                                (fn f_ => fn () => f_
                                  ((case xad
                                     of (NONE, a2g) =>
                                       (fn f_ => fn () => f_
 ((ht_update (B1_, B2_, B3_) (heap_list A_) xg [] a2g) ()) ())
 (fn x_k => (fn () => ((), x_k)))
                                     | (SOME x_j, a2g) =>
                                       (fn f_ => fn () => f_
 ((ht_update (B1_, B2_, B3_) (heap_list A_) xg
    (if op_list_is_empty x_j then [] else op_list_tl x_j) a2g)
 ()) ())
 (fn x_l => (fn () => ((), x_l))))
                                  ()) ())
                                  (fn (_, a2g) =>
                                    (fn f_ => fn () => f_ ((copyia a2a) ()) ())
                                      (fn xh =>
(fn f_ => fn () => f_ ((keyia xh) ()) ())
  (fn xi =>
    (fn f_ => fn () => f_
      ((hms_extract (ht_lookup (B1_, B2_, B3_) (heap_list A_))
         (ht_delete (B1_, B2_, B3_) (heap_list A_)) xi a1e)
      ()) ())
      (fn xae =>
        (fn f_ => fn () => f_
          ((case xae
             of (NONE, a2h) =>
               (fn f_ => fn () => f_ ((copyia a2a) ()) ())
                 (fn xaf =>
                   (fn f_ => fn () => f_
                     ((ht_update (B1_, B2_, B3_) (heap_list A_) xi [xaf] a2h)
                     ()) ())
                     (fn x_m => (fn () => ((), x_m))))
             | (SOME x_l, a2h) =>
               (fn f_ => fn () => f_ ((copyia a2a) ()) ())
                 (fn xaf =>
                   (fn f_ => fn () => f_
                     ((ht_update (B1_, B2_, B3_) (heap_list A_) xi (xaf :: x_l)
                        a2h)
                     ()) ())
                     (fn x_n => (fn () => ((), x_n)))))
          ()) ())
          (fn (_, a2h) =>
            (fn f_ => fn () => f_ (tRACE_impl ()) ())
              (fn _ => (fn () => (a2h, (a2g, a2f))))))))))))))))))))))))))
  end;

fun leadsto_impl A_ (B1_, B2_, B3_) copyia succsia a_0ia leia keyia succs1i
  emptyi pi qi tracei =
  (fn f_ => fn () => f_ (a_0ia ()) ())
    (fn x =>
      (fn f_ => fn () => f_ ((emptyi x) ()) ())
        (fn xa =>
          (fn f_ => fn () => f_ (a_0ia ()) ())
            (fn _ =>
              (fn f_ => fn () => f_
                ((if not xa andalso false
                   then (fn f_ => fn () => f_
                          ((ht_new (B2_, B3_) (heap_list A_)) ()) ())
                          (fn x_b => (fn () => (true, x_b)))
                   else (fn f_ => fn () => f_ (a_0ia ()) ())
                          (fn xb =>
                            (fn f_ => fn () => f_ ((emptyi xb) ()) ())
                              (fn x_a =>
                                (if x_a
                                  then (fn f_ => fn () => f_
 ((ht_new (B2_, B3_) (heap_list A_)) ()) ())
 (fn x_c => (fn () => (false, x_c)))
                                  else (fn f_ => fn () => f_ (a_0ia ()) ())
 (fn xc =>
   (fn f_ => fn () => f_ ((keyia xc) ()) ())
     (fn xd =>
       (fn f_ => fn () => f_ (a_0ia ()) ())
         (fn xaa =>
           (fn f_ => fn () => f_ ((ht_new (B2_, B3_) (heap_list A_)) ()) ())
             (fn xba =>
               (fn f_ => fn () => f_
                 ((ht_update (B1_, B2_, B3_) (heap_list A_) xd [xaa] xba) ())
                 ())
                 (fn xe =>
                   (fn f_ => fn () => f_ (a_0ia ()) ())
                     (fn xab =>
                       (fn f_ => fn () => f_
                         ((heap_WHILET
                            (fn (_, (a1b, a2b)) =>
                              (fn () =>
                                (not a2b andalso not (op_list_is_empty a1b))))
                            (fn (a1a, (a1b, a2b)) =>
                              let
                                val (a1c, a2c) =
                                  (case a1b
                                    of [] =>
                                      cODE_ABORT (fn _ => (hda a1b, tla a1b))
                                    | a :: b => (a, b));
                              in
                                (fn f_ => fn () => f_ ((emptyi a1c) ()) ())
                                  (fn x_e =>
                                    (if x_e then (fn () => (a1a, (a2c, a2b)))
                                      else (fn f_ => fn () => f_ (tRACE_impl ())
     ())
     (fn _ =>
       (fn f_ => fn () => f_
         ((tracei
             [Chara (true, false, true, false, false, false, true, false),
               Chara (false, false, false, true, true, true, true, false),
               Chara (false, false, false, false, true, true, true, false),
               Chara (false, false, true, true, false, true, true, false),
               Chara (true, true, true, true, false, true, true, false),
               Chara (false, true, false, false, true, true, true, false),
               Chara (true, false, true, false, false, true, true, false),
               Chara (false, false, true, false, false, true, true, false)]
            a1c)
         ()) ())
         (fn _ =>
           (fn f_ => fn () => f_ ((succs1i a1c) ()) ())
             (fn x_h =>
               imp_nfoldli x_h (fn (_, (_, b)) => (fn () => (not b)))
                 (fn xl => fn (a1d, (a1e, _)) =>
                   (fn f_ => fn () => f_ ((emptyi xl) ()) ())
                     (fn x_k =>
                       (if x_k then (fn () => (a1d, (a1e, false)))
                         else (fn f_ => fn () => f_ ((keyia xl) ()) ())
                                (fn x_m =>
                                  (fn f_ => fn () => f_
                                    ((hms_extract
                                       (ht_lookup (B1_, B2_, B3_)
 (heap_list A_))
                                       (ht_delete (B1_, B2_, B3_)
 (heap_list A_))
                                       x_m a1d)
                                    ()) ())
                                    (fn a =>
                                      (case a
of (NONE, a2f) =>
  (fn f_ => fn () => f_ ((copyia xl) ()) ())
    (fn xf =>
      (fn f_ => fn () => f_
        ((ht_update (B1_, B2_, B3_) (heap_list A_) x_m [xf] a2f) ()) ())
        (fn x_o => (fn () => (x_o, (op_list_prepend xl a1e, false)))))
| (SOME x_o, a2f) =>
  (fn f_ => fn () => f_ ((lso_bex_impl (leia xl) x_o) ()) ())
    (fn x_p =>
      (if x_p
        then (fn f_ => fn () => f_
               ((ht_update (B1_, B2_, B3_) (heap_list A_) x_m x_o a2f) ()) ())
               (fn x_q => (fn () => (x_q, (a1e, false))))
        else (fn f_ => fn () => f_ ((copyia xl) ()) ())
               (fn xf =>
                 (fn f_ => fn () => f_
                   ((ht_update (B1_, B2_, B3_) (heap_list A_) x_m (xf :: x_o)
                      a2f)
                   ()) ())
                   (fn x_q =>
                     (fn () => (x_q, (op_list_prepend xl a1e, false)))))))))))))
                 (a1a, (a2c, false)))))))
                              end)
                            (xe, (op_list_prepend xab [], false)))
                         ()) ())
                         (fn (a1a, (_, a2b)) => (fn () => (a2b, a1a)))))))))))))
                ()) ())
                (fn (_, a2) =>
                  (fn f_ => fn () => f_
                    ((ran_of_map_impl (B1_, B2_, B3_) (heap_list A_) a2) ()) ())
                    (fn x_a =>
                      (fn f_ => fn () => f_ ((ht_new (B2_, B3_) (heap_list A_))
                        ()) ())
                        (fn xb =>
                          (fn f_ => fn () => f_
                            ((imp_nfoldli x_a
                               (fn (a1a, _) => (fn () => (not a1a)))
                               (fn xd => fn (_, a2a) =>
                                 imp_nfoldli xd
                                   (fn (a1b, _) => (fn () => (not a1b)))
                                   (fn xg => fn (_, a2b) =>
                                     (fn f_ => fn () => f_ ((pi xg) ()) ())
                                       (fn xc =>
 (fn f_ => fn () => f_ ((qi xg) ()) ())
   (fn xaa =>
     (if xc andalso xaa
       then (fn f_ => fn () => f_ ((ht_new (B2_, B3_) (heap_list A_)) ()) ())
              (fn xe =>
                (fn f_ => fn () => f_
                  ((leadsto_impl_0 A_ (B1_, B2_, B3_) copyia succsia leia keyia
                     (a2b, (xe, xg)))
                  ()) ())
                  (fn (a1, (_, a2aa)) => (fn () => (a2aa, a1))))
       else (fn () => (false, a2b))))))
                                   (false, a2a))
                               (false, xb))
                            ()) ())
                            (fn (a1a, _) => (fn () => a1a))))))));

fun as_length x = snd x;

fun last_seg_tr s =
  let
    val (a, (aa, (_, _))) = s;
    val (_, bc) =
      whilea
        (fn (xe, _) =>
          less_nat xe
            (if equal_nata
                  (plus_nata (minus_nata (as_length aa) one_nata) one_nata)
                  (as_length aa)
              then as_length a
              else as_get aa
                     (plus_nata (minus_nata (as_length aa) one_nata) one_nata)))
        (fn (ac, bc) => let
                          val xa = as_get a ac;
                        in
                          (suc ac, xa :: bc)
                        end)
        (as_get aa (minus_nata (as_length aa) one_nata), []);
  in
    bc
  end;

fun list_map_update_aux eq k v [] accu = (k, v) :: accu
  | list_map_update_aux eq k v (x :: xs) accu =
    (if eq (fst x) k then (k, v) :: xs @ accu
      else list_map_update_aux eq k v xs (x :: accu));

fun list_map_update eq k v m = list_map_update_aux eq k v m [];

fun list_map_lookup eq uu [] = NONE
  | list_map_lookup eq k (y :: ys) =
    (if eq (fst y) k then SOME (snd y) else list_map_lookup eq k ys);

fun ahm_update_aux eq bhc (HashMap (a, n)) k v =
  let
    val h = bhc (array_length a) k;
    val m = array_get a h;
    val insert = is_none (list_map_lookup eq k m);
  in
    HashMap
      (array_set a h (list_map_update eq k v m),
        (if insert then plus_nata n one_nata else n))
  end;

fun ahm_iteratei_aux a c f sigma =
  idx_iteratei array_get array_length a c (fn x => foldli x c f) sigma;

fun ahm_rehash_auxa bhc n kv a = let
                                   val h = bhc n (fst kv);
                                 in
                                   array_set a h (kv :: array_get a h)
                                 end;

fun ahm_rehash_aux bhc a sz =
  ahm_iteratei_aux a (fn _ => true) (ahm_rehash_auxa bhc sz) (new_array [] sz);

fun ahm_rehash bhc (HashMap (a, n)) sz = HashMap (ahm_rehash_aux bhc a sz, n);

val load_factora : nat = nat_of_integer (75 : Int.int);

fun ahm_filled (HashMap (a, n)) =
  less_eq_nat (times_nata (array_length a) load_factora)
    (times_nata n (nat_of_integer (100 : Int.int)));

fun hm_grow (HashMap (a, n)) =
  plus_nata (times_nata (nat_of_integer (2 : Int.int)) (array_length a))
    (nat_of_integer (3 : Int.int));

fun ahm_update eq bhc k v hm =
  let
    val hma = ahm_update_aux eq bhc hm k v;
  in
    (if ahm_filled hma then ahm_rehash bhc hma (hm_grow hma) else hma)
  end;

fun pop_tr node_eq_impl node_hash_impl s =
  let
    val (a, (aa, (ab, bb))) = s;
    val x = minus_nata (as_length aa) one_nata;
    val xa =
      let
        val (_, bc) =
          whilea
            (fn (xe, _) =>
              less_nat xe
                (if equal_nata (plus_nata x one_nata) (as_length aa)
                  then as_length a else as_get aa (plus_nata x one_nata)))
            (fn (ac, bc) =>
              (suc ac,
                ahm_update node_eq_impl node_hash_impl (as_get a ac)
                  (uminus_inta one_inta) bc))
            (as_get aa x, ab);
      in
        bc
      end;
    val xb = as_take (as_top aa) a;
    val xc = as_pop aa;
  in
    (xb, (xc, (xa, bb)))
  end;

fun glist_delete_aux eq x [] asa = asa
  | glist_delete_aux eq x (y :: ys) asa =
    (if eq x y then rev_append asa ys else glist_delete_aux eq x ys (y :: asa));

fun glist_delete eq x l = glist_delete_aux eq x l [];

fun lx_uppercase x =
  range (linorder_char, show_char)
    (Chara (true, false, false, false, false, false, true, false))
    (Chara (false, true, false, true, true, false, true, false)) x;

fun lx_lowercase x =
  range (linorder_char, show_char)
    (Chara (true, false, false, false, false, true, true, false))
    (Chara (false, true, false, true, true, true, true, false)) x;

fun lx_alpha x =
  bindb (alt lx_lowercase lx_uppercase) (fn xa => return (sum_join xa)) x;

val zero_rat : rat = Frct (zero_inta, one_inta);

fun is_predAtom (Atom (PredAtm (uu, uv))) = true
  | is_predAtom (Atom (EqAtm (va, vb))) = false
  | is_predAtom (Atom (NumericEqAtm (va, vb))) = false
  | is_predAtom (Atom (NumericLessAtm (va, vb))) = false
  | is_predAtom (Atom (NumericLEAtm (va, vb))) = false
  | is_predAtom (Atom (NumericGreaterAtm (va, vb))) = false
  | is_predAtom (Atom (NumericGEAtm (va, vb))) = false
  | is_predAtom Bot = false
  | is_predAtom (Not v) = false
  | is_predAtom (And (v, va)) = false
  | is_predAtom (Or (v, va)) = false
  | is_predAtom (Imp (v, va)) = false;

fun is_Nil a = (case a of [] => true | _ :: _ => false);

fun act_sym (In a) = a
  | act_sym (Out a) = a
  | act_sym (Sil a) = a;

fun norm_diag (A1_, A2_, A3_) e =
  (if dbm_lt A3_ e (Le (zero A1_)) then Lt (zero A1_)
    else (if equal_DBMEntry A2_ e (Le (zero A1_)) then e else INF));

fun fold_error f [] a = Result a
  | fold_error f (x :: xs) a = binda (f x a) (fold_error f xs);

fun the_errors (Error es) = es;

fun find_max_nat n uu =
  (if equal_nata n zero_nata then zero_nata
    else (if uu (minus_nata n one_nata) then minus_nata n one_nata
           else find_max_nat (minus_nata n one_nata) uu));

fun amtx_copy A_ = array_copy A_;

fun amtx_dflt A_ n m v = make A_ (times_nata n m) (fn _ => v);

fun inst_duration_in_numeric_expression (ConstantExpr x) d = ConstantExpr x
  | inst_duration_in_numeric_expression DurationExpr d = ConstantExpr d
  | inst_duration_in_numeric_expression (AddExpr (x, y)) d =
    AddExpr
      (inst_duration_in_numeric_expression x d,
        inst_duration_in_numeric_expression y d)
  | inst_duration_in_numeric_expression (SubExpr (x, y)) d =
    SubExpr
      (inst_duration_in_numeric_expression x d,
        inst_duration_in_numeric_expression y d)
  | inst_duration_in_numeric_expression (MulExpr (x, y)) d =
    MulExpr
      (inst_duration_in_numeric_expression x d,
        inst_duration_in_numeric_expression y d)
  | inst_duration_in_numeric_expression (DivExpr (x, y)) d =
    DivExpr
      (inst_duration_in_numeric_expression x d,
        inst_duration_in_numeric_expression y d)
  | inst_duration_in_numeric_expression (SinExpr x) d =
    SinExpr (inst_duration_in_numeric_expression x d)
  | inst_duration_in_numeric_expression (CosExpr x) d =
    CosExpr (inst_duration_in_numeric_expression x d)
  | inst_duration_in_numeric_expression (ExpExpr x) d =
    ExpExpr (inst_duration_in_numeric_expression x d)
  | inst_duration_in_numeric_expression PiExpr d = PiExpr
  | inst_duration_in_numeric_expression (FunctionExpr x) d = FunctionExpr x;

fun inst_duration_in_atom (EqAtm (x, y)) d = EqAtm (x, y)
  | inst_duration_in_atom (NumericEqAtm (x, y)) d =
    NumericEqAtm
      (inst_duration_in_numeric_expression x d,
        inst_duration_in_numeric_expression y d)
  | inst_duration_in_atom (NumericLessAtm (x, y)) d =
    NumericLessAtm
      (inst_duration_in_numeric_expression x d,
        inst_duration_in_numeric_expression y d)
  | inst_duration_in_atom (NumericLEAtm (x, y)) d =
    NumericLEAtm
      (inst_duration_in_numeric_expression x d,
        inst_duration_in_numeric_expression y d)
  | inst_duration_in_atom (NumericGreaterAtm (x, y)) d =
    NumericGreaterAtm
      (inst_duration_in_numeric_expression x d,
        inst_duration_in_numeric_expression y d)
  | inst_duration_in_atom (NumericGEAtm (x, y)) d =
    NumericGEAtm
      (inst_duration_in_numeric_expression x d,
        inst_duration_in_numeric_expression y d)
  | inst_duration_in_atom (PredAtm (p, a)) d = PredAtm (p, a);

fun map_primitive_numeric_expression f (PNE (x1, x2)) = PNE (x1, map f x2);

fun map_numeric_expression f (ConstantExpr x1) = ConstantExpr x1
  | map_numeric_expression f DurationExpr = DurationExpr
  | map_numeric_expression f (AddExpr (x31, x32)) =
    AddExpr (map_numeric_expression f x31, map_numeric_expression f x32)
  | map_numeric_expression f (SubExpr (x41, x42)) =
    SubExpr (map_numeric_expression f x41, map_numeric_expression f x42)
  | map_numeric_expression f (MulExpr (x51, x52)) =
    MulExpr (map_numeric_expression f x51, map_numeric_expression f x52)
  | map_numeric_expression f (DivExpr (x61, x62)) =
    DivExpr (map_numeric_expression f x61, map_numeric_expression f x62)
  | map_numeric_expression f (SinExpr x7) =
    SinExpr (map_numeric_expression f x7)
  | map_numeric_expression f (CosExpr x8) =
    CosExpr (map_numeric_expression f x8)
  | map_numeric_expression f (ExpExpr x9) =
    ExpExpr (map_numeric_expression f x9)
  | map_numeric_expression f PiExpr = PiExpr
  | map_numeric_expression f (FunctionExpr x11) =
    FunctionExpr (map_primitive_numeric_expression f x11);

fun map_atom f (PredAtm (x11, x12)) = PredAtm (x11, map f x12)
  | map_atom f (EqAtm (x21, x22)) = EqAtm (f x21, f x22)
  | map_atom f (NumericEqAtm (x31, x32)) =
    NumericEqAtm (map_numeric_expression f x31, map_numeric_expression f x32)
  | map_atom f (NumericLessAtm (x41, x42)) =
    NumericLessAtm (map_numeric_expression f x41, map_numeric_expression f x42)
  | map_atom f (NumericLEAtm (x51, x52)) =
    NumericLEAtm (map_numeric_expression f x51, map_numeric_expression f x52)
  | map_atom f (NumericGreaterAtm (x61, x62)) =
    NumericGreaterAtm
      (map_numeric_expression f x61, map_numeric_expression f x62)
  | map_atom f (NumericGEAtm (x71, x72)) =
    NumericGEAtm (map_numeric_expression f x71, map_numeric_expression f x72);

fun map_formula f (Atom x1) = Atom (f x1)
  | map_formula f Bot = Bot
  | map_formula f (Not x3) = Not (map_formula f x3)
  | map_formula f (And (x41, x42)) = And (map_formula f x41, map_formula f x42)
  | map_formula f (Or (x51, x52)) = Or (map_formula f x51, map_formula f x52)
  | map_formula f (Imp (x61, x62)) = Imp (map_formula f x61, map_formula f x62);

fun inst_formula f dur form =
  map_formula ((fn x => inst_duration_in_atom x dur) o map_atom f) form;

fun ll_from_list l = LL (size_list l, l);

fun show_pres (Inr (ll, uu)) = Inr ll
  | show_pres (Inl e) = Inl e;

fun parse_all ws p =
  show_pres o
    bindb p
      (fn a => bindb ws (fn _ => bindb (eoi show_char) (fn _ => return a))) o
    ll_from_list o
    explode;

fun save_time_impl x =
  ((fn a => (fn () => a)) o (fn a => Timing.save_time a)) x;

fun is_None a = (case a of NONE => true | SOME _ => false);

fun norm_lower A_ e t = (if dbm_lt A_ e (Lt t) then Lt t else e);

fun norm_upper A_ e t = (if dbm_lt A_ (Le t) e then INF else e);

fun min_int_entry (Lt x) (Lt y) = (if less_eq_int x y then Lt x else Lt y)
  | min_int_entry (Lt x) (Le y) = (if less_eq_int x y then Lt x else Le y)
  | min_int_entry (Le x) (Lt y) = (if less_int x y then Le x else Lt y)
  | min_int_entry (Le x) (Le y) = (if less_eq_int x y then Le x else Le y)
  | min_int_entry INF x = x
  | min_int_entry (Le v) INF = Le v
  | min_int_entry (Lt v) INF = Lt v;

fun and_entry_impl x =
  (fn n => fn ai => fn bib => fn bia => fn bi =>
    (fn f_ => fn () => f_
      ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (ai, bib)) ()) ())
      (fn xa =>
        mtx_set (heap_DBMEntry heap_int) (suc n) bi (ai, bib)
          (min_int_entry xa bia)))
    x;

fun free_impl_int x =
  (fn n => fn ai => fn bi =>
    (fn f_ => fn () => f_
      ((imp_for_inta zero_nata (suc n)
         (fn xa => fn sigma =>
           (if not (equal_nata xa bi)
             then (fn f_ => fn () => f_
                    ((mtx_get (heap_DBMEntry heap_int) (suc n) sigma
                       (xa, zero_nata))
                    ()) ())
                    (mtx_set (heap_DBMEntry heap_int) (suc n) sigma (xa, bi))
             else (fn () => sigma)))
         ai)
      ()) ())
      (imp_for_inta zero_nata (suc n)
        (fn xb => fn sigma =>
          (if not (equal_nata xb bi)
            then mtx_set (heap_DBMEntry heap_int) (suc n) sigma (bi, xb) INF
            else (fn () => sigma)))))
    x;

fun dbm_lt_int (Le a) (Le b) = less_int a b
  | dbm_lt_int (Le a) (Lt b) = less_int a b
  | dbm_lt_int (Lt a) (Le b) = less_eq_int a b
  | dbm_lt_int (Lt a) (Lt b) = less_int a b
  | dbm_lt_int INF uu = false
  | dbm_lt_int (Le v) INF = true
  | dbm_lt_int (Lt v) INF = true;

fun dbm_add_int INF uu = INF
  | dbm_add_int (Le v) INF = INF
  | dbm_add_int (Lt v) INF = INF
  | dbm_add_int (Le a) (Le b) = Le (plus_inta a b)
  | dbm_add_int (Le a) (Lt b) = Lt (plus_inta a b)
  | dbm_add_int (Lt a) (Le b) = Lt (plus_inta a b)
  | dbm_add_int (Lt a) (Lt b) = Lt (plus_inta a b);

fun fw_upd_impl_integer n a k i j =
  let
    val na = n + (1 : Int.int);
    val ia = i * na + j;
  in
    (fn f_ => fn () => f_ (((fn () => Array.sub (a, Int.toInt (i * na + k))))
      ()) ())
      (fn y =>
        (fn f_ => fn () => f_
          (((fn () => Array.sub (a, Int.toInt (k * na + j)))) ()) ())
          (fn z =>
            (fn f_ => fn () => f_ (((fn () => Array.sub (a, Int.toInt ia)))
              ()) ())
              (fn x =>
                let
                  val m = dbm_add_int y z;
                in
                  (if dbm_lt_int m x
                    then (fn a => fn () => (Array.update (a, Int.toInt ia, m); a)) a
                    else (fn () => a))
                end)))
  end;

fun fwi_impl_int n a k =
  let
    val na = integer_of_nat n;
    val n_plus_1 = na + (1 : Int.int);
  in
    imp_for_int_innera (0 : Int.int) n_plus_1
      (fn i =>
        imp_for_int_innera (0 : Int.int) n_plus_1
          (fn ia => fn xa => fw_upd_impl_integer na xa (integer_of_nat k) i ia))
      a
  end;

fun repair_pair_impl_int x =
  (fn n => fn ai => fn bia => fn bi =>
    (fn f_ => fn () => f_ ((fwi_impl_int n ai bi) ()) ())
      (fn xa => fwi_impl_int n xa bia))
    x;

fun restrict_zero_impl n =
  (fn ai => fn bi =>
    (fn f_ => fn () => f_ ((and_entry_impl n bi zero_nata (Le zero_inta) ai) ())
      ())
      (fn x =>
        (fn f_ => fn () => f_ ((and_entry_impl n zero_nata bi (Le zero_inta) x)
          ()) ())
          (fn x_a => repair_pair_impl_int n x_a bi zero_nata)));

fun pre_reset_impl n =
  (fn ai => fn bi =>
    (fn f_ => fn () => f_ ((restrict_zero_impl n ai bi) ()) ())
      (fn x => free_impl_int n x bi));

fun gi_E (Gen_g_impl_ext (gi_V, gi_E, gi_V0, more)) = gi_E;

fun more (Gen_g_impl_ext (gi_V, gi_E, gi_V0, more)) = more;

fun combine_map f xs = combinea (map f xs);

fun as_is_empty s = equal_nata (snd s) zero_nata;

fun interval (A1_, A2_) a b =
  (if less ((ord_preorder o preorder_order o order_linorder o linorder_interval)
             A2_)
        a b
    then a :: interval (A1_, A2_)
                (plus ((plus_semigroup_add o semigroup_add_numeral o
                         numeral_semiring_numeral o
                         semiring_numeral_semiring_1 o
                         semiring_1_comm_semiring_1 o
                         comm_semiring_1_comm_semiring_1_cancel o
                         comm_semiring_1_cancel_interval)
                        A2_)
                  a (one ((one_numeral o numeral_semiring_numeral o
                            semiring_numeral_semiring_1 o
                            semiring_1_comm_semiring_1 o
                            comm_semiring_1_comm_semiring_1_cancel o
                            comm_semiring_1_cancel_interval)
                           A2_)))
                b
    else (if eq A1_ a b then [a] else []));

fun tab_succ (A1_, A2_, A3_) l =
  lookup_default (A1_, A2_) []
    (fold (fn (u, v) => map_defaulta (A1_, A2_) u [] (fn a => v :: a)) l
      (emptya (A1_, A3_)));

fun ty_term varT objT (VAR v) = varT v
  | ty_term varT objT (CONST c) =
    lookupa (ccompare_object, equal_object) objT c;

fun minus_set (A1_, A2_) (RBT_set rbt1) (RBT_set rbt2) =
  (case ccompare A2_
    of NONE =>
      (raise Fail "minus RBT_set RBT_set: ccompare = None")
        (fn _ => minus_set (A1_, A2_) (RBT_set rbt1) (RBT_set rbt2))
    | SOME _ => RBT_set (minus A2_ rbt1 rbt2))
  | minus_set (A1_, A2_) a b = inf_seta (A1_, A2_) a (uminus_set b);

fun heap_map copy xs =
  (fn f_ => fn () => f_
    ((imp_nfoldli xs (fn _ => (fn () => true))
       (fn x => fn xsa =>
         (fn f_ => fn () => f_ ((copy x) ()) ())
           (fn xa => (fn () => (xa :: xsa))))
       [])
    ()) ())
    (fn xsa => (fn () => (rev xsa)));

fun gi_V0 (Gen_g_impl_ext (gi_V, gi_E, gi_V0, more)) = gi_V0;

fun select_edge_tr node_eq_impl s =
  let
    val (a, (aa, (ab, bb))) = s;
  in
    (if as_is_empty bb then (NONE, (a, (aa, (ab, bb))))
      else let
             val (ac, bc) = as_top bb;
           in
             (if less_eq_nat (as_get aa (minus_nata (as_length aa) one_nata)) ac
               then let
                      val xa = gen_pick (fn x => foldli (id x)) bc;
                      val xb = glist_delete node_eq_impl xa bc;
                      val xc =
                        (if is_Nil xb then as_pop bb
                          else as_set bb (minus_nata (as_length bb) one_nata)
                                 (ac, xb));
                    in
                      (SOME xa, (a, (aa, (ab, xc))))
                    end
               else (NONE, (a, (aa, (ab, bb)))))
           end)
  end;

fun ahm_lookup_aux eq bhc k a =
  list_map_lookup eq k (array_get a (bhc (array_length a) k));

fun ahm_lookup eq bhc k (HashMap (a, uu)) = ahm_lookup_aux eq bhc k a;

fun idx_of_tr node_eq_impl node_hash_impl s v =
  let
    val (_, (aa, (ab, _))) = v;
    val x = let
              val SOME i = ahm_lookup node_eq_impl node_hash_impl s ab;
              val true = less_eq_int zero_inta i;
            in
              nat i
            end;
    val xa = find_max_nat (as_length aa) (fn j => less_eq_nat (as_get aa j) x);
  in
    xa
  end;

fun collapse_tr node_eq_impl node_hash_impl v s =
  let
    val (a, (aa, (ab, bb))) = s;
    val x = idx_of_tr node_eq_impl node_hash_impl v (a, (aa, (ab, bb)));
    val xa = as_take (plus_nata x one_nata) aa;
  in
    (a, (xa, (ab, bb)))
  end;

fun as_singleton B_ x = (FArray.IsabelleMapping.array_of_list [x], one B_);

fun new_hashmap_with size = HashMap (new_array [] size, zero_nata);

fun ahm_empty def_size = new_hashmap_with def_size;

fun push_code node_eq_impl node_hash_impl g_impl =
  (fn x => fn (xa, (xb, (xc, xd))) =>
    let
      val _ = (fn x => ()) ();
      val y_a = as_length xa;
      val y_b = as_push xa x;
      val y_c = as_push xb y_a;
      val y_d = ahm_update node_eq_impl node_hash_impl x (int_of_nat y_a) xc;
      val y_e =
        (if is_Nil (gi_E g_impl x) then xd
          else as_push xd (y_a, gi_E g_impl x));
    in
      (y_b, (y_c, (y_d, y_e)))
    end);

fun compute_SCC_tr node_eq_impl node_hash_impl node_def_hash_size g =
  let
    val _ = (fn x => ()) ();
    val xa = ([], ahm_empty node_def_hash_size);
    val (a, _) =
      foldli (id (gi_V0 g)) (fn _ => true)
        (fn xb => fn (a, b) =>
          (if not (case ahm_lookup node_eq_impl node_hash_impl xb b
                    of NONE => false
                    | SOME i =>
                      (if less_eq_int zero_inta i then false else true))
            then let
                   val xc =
                     (a, (as_singleton one_nat xb,
                           (as_singleton one_nat zero_nata,
                             (ahm_update node_eq_impl node_hash_impl xb
                                (int_of_nat zero_nata) b,
                               (if is_Nil (gi_E g xb) then as_empty zero_nat ()
                                 else as_singleton one_nat
(zero_nata, gi_E g xb))))));
                   val (aa, (_, (_, (ad, _)))) =
                     whilea
                       (fn (_, xf) =>
                         not (as_is_empty let
    val (xg, (_, (_, _))) = xf;
  in
    xg
  end))
                       (fn (aa, ba) =>
                         (case select_edge_tr node_eq_impl ba
                           of (NONE, bb) =>
                             let
                               val xf = last_seg_tr bb;
                               val xg = pop_tr node_eq_impl node_hash_impl bb;
                               val xh = xf :: aa;
                             in
                               (xh, xg)
                             end
                           | (SOME xf, bb) =>
                             (if (case ahm_lookup node_eq_impl node_hash_impl xf
 let
   val (_, (_, (xl, _))) = bb;
 in
   xl
 end
                                   of NONE => false
                                   | SOME i =>
                                     (if less_eq_int zero_inta i then true
                                       else false))
                               then let
                                      val ab =
collapse_tr node_eq_impl node_hash_impl xf bb;
                                    in
                                      (aa, ab)
                                    end
                               else (if not
  (case ahm_lookup node_eq_impl node_hash_impl xf let
            val (_, (_, (xl, _))) = bb;
          in
            xl
          end
    of NONE => false
    | SOME i => (if less_eq_int zero_inta i then false else true))
                                      then (aa,
     push_code node_eq_impl node_hash_impl g xf bb)
                                      else (aa, bb)))))
                       xc;
                 in
                   (aa, ad)
                 end
            else (a, b)))
        xa;
    val _ = (fn x => ()) ();
  in
    a
  end;

fun constraint_clk (LTa (c, uu)) = c
  | constraint_clk (LEa (c, uv)) = c
  | constraint_clk (EQa (c, uw)) = c
  | constraint_clk (GEa (c, ux)) = c
  | constraint_clk (GTa (c, uy)) = c;

fun start_timer_impl x =
  ((fn a => (fn () => a)) o (fn a => Timing.start_timer a)) x;

fun predicate (PredAtm (x11, x12)) = x11;

fun namea (Pred x) = x;

fun neg_dbm_entry_int (Le a) = Lt (uminus_inta a)
  | neg_dbm_entry_int (Lt a) = Le (uminus_inta a)
  | neg_dbm_entry_int INF = INF;

fun and_entry_repair_impl x =
  (fn n => fn ai => fn bib => fn bia => fn bi =>
    (fn f_ => fn () => f_ ((and_entry_impl n ai bib bia bi) ()) ())
      (fn xa => repair_pair_impl_int n xa ai bib))
    x;

fun upd_entry_impl_int x =
  (fn n => fn ai => fn bib => fn bia => fn bi =>
    (fn f_ => fn () => f_
      ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (ai, bib)) ()) ())
      (fn xa =>
        (fn f_ => fn () => f_ ((amtx_copy (heap_DBMEntry heap_int) bia) ()) ())
          (and_entry_repair_impl n bib ai (neg_dbm_entry_int xa))))
    x;

fun upd_entries_impl x =
  (fn n => fn ai => fn bib => fn bia => fn bi =>
    (fn f_ => fn () => f_
      ((imp_nfoldli bi (fn _ => (fn () => true))
         (fn xa => fn sigma =>
           (fn f_ => fn () => f_ ((upd_entry_impl_int n ai bib xa bia) ()) ())
             (fn x_b => (fn () => (x_b :: sigma))))
         op_list_empty)
      ()) ())
      (fn xa =>
        imp_nfoldli xa (fn _ => (fn () => true))
          (fn xb => fn sigma => (fn () => (xb :: sigma))) op_list_empty))
    x;

fun no_stutter A_ [] = true
  | no_stutter A_ [uu] = true
  | no_stutter A_ (a :: b :: l) =
    not (eq A_ a b) andalso no_stutter A_ (b :: l);

fun trim_ld_zs [] = []
  | trim_ld_zs (d :: ds) =
    (if equal_nata d zero_nata then trim_ld_zs ds else d :: ds);

fun trim_tr_zsa [] zs = []
  | trim_tr_zsa (d :: ds) zs =
    (if equal_nata d zero_nata then trim_tr_zsa ds (zero_nata :: zs)
      else zs @ d :: trim_tr_zsa ds []);

fun trim_tr_zs ds = trim_tr_zsa ds [];

fun map_exp f (Const x1) = Const x1
  | map_exp f (Var x2) = Var (f x2)
  | map_exp f (If_then_else (x31, x32, x33)) =
    If_then_else (map_bexp f x31, map_exp f x32, map_exp f x33)
  | map_exp f (Binop (x41, x42, x43)) =
    Binop (x41, map_exp f x42, map_exp f x43)
  | map_exp f (Unop (x51, x52)) = Unop (x51, map_exp f x52)
and map_bexp f True = True
  | map_bexp f (Nota x2) = Nota (map_bexp f x2)
  | map_bexp f (Anda (x31, x32)) = Anda (map_bexp f x31, map_bexp f x32)
  | map_bexp f (Ora (x41, x42)) = Ora (map_bexp f x41, map_bexp f x42)
  | map_bexp f (Imply (x51, x52)) = Imply (map_bexp f x51, map_bexp f x52)
  | map_bexp f (Eqa (x61, x62)) = Eqa (map_exp f x61, map_exp f x62)
  | map_bexp f (Lea (x71, x72)) = Lea (map_exp f x71, map_exp f x72)
  | map_bexp f (Ltb (x81, x82)) = Ltb (map_exp f x81, map_exp f x82)
  | map_bexp f (Ge (x91, x92)) = Ge (map_exp f x91, map_exp f x92)
  | map_bexp f (Gta (x101, x102)) = Gta (map_exp f x101, map_exp f x102);

fun set_exp (A1_, A2_, A3_) (Const x1) = bot_set (A1_, A2_, A3_)
  | set_exp (A1_, A2_, A3_) (Var x2) =
    insert (A1_, A2_) x2 (bot_set (A1_, A2_, A3_))
  | set_exp (A1_, A2_, A3_) (If_then_else (x31, x32, x33)) =
    sup_seta (A1_, A2_)
      (sup_seta (A1_, A2_) (set_bexp (A1_, A2_, A3_) x31)
        (set_exp (A1_, A2_, A3_) x32))
      (set_exp (A1_, A2_, A3_) x33)
  | set_exp (A1_, A2_, A3_) (Binop (x41, x42, x43)) =
    sup_seta (A1_, A2_) (set_exp (A1_, A2_, A3_) x42)
      (set_exp (A1_, A2_, A3_) x43)
  | set_exp (A1_, A2_, A3_) (Unop (x51, x52)) = set_exp (A1_, A2_, A3_) x52
and set_bexp (A1_, A2_, A3_) True = bot_set (A1_, A2_, A3_)
  | set_bexp (A1_, A2_, A3_) (Nota x2) = set_bexp (A1_, A2_, A3_) x2
  | set_bexp (A1_, A2_, A3_) (Anda (x31, x32)) =
    sup_seta (A1_, A2_) (set_bexp (A1_, A2_, A3_) x31)
      (set_bexp (A1_, A2_, A3_) x32)
  | set_bexp (A1_, A2_, A3_) (Ora (x41, x42)) =
    sup_seta (A1_, A2_) (set_bexp (A1_, A2_, A3_) x41)
      (set_bexp (A1_, A2_, A3_) x42)
  | set_bexp (A1_, A2_, A3_) (Imply (x51, x52)) =
    sup_seta (A1_, A2_) (set_bexp (A1_, A2_, A3_) x51)
      (set_bexp (A1_, A2_, A3_) x52)
  | set_bexp (A1_, A2_, A3_) (Eqa (x61, x62)) =
    sup_seta (A1_, A2_) (set_exp (A1_, A2_, A3_) x61)
      (set_exp (A1_, A2_, A3_) x62)
  | set_bexp (A1_, A2_, A3_) (Lea (x71, x72)) =
    sup_seta (A1_, A2_) (set_exp (A1_, A2_, A3_) x71)
      (set_exp (A1_, A2_, A3_) x72)
  | set_bexp (A1_, A2_, A3_) (Ltb (x81, x82)) =
    sup_seta (A1_, A2_) (set_exp (A1_, A2_, A3_) x81)
      (set_exp (A1_, A2_, A3_) x82)
  | set_bexp (A1_, A2_, A3_) (Ge (x91, x92)) =
    sup_seta (A1_, A2_) (set_exp (A1_, A2_, A3_) x91)
      (set_exp (A1_, A2_, A3_) x92)
  | set_bexp (A1_, A2_, A3_) (Gta (x101, x102)) =
    sup_seta (A1_, A2_) (set_exp (A1_, A2_, A3_) x101)
      (set_exp (A1_, A2_, A3_) x102);

fun constraint_pair (LTa (x, m)) = (x, m)
  | constraint_pair (LEa (x, m)) = (x, m)
  | constraint_pair (EQa (x, m)) = (x, m)
  | constraint_pair (GEa (x, m)) = (x, m)
  | constraint_pair (GTa (x, m)) = (x, m);

fun adds (Effect (x1, x2, x3)) = x1;

fun dels (Effect (x1, x2, x3)) = x2;

fun primitives (Either x) = x;

fun rbt_to_list Empty = []
  | rbt_to_list (Branch (c, l, e, x, r)) = e :: rbt_to_list l @ rbt_to_list r;

fun check_passed_impl A_ (B1_, B2_, B3_) succsi a_0i fi lei emptyi keyi copyi
  tracei qi =
  (fn f_ => fn () => f_ (a_0i ()) ())
    (fn x =>
      (fn f_ => fn () => f_ ((emptyi x) ()) ())
        (fn xa =>
          (fn f_ => fn () => f_ (a_0i ()) ())
            (fn xaa =>
              (fn f_ => fn () => f_ ((fi xaa) ()) ())
                (fn xab =>
                  (fn f_ => fn () => f_
                    ((if not xa andalso xab
                       then (fn f_ => fn () => f_
                              ((ht_new (B2_, B3_) (heap_list A_)) ()) ())
                              (fn x_b => (fn () => (true, x_b)))
                       else (fn f_ => fn () => f_ (a_0i ()) ())
                              (fn xb =>
                                (fn f_ => fn () => f_ ((emptyi xb) ()) ())
                                  (fn x_a =>
                                    (if x_a
                                      then (fn f_ => fn () => f_
     ((ht_new (B2_, B3_) (heap_list A_)) ()) ())
     (fn x_c => (fn () => (false, x_c)))
                                      else (fn f_ => fn () => f_ (a_0i ()) ())
     (fn xc =>
       (fn f_ => fn () => f_ ((keyi xc) ()) ())
         (fn xd =>
           (fn f_ => fn () => f_ (a_0i ()) ())
             (fn xac =>
               (fn f_ => fn () => f_ ((ht_new (B2_, B3_) (heap_list A_)) ()) ())
                 (fn xba =>
                   (fn f_ => fn () => f_
                     ((ht_update (B1_, B2_, B3_) (heap_list A_) xd [xac] xba)
                     ()) ())
                     (fn xe =>
                       (fn f_ => fn () => f_ (a_0i ()) ())
                         (fn xad =>
                           (fn f_ => fn () => f_
                             ((heap_WHILET
                                (fn (_, (a1b, a2b)) =>
                                  (fn () =>
                                    (not a2b andalso
                                      not (op_list_is_empty a1b))))
                                (fn (a1a, (a1b, a2b)) =>
                                  let
                                    val (a1c, a2c) =
                                      (case a1b
of [] => cODE_ABORT (fn _ => (hda a1b, tla a1b)) | a :: b => (a, b));
                                  in
                                    (fn f_ => fn () => f_ ((emptyi a1c) ()) ())
                                      (fn x_e =>
(if x_e then (fn () => (a1a, (a2c, a2b)))
  else (fn f_ => fn () => f_ (tRACE_impl ()) ())
         (fn _ =>
           (fn f_ => fn () => f_
             ((tracei
                 [Chara (true, false, true, false, false, false, true, false),
                   Chara (false, false, false, true, true, true, true, false),
                   Chara (false, false, false, false, true, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, true, false, false, true, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false)]
                a1c)
             ()) ())
             (fn _ =>
               (fn f_ => fn () => f_ ((succsi a1c) ()) ())
                 (fn x_h =>
                   imp_nfoldli x_h (fn (_, (_, b)) => (fn () => (not b)))
                     (fn xl => fn (a1d, (a1e, _)) =>
                       (fn f_ => fn () => f_ ((emptyi xl) ()) ())
                         (fn x_k =>
                           (if x_k then (fn () => (a1d, (a1e, false)))
                             else (fn f_ => fn () => f_ ((fi xl) ()) ())
                                    (fn x_l =>
                                      (if x_l then (fn () => (a1d, (a1e, true)))
else (fn f_ => fn () => f_ ((keyi xl) ()) ())
       (fn x_m =>
         (fn f_ => fn () => f_
           ((hms_extract (ht_lookup (B1_, B2_, B3_) (heap_list A_))
              (ht_delete (B1_, B2_, B3_) (heap_list A_)) x_m a1d)
           ()) ())
           (fn a =>
             (case a
               of (NONE, a2f) =>
                 (fn f_ => fn () => f_ ((copyi xl) ()) ())
                   (fn xf =>
                     (fn f_ => fn () => f_
                       ((ht_update (B1_, B2_, B3_) (heap_list A_) x_m [xf] a2f)
                       ()) ())
                       (fn x_o =>
                         (fn () => (x_o, (op_list_prepend xl a1e, false)))))
               | (SOME x_o, a2f) =>
                 (fn f_ => fn () => f_ ((lso_bex_impl (lei xl) x_o) ()) ())
                   (fn x_p =>
                     (if x_p
                       then (fn f_ => fn () => f_
                              ((ht_update (B1_, B2_, B3_) (heap_list A_) x_m x_o
                                 a2f)
                              ()) ())
                              (fn x_q => (fn () => (x_q, (a1e, false))))
                       else (fn f_ => fn () => f_ ((copyi xl) ()) ())
                              (fn xf =>
                                (fn f_ => fn () => f_
                                  ((ht_update (B1_, B2_, B3_) (heap_list A_) x_m
                                     (xf :: x_o) a2f)
                                  ()) ())
                                  (fn x_q =>
                                    (fn () =>
                                      (x_q,
(op_list_prepend xl a1e, false)))))))))))))))
                     (a1a, (a2c, false)))))))
                                  end)
                                (xe, (op_list_prepend xad [], false)))
                             ()) ())
                             (fn (a1a, (_, a2b)) =>
                               (fn () => (a2b, a1a)))))))))))))
                    ()) ())
                    (fn (_, a2) =>
                      (fn f_ => fn () => f_
                        ((ran_of_map_impl (B1_, B2_, B3_) (heap_list A_) a2) ())
                        ())
                        (fn x_a =>
                          imp_nfoldli x_a (fn sigma => (fn () => (not sigma)))
                            (fn xd => fn _ =>
                              imp_nfoldli xd
                                (fn sigma => (fn () => (not sigma)))
                                (fn xg => fn _ =>
                                  (fn f_ => fn () => f_ ((qi xg) ()) ())
                                    (fn x_g =>
                                      (fn () => (if x_g then true else false))))
                                false)
                            false))))));

fun numeric_effects (Effect (x1, x2, x3)) = x3;

fun conjunct_effects l =
  Effect
    ((concat o map adds) l, (concat o map dels) l,
      (concat o map numeric_effects) l);

fun filter_time_spec t l =
  map_filter
    (fn x =>
      (if (equal_temporal_annotationa t o fst) x then SOME (snd x) else NONE))
    l;

fun maxa (A1_, A2_, A3_, A4_) a = set_fold1 (A1_, A2_, A3_) (max_sls A4_) a;

fun quicksorta A_ =
  quicksort_by_rel
    (less_eq ((ord_preorder o preorder_order o order_linorder) A_)) [];

fun distinct_ds (A1_, A2_) l = no_stutter A1_ (quicksorta A2_ l);

fun print_check s b = writeln (s ^ ": " ^ (if b then "passed" else "failed"));

fun types (Domain (x1, x2, x3, x4, x5)) = x1;

fun goal (Problem (x1, x2, x3, x4)) = x4;

fun inita (Problem (x1, x2, x3, x4)) = x3;

fun collect_clock_pairs (A1_, A2_, A3_, A4_, A5_) (B1_, B2_, B3_, B4_, B5_) cc =
  image (ceq_acconstraint A4_ B4_, ccompare_acconstraint A3_ B3_)
    (ceq_prod A1_ B1_, ccompare_prod A2_ B2_, set_impl_prod A5_ B5_)
    constraint_pair
    (set (ceq_acconstraint A4_ B4_, ccompare_acconstraint A3_ B3_,
           set_impl_acconstraint)
      cc);

fun clkp_set_impl (E1_, E2_, E3_, E4_, E5_) (F1_, F2_, F3_, F4_, F5_) automata =
  sup_seta (ceq_prod E1_ F1_, ccompare_prod E2_ F2_)
    (foldl (sup_seta (ceq_prod E1_ F1_, ccompare_prod E2_ F2_))
      (bot_set (ceq_prod E1_ F1_, ccompare_prod E2_ F2_, set_impl_prod E5_ F5_))
      (foldl
        (fn a => fn x =>
          a @ map (fn g =>
                    collect_clock_pairs (E1_, E2_, E3_, E4_, E5_)
                      (F1_, F2_, F3_, F4_, F5_) (snd g))
                (snd (snd (snd x))))
        [] automata))
    (foldl (sup_seta (ceq_prod E1_ F1_, ccompare_prod E2_ F2_))
      (bot_set (ceq_prod E1_ F1_, ccompare_prod E2_ F2_, set_impl_prod E5_ F5_))
      (foldl
        (fn a => fn x =>
          a @ map (fn (_, (_, (g, _))) =>
                    collect_clock_pairs (E1_, E2_, E3_, E4_, E5_)
                      (F1_, F2_, F3_, F4_, F5_) g)
                (fst (snd (snd x))))
        [] automata));

fun clk_set_impl (E1_, E2_, E3_, E4_, E5_) (F1_, F2_, F3_, F4_, F5_) automata =
  sup_seta (E1_, E2_)
    (image (ceq_prod E1_ F1_, ccompare_prod E2_ F2_) (E1_, E2_, E5_) fst
      (clkp_set_impl (E1_, E2_, E3_, E4_, E5_) (F1_, F2_, F3_, F4_, F5_)
        automata))
    (foldl (sup_seta (E1_, E2_)) (bot_set (E1_, E2_, E5_))
      (foldl
        (fn a => fn x =>
          a @ map (fn (_, (_, (_, (_, (_, (r, _)))))) => set (E1_, E2_, E5_) r)
                (fst (snd (snd x))))
        [] automata));

fun loc_set_impl (C1_, C2_, C3_) automata p =
  foldl (fn a => fn x =>
          sup_seta (C1_, C2_) a
            let
              val (l, (_, (_, (_, (_, (_, la)))))) = x;
            in
              insert (C1_, C2_) l
                (insert (C1_, C2_) la (bot_set (C1_, C2_, C3_)))
            end)
    (bot_set (C1_, C2_, C3_)) (fst (snd (snd (nth automata p))));

fun all_interval (A1_, A2_) p a b =
  (if less ((ord_preorder o preorder_order o order_linorder o linorder_interval)
             A2_)
        a b
    then p a andalso
           all_interval (A1_, A2_) p
             (plus ((plus_semigroup_add o semigroup_add_numeral o
                      numeral_semiring_numeral o semiring_numeral_semiring_1 o
                      semiring_1_comm_semiring_1 o
                      comm_semiring_1_comm_semiring_1_cancel o
                      comm_semiring_1_cancel_interval)
                     A2_)
               a (one ((one_numeral o numeral_semiring_numeral o
                         semiring_numeral_semiring_1 o
                         semiring_1_comm_semiring_1 o
                         comm_semiring_1_comm_semiring_1_cancel o
                         comm_semiring_1_cancel_interval)
                        A2_)))
             b
    else true) andalso
    (if eq A1_ a b then p a else true);

fun dfs_reachable (A1_, A2_, A3_) succ d w =
  let
    val (_, (_, brk)) =
      whilea (fn (_, (wa, brk)) => not brk andalso not (null wa))
        (fn (v, (va :: wa, _)) =>
          (if d va then (v, (va :: wa, true))
            else (if member (A1_, A2_) va v then (v, (wa, false))
                   else let
                          val vb = insert (A1_, A2_) va v;
                          val wb = succ va @ wa;
                        in
                          (vb, (wb, false))
                        end)))
        (bot_set (A1_, A2_, A3_), (w, false));
  in
    brk
  end;

fun of_type_impl g oT t =
  list_all
    (fn pt =>
      dfs_reachable (ceq_literal, ccompare_literal, set_impl_literal) g
        (fn a => ((pt : string) = a)) (primitives t))
    (primitives oT);

fun run_map_heap f xs = Par_List.map ((fn a => (fn f => f ()) a) o f) xs;

fun consts (Domain (x1, x2, x3, x4, x5)) = x4;

fun n num_states q = num_states q;

fun sup_setb (A1_, A2_, A3_, A4_, A5_) a =
  (if finite
        (finite_UNIV_set A1_, ceq_set (A2_, A3_, ccompare_cproper_interval A4_),
          ccompare_set (A1_, A3_, A4_, A5_))
        a
    then set_fold_cfi
           (ceq_set (A2_, A3_, ccompare_cproper_interval A4_),
             ccompare_set (A1_, A3_, A4_, A5_))
           (sup_cfi (lattice_set (A2_, A3_, ccompare_cproper_interval A4_)))
           (bot_set (A3_, ccompare_cproper_interval A4_, A5_)) a
    else (raise Fail "Sup: infinite")
           (fn _ => sup_setb (A1_, A2_, A3_, A4_, A5_) a));

fun clkp_inv automata i l =
  sup_setb
    (finite_UNIV_prod finite_UNIV_nat finite_UNIV_int,
      cenum_prod cenum_nat cenum_int, ceq_prod ceq_nat ceq_int,
      cproper_interval_prod cproper_interval_nat cproper_interval_int,
      set_impl_prod set_impl_nat set_impl_int)
    (image
      (ceq_prod ceq_nat (ceq_list (ceq_acconstraint equal_nat equal_int)),
        ccompare_prod ccompare_nat
          (ccompare_list (ccompare_acconstraint compare_nat compare_int)))
      (ceq_set
         (cenum_prod cenum_nat cenum_int, ceq_prod ceq_nat ceq_int,
           ccompare_cproper_interval
             (cproper_interval_prod cproper_interval_nat cproper_interval_int)),
        ccompare_set
          (finite_UNIV_prod finite_UNIV_nat finite_UNIV_int,
            ceq_prod ceq_nat ceq_int,
            cproper_interval_prod cproper_interval_nat cproper_interval_int,
            set_impl_prod set_impl_nat set_impl_int),
        set_impl_set)
      (fn g =>
        collect_clock_pairs
          (ceq_nat, ccompare_nat, compare_nat, equal_nat, set_impl_nat)
          (ceq_int, ccompare_int, compare_int, equal_int, set_impl_int) (snd g))
      (set (ceq_prod ceq_nat (ceq_list (ceq_acconstraint equal_nat equal_int)),
             ccompare_prod ccompare_nat
               (ccompare_list (ccompare_acconstraint compare_nat compare_int)),
             set_impl_prod set_impl_nat set_impl_list)
        (filter (fn (a, _) => equal_nata a l)
          (snd (snd (snd (nth automata i)))))));

fun bound_inv automata q c l =
  maxa (ceq_int, ccompare_int, lattice_int, linorder_int)
    (sup_seta (ceq_int, ccompare_int)
      (insert (ceq_int, ccompare_int) zero_inta
        (set_empty (ceq_int, ccompare_int) (of_phantom set_impl_inta)))
      (sup_setb
        (finite_UNIV_int, cenum_int, ceq_int, cproper_interval_int,
          set_impl_int)
        (image
          (ceq_prod ceq_nat ceq_int, ccompare_prod ccompare_nat ccompare_int)
          (ceq_set
             (cenum_int, ceq_int,
               ccompare_cproper_interval cproper_interval_int),
            ccompare_set
              (finite_UNIV_int, ceq_int, cproper_interval_int, set_impl_int),
            set_impl_set)
          (fn (x, d) =>
            (if equal_nata x c
              then insert (ceq_int, ccompare_int) d
                     (set_empty (ceq_int, ccompare_int)
                       (of_phantom set_impl_inta))
              else set_empty (ceq_int, ccompare_int)
                     (of_phantom set_impl_inta)))
          (clkp_inv automata q l))));

fun clkp_set_impla automata i l =
  sup_seta (ceq_prod ceq_nat ceq_int, ccompare_prod ccompare_nat ccompare_int)
    (clkp_inv automata i l)
    (foldl
      (fn a => fn x =>
        sup_seta
          (ceq_prod ceq_nat ceq_int, ccompare_prod ccompare_nat ccompare_int) a
          let
            val (la, (_, (g, _))) = x;
          in
            (if equal_nata la l
              then collect_clock_pairs
                     (ceq_nat, ccompare_nat, compare_nat, equal_nat,
                       set_impl_nat)
                     (ceq_int, ccompare_int, compare_int, equal_int,
                       set_impl_int)
                     g
              else set_empty
                     (ceq_prod ceq_nat ceq_int,
                       ccompare_prod ccompare_nat ccompare_int)
                     (of_phantom (set_impl_proda set_impl_nat set_impl_int)))
          end)
      (set_empty
        (ceq_prod ceq_nat ceq_int, ccompare_prod ccompare_nat ccompare_int)
        (of_phantom (set_impl_proda set_impl_nat set_impl_int)))
      (fst (snd (snd (nth automata i)))));

fun clkp_set x = clkp_set_impla x;

fun bound_g automata q c l =
  maxa (ceq_int, ccompare_int, lattice_int, linorder_int)
    (sup_seta (ceq_int, ccompare_int)
      (insert (ceq_int, ccompare_int) zero_inta
        (set_empty (ceq_int, ccompare_int) (of_phantom set_impl_inta)))
      (sup_setb
        (finite_UNIV_int, cenum_int, ceq_int, cproper_interval_int,
          set_impl_int)
        (image
          (ceq_prod ceq_nat ceq_int, ccompare_prod ccompare_nat ccompare_int)
          (ceq_set
             (cenum_int, ceq_int,
               ccompare_cproper_interval cproper_interval_int),
            ccompare_set
              (finite_UNIV_int, ceq_int, cproper_interval_int, set_impl_int),
            set_impl_set)
          (fn (x, d) =>
            (if equal_nata x c
              then insert (ceq_int, ccompare_int) d
                     (set_empty (ceq_int, ccompare_int)
                       (of_phantom set_impl_inta))
              else set_empty (ceq_int, ccompare_int)
                     (of_phantom set_impl_inta)))
          (clkp_set automata q l))));

fun bound automata q c l =
  max ord_int (bound_g automata q c l) (bound_inv automata q c l);

fun w automata num_states q c la l =
  (if equal_nata la (n num_states q) then uminus_inta (bound automata q c l)
    else zero_inta);

fun v num_states q = (fn v => less_eq_nat v (n num_states q));

fun resets automata q c l =
  fold (fn (l1, (_, (_, (_, (_, (r, la)))))) => fn xs =>
         (if not (equal_nata l1 l) orelse
               (membera equal_nat xs la orelse membera equal_nat r c)
           then xs else la :: xs))
    (fst (snd (snd (nth automata q)))) [];

fun ea automata q c l = resets automata q c l;

fun e automata num_states q c l =
  (if equal_nata l (n num_states q) then upt zero_nata (n num_states q)
    else filter (fn la => membera equal_nat (ea automata q c la) l)
           (upt zero_nata (n num_states q)));

fun g automata num_states q c =
  Gen_g_impl_ext
    (v num_states q, e automata num_states q c, [n num_states q],
      w automata num_states q c);

fun compute_SCC_tra (A1_, A2_) =
  compute_SCC_tr (eq A1_) (bounded_hashcode_nat A2_)
    (def_hashmap_size A2_ Type);

fun calc_shortest_scc_paths (A1_, A2_, A3_) g n =
  let
    val sccs = compute_SCC_tra (equal_nat, hashable_nat) g;
    val d = replicate n NONE @ [SOME (zero A2_)];
    val da =
      fold (fold (fn u =>
                   fold (fn v => fn da =>
                          (case nth da u of NONE => da
                            | SOME du =>
                              (case nth da v
                                of NONE =>
                                  list_update da v
                                    (SOME (plus A1_ du (more g u v)))
                                | SOME dv =>
                                  (if less A3_ (plus A1_ du (more g u v)) dv
                                    then list_update da v
   (SOME (plus A1_ du (more g u v)))
                                    else da))))
                     (gi_E g u)))
        sccs d;
    val db =
      fold (fn vs => fn db =>
             let
               val dscc =
                 fold (fn v => fn dscc =>
                        (case dscc of NONE => nth db v
                          | SOME daa =>
                            (case nth db v of NONE => dscc
                              | SOME dv => SOME (min A3_ dv daa))))
                   vs NONE;
             in
               fold (fn v => fn dc => list_update dc v dscc) vs db
             end)
        sccs da;
  in
    db
  end;

fun local_ceiling_single automata num_states q c =
  let
    val a =
      calc_shortest_scc_paths (plus_int, zero_int, ord_int)
        (g automata num_states q c) (n num_states q);
  in
    map (fn aa =>
          (case aa of NONE => zero_nata | SOME x => nat (uminus_inta x)))
      a
  end;

fun local_ceiling broadcast bounds automata m num_states =
  app rev
    (fold (fn q => fn xs =>
            app (fn x => rev x :: xs)
              (fold (fn l => fn xsa =>
                      app (fn x => (zero_nata :: rev x) :: xsa)
                        (fold (fn c =>
                                (fn a =>
                                  nth (local_ceiling_single automata num_states
q c)
                                    l ::
                                    a))
                          (upt one_nata (suc m)) []))
                (upt zero_nata (n num_states q)) []))
      (upt zero_nata (size_list automata)) []);

fun map_acconstraint f1 f2 (LTa (x11, x12)) = LTa (f1 x11, f2 x12)
  | map_acconstraint f1 f2 (LEa (x21, x22)) = LEa (f1 x21, f2 x22)
  | map_acconstraint f1 f2 (EQa (x31, x32)) = EQa (f1 x31, f2 x32)
  | map_acconstraint f1 f2 (GTa (x41, x42)) = GTa (f1 x41, f2 x42)
  | map_acconstraint f1 f2 (GEa (x51, x52)) = GEa (f1 x51, f2 x52);

fun map_cconstraint f g xs = map (map_acconstraint f g) xs;

fun renum_cconstraint A_ renum_clocks = map_cconstraint renum_clocks id;

fun renum_reset A_ renum_clocks = map renum_clocks;

fun renum_bexp A_ renum_vars = map_bexp renum_vars;

fun renum_exp A_ renum_vars = map_exp renum_vars;

fun renum_upd A_ renum_vars =
  (fn (x, upd) => (renum_vars x, renum_exp A_ renum_vars upd));

fun renum_act A_ renum_acts = map_act renum_acts;

fun renum_automaton A_ B_ C_ D_ renum_acts renum_vars renum_clocks renum_states
  i = (fn (committed, (urgent, (trans, inv))) =>
        let
          val committeda = map (renum_states i) committed;
          val urgenta = map (renum_states i) urgent;
          val transa =
            map (fn (l, (b, (g, (a, (upd, (r, la)))))) =>
                  (renum_states i l,
                    (renum_bexp B_ renum_vars b,
                      (renum_cconstraint C_ renum_clocks g,
                        (renum_act A_ renum_acts a,
                          (map (renum_upd B_ renum_vars) upd,
                            (renum_reset C_ renum_clocks r,
                              renum_states i la)))))))
              trans;
          val inva =
            map (fn (l, g) =>
                  (renum_states i l, renum_cconstraint C_ renum_clocks g))
              inv;
        in
          (committeda, (urgenta, (transa, inva)))
        end);

fun rename_network A_ B_ E_ G_ broadcast bounds automata renum_acts renum_vars
  renum_clocks renum_states =
  let
    val automataa =
      map_index zero_nata
        (renum_automaton A_ B_ G_ E_ renum_acts renum_vars renum_clocks
          renum_states)
        automata;
    val broadcasta = map renum_acts broadcast;
    val boundsa = map (fn (a, (b, c)) => (renum_vars a, (b, c))) bounds;
  in
    (broadcasta, (automataa, boundsa))
  end;

fun action_set_impl (F1_, F2_, F3_) automata broadcast =
  set (F1_, F2_, F3_)
    (map act_sym
       (map (fn (_, (_, (_, (a, (_, (_, _)))))) => a)
         (foldl (fn a => fn x => a @ let
                                       val (_, (_, (trans, _))) = x;
                                     in
                                       trans
                                     end)
           [] automata)) @
      broadcast);

fun action_set (D1_, D2_, D3_) = action_set_impl (D1_, D2_, D3_);

fun loc_set (A1_, A2_, A3_) = loc_set_impl (A1_, A2_, A3_);

fun clk_set (C1_, C2_, C3_, C4_, C5_) =
  clk_set_impl (C1_, C2_, C3_, C4_, C5_)
    (ceq_int, ccompare_int, compare_int, equal_int, set_impl_int);

fun extend_domain A_ (B1_, B2_) m d n =
  let
    val (_, xs) =
      fold (fn x => fn (i, xs) =>
             (if membera A_ d x
               then (plus B2_ i (one B1_), (x, plus B2_ i (one B1_)) :: xs)
               else (i, xs)))
        d (n, []);
    val ma = map_of A_ xs;
  in
    (fn x => (if membera A_ d x then the (ma x) else m x))
  end;

fun mem_assoc A_ x = list_ex (fn (y, _) => eq A_ x y);

fun mk_renaming A_ str xs =
  binda (fold_error
          (fn x => fn m =>
            (if mem_assoc A_ x m then Error ["Duplicate name: " ^ str x]
              else Result ((x, size_list m) :: m)))
          xs [])
    (fn mapping =>
      Result
        let
          val m = map_of A_ mapping;
          val f =
            (fn x =>
              (case m x of NONE => raise Fail "empty case" | SOME v => v));
          val ma = map_of equal_nat (map swap mapping);
          val a =
            (fn x =>
              (case ma x of NONE => raise Fail "empty case" | SOME v => v));
        in
          (f, a)
        end);

fun mk_renaminga (A1_, A2_) xs =
  mk_renaming A1_ (implode o (fn x => shows_prec A2_ zero_nata x [])) xs;

fun list_of_set A_ xs = remdups A_ ((fn (Set_Monad xs) => xs | DList_set (Abs_dlist xs) => xs | RBT_set (Mapping_RBTa r) => rbt_to_list r | _ => raise Fail "Unsupported set implementation") xs);

fun vars_of_bexp (A1_, A2_, A3_) (Nota e) = vars_of_bexp (A1_, A2_, A3_) e
  | vars_of_bexp (A1_, A2_, A3_) (Anda (e1, e2)) =
    sup_seta (A1_, A2_) (vars_of_bexp (A1_, A2_, A3_) e1)
      (vars_of_bexp (A1_, A2_, A3_) e2)
  | vars_of_bexp (A1_, A2_, A3_) (Ora (e1, e2)) =
    sup_seta (A1_, A2_) (vars_of_bexp (A1_, A2_, A3_) e1)
      (vars_of_bexp (A1_, A2_, A3_) e2)
  | vars_of_bexp (A1_, A2_, A3_) (Imply (e1, e2)) =
    sup_seta (A1_, A2_) (vars_of_bexp (A1_, A2_, A3_) e1)
      (vars_of_bexp (A1_, A2_, A3_) e2)
  | vars_of_bexp (A1_, A2_, A3_) (Eqa (i, x)) =
    sup_seta (A1_, A2_) (vars_of_exp (A1_, A2_, A3_) i)
      (vars_of_exp (A1_, A2_, A3_) x)
  | vars_of_bexp (A1_, A2_, A3_) (Lea (i, x)) =
    sup_seta (A1_, A2_) (vars_of_exp (A1_, A2_, A3_) i)
      (vars_of_exp (A1_, A2_, A3_) x)
  | vars_of_bexp (A1_, A2_, A3_) (Ltb (i, x)) =
    sup_seta (A1_, A2_) (vars_of_exp (A1_, A2_, A3_) i)
      (vars_of_exp (A1_, A2_, A3_) x)
  | vars_of_bexp (A1_, A2_, A3_) (Ge (i, x)) =
    sup_seta (A1_, A2_) (vars_of_exp (A1_, A2_, A3_) i)
      (vars_of_exp (A1_, A2_, A3_) x)
  | vars_of_bexp (A1_, A2_, A3_) (Gta (i, x)) =
    sup_seta (A1_, A2_) (vars_of_exp (A1_, A2_, A3_) i)
      (vars_of_exp (A1_, A2_, A3_) x)
  | vars_of_bexp (A1_, A2_, A3_) True = bot_set (A1_, A2_, A3_)
and vars_of_exp (A1_, A2_, A3_) (Const c) = bot_set (A1_, A2_, A3_)
  | vars_of_exp (A1_, A2_, A3_) (Var x) =
    insert (A1_, A2_) x (bot_set (A1_, A2_, A3_))
  | vars_of_exp (A1_, A2_, A3_) (If_then_else (b, e1, e2)) =
    sup_seta (A1_, A2_)
      (sup_seta (A1_, A2_) (vars_of_bexp (A1_, A2_, A3_) b)
        (vars_of_exp (A1_, A2_, A3_) e1))
      (vars_of_exp (A1_, A2_, A3_) e2)
  | vars_of_exp (A1_, A2_, A3_) (Binop (uu, e1, e2)) =
    sup_seta (A1_, A2_) (vars_of_exp (A1_, A2_, A3_) e1)
      (vars_of_exp (A1_, A2_, A3_) e2)
  | vars_of_exp (A1_, A2_, A3_) (Unop (uv, e)) = vars_of_exp (A1_, A2_, A3_) e;

fun prop_TA_var_set_impl (E1_, E2_, E3_) (broadcast, (automata, bounds)) =
  sup_seta (E1_, E2_)
    (foldl (sup_seta (E1_, E2_)) (bot_set (E1_, E2_, E3_))
      (foldl
        (fn a => fn x =>
          a @ map (vars_of_bexp (E1_, E2_, E3_))
                (map (fn (_, (b, (_, (_, (_, (_, _)))))) => b)
                  let
                    val (_, (_, (trans, _))) = nth automata x;
                  in
                    trans
                  end))
        [] (upt zero_nata (size_list automata))))
    (foldl (sup_seta (E1_, E2_)) (bot_set (E1_, E2_, E3_))
      (foldl (fn a => fn b => a @ b) []
        (foldl
          (fn a => fn x =>
            a @ map (map (fn (xa, e) =>
                           sup_seta (E1_, E2_)
                             (insert (E1_, E2_) xa (bot_set (E1_, E2_, E3_)))
                             (vars_of_exp (E1_, E2_, E3_) e)))
                  (map (fn (_, (_, (_, (_, (u, (_, _)))))) => u)
                    let
                      val (_, (_, (trans, _))) = nth automata x;
                    in
                      trans
                    end))
          [] (upt zero_nata (size_list automata)))));

fun prod_TA_loc_set_impl (D1_, D2_, D3_) (broadcast, (automata, bounds)) =
  let
    val trans =
      map (fn p => let
                     val (_, (_, (trans, _))) = nth automata p;
                   in
                     trans
                   end)
        (upt zero_nata (size_list automata));
    val locs =
      foldl (sup_seta (D1_, D2_)) (bot_set (D1_, D2_, D3_))
        (foldl
          (fn a => fn x =>
            a @ map (fn (l, (_, (_, (_, (_, (_, la)))))) =>
                      insert (D1_, D2_) l
                        (insert (D1_, D2_) la (bot_set (D1_, D2_, D3_))))
                  x)
          [] trans);
  in
    locs
  end;

fun make_renaming (A1_, A2_, A3_, A4_, A5_) =
  (fn broadcast => fn automata => fn bounds =>
    let
      val action_seta =
        list_of_set equal_literal
          (action_set (ceq_literal, ccompare_literal, set_impl_literal) automata
            broadcast);
      val clk_seta =
        list_of_set equal_literal
          (clk_set
            (ceq_literal, ccompare_literal, compare_literal, equal_literal,
              set_impl_literal)
            automata);
      val clk_setb = clk_seta @ ["_urge"];
      val loc_seta =
        (fn i => list_of_set A3_ (loc_set (A1_, A2_, A4_) automata i));
      val loc_setaa =
        prod_TA_loc_set_impl (A1_, A2_, A4_) (broadcast, (automata, bounds));
      val loc_set_diff =
        (fn i =>
          list_of_set A3_
            (minus_set (A1_, A2_) loc_setaa
              (loc_set (A1_, A2_, A4_) automata i)));
      val _ = list_of_set A3_ loc_setaa;
      val var_set =
        list_of_set equal_literal
          (prop_TA_var_set_impl
            (ceq_literal, ccompare_literal, set_impl_literal)
            (broadcast, (automata, bounds)));
      val n_ps = size_list automata;
      val num_actions = size_list action_seta;
      val m = size_list (remdups equal_literal clk_setb);
      val num_states_list =
        map (fn i => size_list (remdups A3_ (loc_seta i))) (upt zero_nata n_ps);
      val num_states = nth num_states_list;
      val mk_renamingb = mk_renaming equal_literal (fn x => x);
    in
      binda (combine2 (mk_renamingb action_seta)
              (combine2 (mk_renamingb clk_setb) (mk_renamingb var_set)))
        (fn (a, b) =>
          let
            val (renum_acts, _) = a;
          in
            (fn (aa, ba) =>
              let
                val (renum_clocks, inv_renum_clocks) = aa;
              in
                (fn (renum_vars, inv_renum_vars) =>
                  let
                    val renum_clocksa = suc o renum_clocks;
                    val inv_renum_clocksa =
                      (fn c =>
                        (if equal_nata c zero_nata then "0"
                          else inv_renum_clocks (minus_nata c one_nata)));
                  in
                    binda (combine_map
                            (fn i => mk_renaminga (A3_, A5_) (loc_seta i))
                            (upt zero_nata n_ps))
                      (fn renum_states_list =>
                        let
                          val renum_states_lista = map fst renum_states_list;
                          val renum_states_listaa =
                            map_index zero_nata
                              (fn i => fn ma =>
                                extend_domain A3_ (one_nat, plus_nat) ma
                                  (loc_set_diff i) (size_list (loc_seta i)))
                              renum_states_lista;
                          val renum_states = nth renum_states_listaa;
                          val inv_renum_states =
                            nth (map snd renum_states_list);
                        in
                          binda (assert
                                  (less_eq_set
                                    (cenum_literal, ceq_literal,
                                      ccompare_literal)
                                    (image
                                      (ceq_prod ceq_literal
 (ceq_prod ceq_int ceq_int),
ccompare_prod ccompare_literal (ccompare_prod ccompare_int ccompare_int))
                                      (ceq_literal, ccompare_literal,
set_impl_literal)
                                      fst (set
    (ceq_prod ceq_literal (ceq_prod ceq_int ceq_int),
      ccompare_prod ccompare_literal (ccompare_prod ccompare_int ccompare_int),
      set_impl_prod set_impl_literal (set_impl_prod set_impl_int set_impl_int))
    bounds))
                                    (set (ceq_literal, ccompare_literal,
   set_impl_literal)
                                      var_set))
                                  "State variables are declared but do not appear in model")
                            (fn _ =>
                              Result
                                (m, (num_states,
                                      (num_actions,
(renum_acts,
  (renum_vars,
    (renum_clocksa,
      (renum_states,
        (inv_renum_states, (inv_renum_vars, inv_renum_clocksa))))))))))
                        end)
                  end)
              end
                ba)
          end
            b)
    end);

fun compute_model model renaming =
  let
    val (_, (_, (broadcast, (automata, (bounds, (formula, (l_0, s_0))))))) =
      model;
    val (renum_vars,
          (renum_clocks,
            (renum_states,
              (inv_renum_vars, (inv_renum_clocks, inv_renum_states)))))
      = renaming;
  in
    binda (make_renaming
            (ceq_nat, ccompare_nat, equal_nat, set_impl_nat, show_nat) broadcast
            automata bounds)
      (fn (m, (num_states,
                (num_actions, (renum_acts, (_, (_, (_, (_, (_, _)))))))))
         =>
        binda (assert (equal_nata (renum_clocks "_urge") m)
                "Given renaming: _urge is not last clock!")
          (fn _ =>
            let
              val _ = writeln "Renaming";
              val (broadcasta, (automataa, boundsa)) =
                rename_network countable_literal countable_literal countable_nat
                  countable_literal broadcast bounds automata renum_acts
                  renum_vars renum_clocks renum_states;
              val _ = writeln "Calculating ceiling";
              val k = local_ceiling broadcasta boundsa automataa m num_states;
              val urgent_locations =
                map (fn (_, (urgent, (_, _))) => urgent) automataa;
            in
              Result
                (broadcast,
                  (bounds,
                    (automata,
                      (urgent_locations,
                        (k, (l_0, (s_0, (formula,
  (m, (num_states,
        (num_actions,
          (renum_acts,
            (renum_vars,
              (renum_clocks,
                (renum_states,
                  (inv_renum_states,
                    (inv_renum_vars, inv_renum_clocks)))))))))))))))))
            end))
  end;

fun insert_every_nth n a xs =
  rev (snd (fold (fn x => fn (i, xsa) =>
                   (if equal_nata i n then (one_nata, a :: x :: xsa)
                     else (plus_nata i one_nata, x :: xsa)))
             xs (one_nata, [])));

fun fw_upd_impl_inta x =
  (fn n => fn ai => fn bib => fn bia => fn bi =>
    (fn f_ => fn () => f_
      ((mtx_get (heap_DBMEntry heap_int) (suc n) ai (bia, bib)) ()) ())
      (fn xa =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) ai (bib, bi)) ()) ())
          (fn xaa =>
            let
              val xb = dbm_add_int xa xaa;
            in
              (fn f_ => fn () => f_
                ((mtx_get (heap_DBMEntry heap_int) (suc n) ai (bia, bi)) ()) ())
                (fn xab =>
                  (if less_DBMEntry linorder_int xb xab
                    then mtx_set (heap_DBMEntry heap_int) (suc n) ai (bia, bi)
                           xb
                    else (fn () => ai)))
            end)))
    x;

fun fw_impl_inta x =
  (fn n =>
    imp_for_inta zero_nata (plus_nata n one_nata)
      (fn xb =>
        imp_for_inta zero_nata (plus_nata n one_nata)
          (fn xd =>
            imp_for_inta zero_nata (plus_nata n one_nata)
              (fn xf => fn sigma => fw_upd_impl_inta n sigma xb xd xf))))
    x;

fun normalize_dbm m xs =
  (fn f => f ()) ((fn f_ => fn () => f_ (((fn () => Array.fromList xs)) ()) ())
                   (fn dbm =>
                     (fn f_ => fn () => f_ ((fw_impl_inta m dbm) ()) ())
                       (freeze (heap_DBMEntry heap_int))));

fun convert_dbm urge m dbm =
  normalize_dbm m
    (take m dbm @
      Le zero_inta ::
        insert_every_nth m INF (drop m dbm) @
          (if urge then Le zero_inta else INF) ::
            replicate (minus_nata m one_nata) INF @ [Le zero_inta]);

fun convert_state_space m is_urgent (Reachable_Set xs) =
  Reachable_Set
    (map (fn (a, b) =>
           let
             val (locs, vars) = a;
           in
             (fn dbms =>
               ((map nat locs, vars),
                 map (convert_dbm (is_urgent (locs, vars)) m) dbms))
           end
             b)
      xs)
  | convert_state_space m is_urgent (Buechi_Set xs) =
    Buechi_Set
      (map (fn (a, b) =>
             let
               val (locs, vars) = a;
             in
               (fn dbms =>
                 ((map nat locs, vars),
                   map (fn (dbm, aa) =>
                         (convert_dbm (is_urgent (locs, vars)) m dbm, aa))
                     dbms))
             end
               b)
        xs);

fun len_of_state_space (Reachable_Set xs) = size_list xs
  | len_of_state_space (Buechi_Set xs) = size_list xs;

fun show_clock B_ inv_renum_clocks =
  (fn x => shows_prec B_ zero_nata x []) o inv_renum_clocks;

fun make_string (A1_, A2_, A3_) show_clock show_num e i j =
  (if equal_nata i j
    then (if less_DBMEntry
               ((linorder_linordered_ab_semigroup_add o
                  linordered_ab_semigroup_add_linordered_ab_monoid_add o
                  linordered_ab_monoid_add_linordered_cancel_ab_monoid_add o
                  linordered_cancel_ab_monoid_add_linordered_ab_group_add)
                 A1_)
               e (zero_DBMEntrya
                   ((zero_monoid_add o monoid_add_group_add o
                      group_add_ab_group_add o
                      ab_group_add_ordered_ab_group_add o
                      ordered_ab_group_add_linordered_ab_group_add)
                     A1_))
           then SOME [Chara (true, false, true, false, false, false, true,
                              false),
                       Chara (true, false, true, true, false, false, true,
                               false),
                       Chara (false, false, false, false, true, false, true,
                               false),
                       Chara (false, false, true, false, true, false, true,
                               false),
                       Chara (true, false, false, true, true, false, true,
                               false)]
           else NONE)
    else (if equal_nata i zero_nata
           then (case e
                  of Le a =>
                    (if eq A2_ a
                          (zero ((zero_monoid_add o monoid_add_group_add o
                                   group_add_ab_group_add o
                                   ab_group_add_ordered_ab_group_add o
                                   ordered_ab_group_add_linordered_ab_group_add)
                                  A1_))
                      then NONE
                      else SOME (show_clock j @
                                  [Chara (false, false, false, false, false,
   true, false, false),
                                    Chara (false, true, true, true, true, true,
    false, false),
                                    Chara (true, false, true, true, true, true,
    false, false),
                                    Chara (false, false, false, false, false,
    true, false, false)] @
                                    show_num
                                      (uminus
((uminus_group_add o group_add_ab_group_add o
   ab_group_add_ordered_ab_group_add o
   ordered_ab_group_add_linordered_ab_group_add)
  A1_)
a)))
                  | Lt a =>
                    SOME (show_clock j @
                           [Chara (false, false, false, false, false, true,
                                    false, false),
                             Chara (false, true, true, true, true, true, false,
                                     false),
                             Chara (false, false, false, false, false, true,
                                     false, false)] @
                             show_num
                               (uminus
                                 ((uminus_group_add o group_add_ab_group_add o
                                    ab_group_add_ordered_ab_group_add o
                                    ordered_ab_group_add_linordered_ab_group_add)
                                   A1_)
                                 a))
                  | INF => NONE)
           else (if equal_nata j zero_nata
                  then (case e
                         of Le a =>
                           SOME (show_clock i @
                                  [Chara (false, false, false, false, false,
   true, false, false),
                                    Chara (false, false, true, true, true, true,
    false, false),
                                    Chara (true, false, true, true, true, true,
    false, false),
                                    Chara (false, false, false, false, false,
    true, false, false)] @
                                    show_num a)
                         | Lt a =>
                           SOME (show_clock i @
                                  [Chara (false, false, false, false, false,
   true, false, false),
                                    Chara (false, false, true, true, true, true,
    false, false),
                                    Chara (false, false, false, false, false,
    true, false, false)] @
                                    show_num a)
                         | INF => NONE)
                  else (case e
                         of Le a =>
                           SOME (show_clock i @
                                  [Chara (false, false, false, false, false,
   true, false, false),
                                    Chara (true, false, true, true, false, true,
    false, false),
                                    Chara (false, false, false, false, false,
    true, false, false)] @
                                    show_clock j @
                                      [Chara
 (false, false, false, false, false, true, false, false),
Chara (false, false, true, true, true, true, false, false),
Chara (true, false, true, true, true, true, false, false),
Chara (false, false, false, false, false, true, false, false)] @
show_num a)
                         | Lt a =>
                           SOME (show_clock i @
                                  [Chara (false, false, false, false, false,
   true, false, false),
                                    Chara (true, false, true, true, false, true,
    false, false),
                                    Chara (false, false, false, false, false,
    true, false, false)] @
                                    show_clock j @
                                      [Chara
 (false, false, false, false, false, true, false, false),
Chara (false, false, true, true, true, true, false, false),
Chara (false, false, false, false, false, true, false, false)] @
show_num a)
                         | INF => NONE))));

fun dbm_list_to_string (A1_, A2_, A3_) n show_clock show_num xs =
  app (concat o
         intersperse
           [Chara (false, false, true, true, false, true, false, false),
             Chara (false, false, false, false, false, true, false, false)] o
         rev o
         snd o
        snd)
    (fold (fn e => fn (i, (j, acc)) =>
            let
              val v = make_string (A1_, A2_, A3_) show_clock show_num e i j;
              val ja = modulo_nat (plus_nata j one_nata) (plus_nata n one_nata);
              val ia =
                (if equal_nata ja zero_nata then plus_nata i one_nata else i);
            in
              (case v of NONE => (ia, (ja, acc))
                | SOME s => (ia, (ja, s :: acc)))
            end)
      xs (zero_nata, (zero_nata, [])));

fun show_dbm num_clocks inv_renum_clocks =
  dbm_list_to_string (linordered_ab_group_add_int, equal_int, heap_int)
    num_clocks (show_clock show_literal inv_renum_clocks)
    (fn x => shows_prec_int zero_nata x []);

fun show_vars A_ B_ inv_renum_vars =
  (fn x => shows_prec_list (show_list show_char) zero_nata x []) o
    map_index zero_nata
      (fn i => fn v =>
        shows_prec A_ zero_nata (inv_renum_vars i) [] @
          [Chara (true, false, true, true, true, true, false, false)] @
            shows_prec B_ zero_nata v []);

fun show_locs B_ inv_renum_states =
  (fn x => shows_prec_list B_ zero_nata x []) o
    map_index zero_nata inv_renum_states;

fun show_state B_ C_ D_ inv_renum_states inv_renum_vars =
  (fn (l, vs) =>
    let
      val la = show_locs B_ inv_renum_states l;
      val vsa = show_vars C_ D_ inv_renum_vars vs;
    in
      [Chara (false, false, true, true, true, true, false, false)] @
        la @ [Chara (false, true, true, true, true, true, false, false),
               Chara (false, false, true, true, false, true, false, false),
               Chara (false, false, false, false, false, true, false, false),
               Chara (false, false, true, true, true, true, false, false)] @
               vsa @ [Chara (false, true, true, true, true, true, false, false)]
    end);

fun show_st A_ inv_renum_states inv_renum_vars =
  show_state show_nat show_literal A_ inv_renum_states inv_renum_vars;

fun show_state_space num_clocks inv_renum_states inv_renum_vars inv_renum_clocks
  (Reachable_Set xs) =
  map (fn (l, a) =>
        map (fn x =>
              writeln (implode
                        ([Chara (false, false, false, true, false, true, false,
                                  false)] @
                          show_st show_int inv_renum_states inv_renum_vars l @
                            [Chara (false, false, true, true, false, true,
                                     false, false),
                              Chara (false, false, false, false, false, true,
                                      false, false),
                              Chara (false, false, true, true, true, true,
                                      false, false)] @
                              show_dbm num_clocks inv_renum_clocks x @
                                [Chara (false, true, true, true, true, true,
 false, false),
                                  Chara (true, false, false, true, false, true,
  false, false)])))
          a)
    xs
  | show_state_space num_clocks inv_renum_states inv_renum_vars inv_renum_clocks
    (Buechi_Set xs) =
    map (fn (l, a) =>
          map (fn (x, i) =>
                writeln (implode
                          (shows_prec_nat zero_nata i [] @
                            [Chara (false, true, false, true, true, true, false,
                                     false),
                              Chara (false, false, false, false, false, true,
                                      false, false),
                              Chara (false, false, false, true, false, true,
                                      false, false)] @
                              show_st show_int inv_renum_states inv_renum_vars
                                l @
                                [Chara (false, false, true, true, false, true,
 false, false),
                                  Chara (false, false, false, false, false,
  true, false, false),
                                  Chara (false, false, true, true, true, true,
  false, false)] @
                                  show_dbm num_clocks inv_renum_clocks x @
                                    [Chara (false, true, true, true, true, true,
     false, false),
                                      Chara
(true, false, false, true, false, true, false, false)])))
            a)
      xs;

fun print_sep x =
  (fn () =>
    writeln (implode
              (replicate (nat_of_integer (100 : Int.int))
                (Chara (true, false, true, true, false, true, false, false)))))
    x;

fun show_lit A_ = implode o (fn x => shows_prec A_ zero_nata x []);

fun vars_of_sexp (C1_, C2_, C3_) (Notb e) = vars_of_sexp (C1_, C2_, C3_) e
  | vars_of_sexp (C1_, C2_, C3_) (Andb (e1, e2)) =
    sup_seta (C1_, C2_) (vars_of_sexp (C1_, C2_, C3_) e1)
      (vars_of_sexp (C1_, C2_, C3_) e2)
  | vars_of_sexp (C1_, C2_, C3_) (Orb (e1, e2)) =
    sup_seta (C1_, C2_) (vars_of_sexp (C1_, C2_, C3_) e1)
      (vars_of_sexp (C1_, C2_, C3_) e2)
  | vars_of_sexp (C1_, C2_, C3_) (Implya (e1, e2)) =
    sup_seta (C1_, C2_) (vars_of_sexp (C1_, C2_, C3_) e1)
      (vars_of_sexp (C1_, C2_, C3_) e2)
  | vars_of_sexp (C1_, C2_, C3_) (Eqb (i, x)) =
    insert (C1_, C2_) i (bot_set (C1_, C2_, C3_))
  | vars_of_sexp (C1_, C2_, C3_) (Ltc (i, x)) =
    insert (C1_, C2_) i (bot_set (C1_, C2_, C3_))
  | vars_of_sexp (C1_, C2_, C3_) (Leb (i, x)) =
    insert (C1_, C2_) i (bot_set (C1_, C2_, C3_))
  | vars_of_sexp (C1_, C2_, C3_) (Gea (i, x)) =
    insert (C1_, C2_) i (bot_set (C1_, C2_, C3_))
  | vars_of_sexp (C1_, C2_, C3_) (Gtb (i, x)) =
    insert (C1_, C2_) i (bot_set (C1_, C2_, C3_))
  | vars_of_sexp (C1_, C2_, C3_) Truea = bot_set (C1_, C2_, C3_)
  | vars_of_sexp (C1_, C2_, C3_) (Loc (v, va)) = bot_set (C1_, C2_, C3_);

fun vars_of_formula (C1_, C2_, C3_) (EX phi) = vars_of_sexp (C1_, C2_, C3_) phi
  | vars_of_formula (C1_, C2_, C3_) (EG phi) = vars_of_sexp (C1_, C2_, C3_) phi
  | vars_of_formula (C1_, C2_, C3_) (AX phi) = vars_of_sexp (C1_, C2_, C3_) phi
  | vars_of_formula (C1_, C2_, C3_) (AG phi) = vars_of_sexp (C1_, C2_, C3_) phi
  | vars_of_formula (C1_, C2_, C3_) (Leadsto (phi, psi)) =
    sup_seta (C1_, C2_) (vars_of_sexp (C1_, C2_, C3_) phi)
      (vars_of_sexp (C1_, C2_, C3_) psi);

fun atLeastLessThan (A1_, A2_, A3_, A4_, A5_) a b =
  let
    val d =
      minusa
        ((minus_cancel_ab_semigroup_add o
           cancel_ab_semigroup_add_cancel_comm_monoid_add o
           cancel_comm_monoid_add_semiring_0_cancel o
           semiring_0_cancel_semiring_1_cancel o
           semiring_1_cancel_comm_semiring_1_cancel o
           comm_semiring_1_cancel_interval)
          A4_)
        b (one ((one_numeral o numeral_semiring_numeral o
                  semiring_numeral_semiring_1 o semiring_1_comm_semiring_1 o
                  comm_semiring_1_comm_semiring_1_cancel o
                  comm_semiring_1_cancel_interval)
                 A4_));
  in
    (if less ((ord_preorder o preorder_order o order_linorder o
                linorder_interval)
               A4_)
          d b
      then set (A1_, A2_, A5_) (interval (A3_, A4_) a d)
      else bot_set (A1_, A2_, A5_))
  end;

fun simple_Network_Impl_nat_ceiling_start_state_axioms x =
  (fn _ => fn bounds => fn automata => fn m => fn num_states => fn k =>
    fn l_0 => fn s_0 => fn formula =>
    let
      val d = minus_nata (size_list automata) one_nata;
    in
      (if less_nat d (size_list automata)
        then all_interval (equal_nat, interval_nat)
               (fn i =>
                 list_all
                   (fn (l, g) =>
                     ball (ceq_prod ceq_nat ceq_int,
                            ccompare_prod ccompare_nat ccompare_int)
                       (collect_clock_pairs
                         (ceq_nat, ccompare_nat, compare_nat, equal_nat,
                           set_impl_nat)
                         (ceq_int, ccompare_int, compare_int, equal_int,
                           set_impl_int)
                         g)
                       (fn (xa, ma) =>
                         less_eq_int ma
                           (int_of_nat (nth (nth (nth k i) l) xa))))
                   ((snd o snd o snd) (nth automata i)))
               zero_nata d
        else true)
    end andalso
      (let
         val d = minus_nata (size_list automata) one_nata;
       in
         (if less_nat d (size_list automata)
           then all_interval (equal_nat, interval_nat)
                  (fn i =>
                    list_all
                      (fn (l, (_, (g, _))) =>
                        ball (ceq_prod ceq_nat ceq_int,
                               ccompare_prod ccompare_nat ccompare_int)
                          (collect_clock_pairs
                            (ceq_nat, ccompare_nat, compare_nat, equal_nat,
                              set_impl_nat)
                            (ceq_int, ccompare_int, compare_int, equal_int,
                              set_impl_int)
                            g)
                          (fn (xa, ma) =>
                            less_eq_int ma
                              (int_of_nat (nth (nth (nth k i) l) xa))))
                      ((fst o snd o snd) (nth automata i)))
                  zero_nata d
           else true)
       end andalso
        let
          val d = minus_nata (size_list automata) one_nata;
        in
          (if less_nat d (size_list automata)
            then all_interval (equal_nat, interval_nat)
                   (fn i =>
                     list_all
                       (fn (l, (_, (_, (_, (_, (r, la)))))) =>
                         ball (ceq_nat, ccompare_nat)
                           (minus_set (ceq_nat, ccompare_nat)
                             (atLeastLessThan
                               (ceq_nat, ccompare_nat, equal_nat, interval_nat,
                                 set_impl_nat)
                               zero_nata (plus_nata m one_nata))
                             (set (ceq_nat, ccompare_nat, set_impl_nat) r))
                           (fn c =>
                             less_eq_nat (nth (nth (nth k i) la) c)
                               (nth (nth (nth k i) l) c)))
                       ((fst o snd o snd) (nth automata i)))
                   zero_nata d
            else true)
        end) andalso
      (equal_nata (size_list k) (size_list automata) andalso
        (let
           val d = minus_nata (size_list automata) one_nata;
         in
           (if less_nat d (size_list automata)
             then all_interval (equal_nat, interval_nat)
                    (fn i => equal_nata (size_list (nth k i)) (num_states i))
                    zero_nata d
             else true)
         end andalso
          list_all
            (list_all
              (fn xxs => equal_nata (size_list xxs) (plus_nata m one_nata)))
            k)) andalso
      (let
         val d = minus_nata (size_list automata) one_nata;
       in
         (if less_nat d (size_list automata)
           then all_interval (equal_nat, interval_nat)
                  (fn i =>
                    let
                      val da = minus_nata (num_states i) one_nata;
                    in
                      (if less_nat da (num_states i)
                        then all_interval (equal_nat, interval_nat)
                               (fn l =>
                                 equal_nata (nth (nth (nth k i) l) zero_nata)
                                   zero_nata)
                               zero_nata da
                        else true)
                    end)
                  zero_nata d
           else true)
       end andalso
         (list_all
            (fn (_, (_, (_, inv))) =>
              distinct_ds (equal_nat, linorder_nat) (map fst inv))
            automata andalso
           (set_eq (cenum_nat, ceq_nat, ccompare_nat)
              (image
                (ceq_prod ceq_nat ceq_int,
                  ccompare_prod ccompare_nat ccompare_int)
                (ceq_nat, ccompare_nat, set_impl_nat) fst
                (set (ceq_prod ceq_nat ceq_int,
                       ccompare_prod ccompare_nat ccompare_int,
                       set_impl_prod set_impl_nat set_impl_int)
                  s_0))
              (image
                (ceq_prod ceq_nat (ceq_prod ceq_int ceq_int),
                  ccompare_prod ccompare_nat
                    (ccompare_prod ccompare_int ccompare_int))
                (ceq_nat, ccompare_nat, set_impl_nat) fst
                (set (ceq_prod ceq_nat (ceq_prod ceq_int ceq_int),
                       ccompare_prod ccompare_nat
                         (ccompare_prod ccompare_int ccompare_int),
                       set_impl_prod set_impl_nat
                         (set_impl_prod set_impl_int set_impl_int))
                  bounds)) andalso
             ball (ceq_nat, ccompare_nat)
               (image
                 (ceq_prod ceq_nat ceq_int,
                   ccompare_prod ccompare_nat ccompare_int)
                 (ceq_nat, ccompare_nat, set_impl_nat) fst
                 (set (ceq_prod ceq_nat ceq_int,
                        ccompare_prod ccompare_nat ccompare_int,
                        set_impl_prod set_impl_nat set_impl_int)
                   s_0))
               (fn xa =>
                 less_eq_int (fst (the (map_of equal_nat bounds xa)))
                   (the (map_of equal_nat s_0 xa)) andalso
                   less_eq_int (the (map_of equal_nat s_0 xa))
                     (snd (the (map_of equal_nat bounds xa)))))) andalso
        (equal_nata (size_list l_0) (size_list automata) andalso
          (let
             val d = minus_nata (size_list automata) one_nata;
           in
             (if less_nat d (size_list automata)
               then all_interval (equal_nat, interval_nat)
                      (fn i =>
                        membera equal_nat
                          (map fst ((fst o snd o snd) (nth automata i)))
                          (nth l_0 i))
                      zero_nata d
               else true)
           end andalso
            less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
              (vars_of_formula (ceq_nat, ccompare_nat, set_impl_nat) formula)
              (atLeastLessThan
                (ceq_nat, ccompare_nat, equal_nat, interval_nat, set_impl_nat)
                zero_nata (size_list bounds))))))
    x;

fun simple_Network_Impl_nat_urge_axioms automata =
  list_all (fn (_, (u, (_, _))) => null u) automata;

fun n_vs bounds = size_list bounds;

fun simple_Network_Impl_nat broadcast bounds automata m num_states num_actions =
  less_nat zero_nata m andalso
    (less_nat zero_nata (size_list automata) andalso
      let
        val d = minus_nata (size_list automata) one_nata;
      in
        (if less_nat d (size_list automata)
          then all_interval (equal_nat, interval_nat)
                 (fn i =>
                   let
                     val (_, (_, (trans, _))) = nth automata i;
                   in
                     list_all
                       (fn (l, (_, (_, (_, (_, (_, la)))))) =>
                         less_nat l (num_states i) andalso
                           less_nat la (num_states i))
                       trans
                   end)
                 zero_nata d
          else true)
      end) andalso
    (let
       val d = minus_nata (size_list automata) one_nata;
     in
       (if less_nat d (size_list automata)
         then all_interval (equal_nat, interval_nat)
                (fn i => let
                           val (_, (_, (_, a))) = nth automata i;
                         in
                           list_all (fn (x, _) => less_nat x (num_states i)) a
                         end)
                zero_nata d
         else true)
     end andalso
      (list_all
         (fn (_, (_, (trans, _))) =>
           list_all
             (fn (_, (_, (_, (_, (f, (_, _)))))) =>
               list_all
                 (fn (x, upd) =>
                   less_nat x (n_vs bounds) andalso
                     ball (ceq_nat, ccompare_nat)
                       (vars_of_exp (ceq_nat, ccompare_nat, set_impl_nat) upd)
                       (fn i => less_nat i (n_vs bounds)))
                 f)
             trans)
         automata andalso
        list_all
          (fn (_, (_, (trans, _))) =>
            list_all
              (fn (_, (b, (_, (_, (_, (_, _)))))) =>
                ball (ceq_nat, ccompare_nat)
                  (vars_of_bexp (ceq_nat, ccompare_nat, set_impl_nat) b)
                  (fn i => less_nat i (n_vs bounds)))
              trans)
          automata)) andalso
    (let
       val d = minus_nata (n_vs bounds) one_nata;
     in
       (if less_nat d (n_vs bounds)
         then all_interval (equal_nat, interval_nat)
                (fn i => equal_nata (fst (nth bounds i)) i) zero_nata d
         else true)
     end andalso
       (list_all (fn a => less_nat a num_actions) broadcast andalso
         list_all
           (fn (_, (_, (trans, _))) =>
             list_all
               (fn (_, (_, (_, (a, (_, (_, _)))))) =>
                 pred_act (ceq_nat, ccompare_nat, set_impl_nat)
                   (fn aa => less_nat aa num_actions) a)
               trans)
           automata) andalso
      (list_all
         (fn (_, (_, (trans, _))) =>
           list_all
             (fn (_, (_, (g, (_, (_, (r, _)))))) =>
               list_all (fn c => less_nat zero_nata c andalso less_eq_nat c m)
                 r andalso
                 ball (ceq_prod ceq_nat ceq_int,
                        ccompare_prod ccompare_nat ccompare_int)
                   (collect_clock_pairs
                     (ceq_nat, ccompare_nat, compare_nat, equal_nat,
                       set_impl_nat)
                     (ceq_int, ccompare_int, compare_int, equal_int,
                       set_impl_int)
                     g)
                   (fn (c, x) =>
                     less_nat zero_nata c andalso
                       (less_eq_nat c m andalso less_eq_int zero_inta x)))
             trans)
         automata andalso
        (list_all
           (fn (_, (_, (_, a))) =>
             list_all
               (fn (_, g) =>
                 ball (ceq_prod ceq_nat ceq_int,
                        ccompare_prod ccompare_nat ccompare_int)
                   (collect_clock_pairs
                     (ceq_nat, ccompare_nat, compare_nat, equal_nat,
                       set_impl_nat)
                     (ceq_int, ccompare_int, compare_int, equal_int,
                       set_impl_int)
                     g)
                   (fn (c, x) =>
                     less_nat zero_nata c andalso
                       (less_eq_nat c m andalso less_eq_int zero_inta x)))
               a)
           automata andalso
          list_all
            (fn (_, (_, (trans, _))) =>
              list_all
                (fn a =>
                  (case a
                    of (_, (_, (g, (In aa, (_, (_, _)))))) =>
                      (if membera equal_nat broadcast aa then null g else true)
                    | (_, (_, (_, (Out _, (_, (_, _)))))) => true
                    | (_, (_, (_, (Sil _, (_, (_, _)))))) => true))
                trans)
            automata)));

fun simple_Network_Impl_nat_urge broadcast bounds automata m num_states
  num_actions =
  simple_Network_Impl_nat broadcast bounds automata m num_states
    num_actions andalso
    simple_Network_Impl_nat_urge_axioms automata;

fun simple_Network_Impl_nat_ceiling_start_state broadcast bounds automata m
  num_states num_actions k l_0 s_0 formula =
  simple_Network_Impl_nat_urge broadcast bounds automata m num_states
    num_actions andalso
    simple_Network_Impl_nat_ceiling_start_state_axioms broadcast bounds automata
      m num_states k l_0 s_0 formula;

fun bounds_map bounds = the o map_of equal_nat bounds;

fun check_boundedi bounds s =
  let
    val d = minus_nata (size_list s) one_nata;
  in
    (if less_nat d (size_list s)
      then all_interval (equal_nat, interval_nat)
             (fn x =>
               less_eq_int (fst (bounds_map bounds x)) (nth s x) andalso
                 less_eq_int (nth s x) (snd (bounds_map bounds x)))
             zero_nata d
      else true)
  end;

fun states_i x =
  (fn automata => fn i =>
    sup_setb
      (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat, set_impl_nat)
      (set (ceq_set
              (cenum_nat, ceq_nat,
                ccompare_cproper_interval cproper_interval_nat),
             ccompare_set
               (finite_UNIV_nat, ceq_nat, cproper_interval_nat, set_impl_nat),
             set_impl_set)
        (map (fn (l, (_, (_, (_, (_, (_, la)))))) =>
               insert (ceq_nat, ccompare_nat) l
                 (insert (ceq_nat, ccompare_nat) la
                   (set_empty (ceq_nat, ccompare_nat)
                     (of_phantom set_impl_nata))))
          (fst (snd (snd (nth automata i)))))))
    x;

fun print_fail s b =
  (if b then () else writeln (s ^ " precondition check failed!"));

fun certificate_checker_pre1 l_list m_list broadcast bounds automata m
  num_states num_actions k l_0 s_0 formula =
  let
    val _ = Timing.start_timer ();
    val check1 =
      simple_Network_Impl_nat_ceiling_start_state broadcast bounds automata m
        num_states num_actions k l_0 s_0 formula;
    val _ = Timing.save_time "Time to check ceiling";
    val n_ps = size_list automata;
    val n_vsa = n_vs bounds;
    val states_ia = map (states_i automata) (upt zero_nata n_ps);
    val _ = Timing.start_timer ();
    val check2 =
      list_all
        (fn (l, s) =>
          equal_nata (size_list l) n_ps andalso
            (let
               val d = minus_nata n_ps one_nata;
             in
               (if less_nat d n_ps
                 then all_interval (equal_nat, interval_nat)
                        (fn i =>
                          member (ceq_nat, ccompare_nat) (nth l i)
                            (nth states_ia i))
                        zero_nata d
                 else true)
             end andalso
              (equal_nata (size_list s) n_vsa andalso check_boundedi bounds s)))
        l_list;
    val _ = Timing.save_time "Time to check states";
    val _ = Timing.start_timer ();
    val n_sq = times_nata (suc m) (suc m);
    val check3 =
      list_all
        (fn (_, a) => list_all (fn (ma, _) => equal_nata (size_list ma) n_sq) a)
        m_list;
    val _ = Timing.save_time "Time to check DBMs";
    val check4 =
      (case formula of EX _ => true | EG _ => false | AX _ => false
        | AG _ => false | Leadsto (_, _) => false);
    val _ =
      map (fn (a, b) => print_fail a b)
        [("Ceiling", check1), ("States", check2), ("DBM", check3),
          ("Formula", check4)];
  in
    check1 andalso (check2 andalso (check3 andalso check4))
  end;

fun dbm_lt_0 (Le x) = less_int x zero_inta
  | dbm_lt_0 (Lt x) = less_eq_int x zero_inta
  | dbm_lt_0 INF = false;

fun imp_for_int_inner i u c f s =
  (if u <= i then (fn () => s)
    else (fn f_ => fn () => f_ ((c s) ()) ())
           (fn ctn =>
             (if ctn
               then (fn f_ => fn () => f_ ((f i s) ()) ())
                      (imp_for_int_inner (i + (1 : Int.int)) u c f)
               else (fn () => s))));

fun imp_for_int i u c f s =
  imp_for_int_inner (integer_of_nat i) (integer_of_nat u) c (f o nat_of_integer)
    s;

fun check_diag_impl_int x =
  (fn n => fn xi =>
    imp_for_int zero_nata (suc n) (fn sigma => (fn () => (not sigma)))
      (fn xc => fn sigma =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) xi (xc, xc)) ()) ())
          (fn xa => (fn () => (dbm_lt_0 xa orelse sigma))))
      false)
    x;

fun hashmap_of_list (A1_, A2_) m =
  fold (fn (a, b) => ahm_update (eq A1_) (bounded_hashcode_nat A2_) a b) m
    (ahm_empty (def_hashmap_size A2_ Type));

fun array_unfreeze A_ a =
  (fn a => fn () =>
  if Vector.length a = 0
  then Array.fromList []
  else
    let
      val x = Vector.sub(a, 0)
      val n = Array.array (Vector.length a, x)
      val _ = Array.copyVec {src=a,dst=n,di=0}
    in n end
) a;

fun array_freeze A_ a = (fn () => Array.vector a);

fun certify_no_buechi_run_pure get_succs li lei li_split pi fi mi initsi =
  let
    val check_all_pre_impl =
      time_it "Time for state set preconditions check"
        (fn _ =>
          let
            val b =
              list_all
                (fn (l_0, s_0) =>
                  (case mi l_0 of NONE => false
                    | SOME xs =>
                      not (is_none (mi l_0)) andalso
                        (pi (l_0, s_0) andalso
                          list_ex (fn (s, _) => lei s_0 s) xs)))
                initsi;
            val _ = print_check "Initial state check" b;
          in
            b
          end andalso
            let
              val b =
                list_all id
                  (Par_List.map
                    (fn l =>
                      (case op_map_lookup l mi of NONE => true
                        | SOME a => list_all (fn (s, _) => pi (l, s)) a))
                    li);
              val _ = print_check "State set preconditions check" b;
            in
              b
            end);
    val check_invariant =
      time_it "Time for state space invariant check"
        (fn _ =>
          list_all id
            (Par_List.map
              (list_all
                (fn l =>
                  (case mi l of NONE => true
                    | SOME a =>
                      list_all
                        (fn (x, i) =>
                          list_all
                            (fn (la, xs) =>
                              (if null xs then true
                                else (case mi la of NONE => false
                                       | SOME ys =>
 list_all
   (fn y =>
     list_ex
       (fn (z, j) =>
         lei y z andalso (if fi (l, x) then less_nat i else less_eq_nat i) j)
       ys)
   xs)))
                            (get_succs l [x]))
                        a)))
              li_split));
  in
    (if check_all_pre_impl
      then let
             val b = check_invariant;
             val _ = print_check "State space invariant check" b;
           in
             b
           end
      else false)
  end;

fun evali (A1_, A2_) s (Const c) = c
  | evali (A1_, A2_) s (Var x) = nth s x
  | evali (A1_, A2_) s (If_then_else (b, e1, e2)) =
    (if bvali (A1_, A2_) s b then evali (A1_, A2_) s e1
      else evali (A1_, A2_) s e2)
  | evali (A1_, A2_) s (Binop (f, e1, e2)) =
    f (evali (A1_, A2_) s e1) (evali (A1_, A2_) s e2)
  | evali (A1_, A2_) s (Unop (f, e)) = f (evali (A1_, A2_) s e)
and bvali (A1_, A2_) s True = true
  | bvali (A1_, A2_) s (Nota e) = not (bvali (A1_, A2_) s e)
  | bvali (A1_, A2_) s (Anda (e1, e2)) =
    bvali (A1_, A2_) s e1 andalso bvali (A1_, A2_) s e2
  | bvali (A1_, A2_) s (Ora (e1, e2)) =
    bvali (A1_, A2_) s e1 orelse bvali (A1_, A2_) s e2
  | bvali (A1_, A2_) s (Imply (e1, e2)) =
    (if bvali (A1_, A2_) s e1 then bvali (A1_, A2_) s e2 else true)
  | bvali (A1_, A2_) s (Eqa (i, x)) =
    eq A1_ (evali (A1_, A2_) s i) (evali (A1_, A2_) s x)
  | bvali (A1_, A2_) s (Lea (i, x)) =
    less_eq ((ord_preorder o preorder_order o order_linorder) A2_)
      (evali (A1_, A2_) s i) (evali (A1_, A2_) s x)
  | bvali (A1_, A2_) s (Ltb (i, x)) =
    less ((ord_preorder o preorder_order o order_linorder) A2_)
      (evali (A1_, A2_) s i) (evali (A1_, A2_) s x)
  | bvali (A1_, A2_) s (Ge (i, x)) =
    less_eq ((ord_preorder o preorder_order o order_linorder) A2_)
      (evali (A1_, A2_) s x) (evali (A1_, A2_) s i)
  | bvali (A1_, A2_) s (Gta (i, x)) =
    less ((ord_preorder o preorder_order o order_linorder) A2_)
      (evali (A1_, A2_) s x) (evali (A1_, A2_) s i);

fun mk_updsi s upds =
  fold (fn (x, upd) => fn sa =>
         list_update sa x (evali (equal_int, linorder_int) sa upd))
    upds s;

fun pairs_by_action_impl bounds l s out ina =
  maps (fn (p, (b1, (g1, (a1, (f1, (r1, l1)))))) =>
         map_filter
           (fn (q, (b2, (g2, (_, (f2, (r2, l2)))))) =>
             (if equal_nata p q then NONE
               else let
                      val sa = mk_updsi (mk_updsi s f1) f2;
                    in
                      (if bvali (equal_int, linorder_int) s b1 andalso
                            (bvali (equal_int, linorder_int) s b2 andalso
                              check_boundedi bounds sa)
                        then SOME (g1 @ g2,
                                    (Bin a1,
                                      (r1 @ r2,
(list_update (list_update l p l1) q l2, sa))))
                        else NONE)
                    end))
           out)
    ina;

fun actions_by_state i =
  fold (fn t => fn acc =>
         list_update acc (fst (snd (snd t)))
           ((i, t) :: nth acc (fst (snd (snd t)))));

fun all_actions_from_vec num_actions t vec =
  fold (fn (p, l) => actions_by_state p (t p l)) vec
    (map (fn _ => []) (upt zero_nata num_actions));

fun all_actions_by_state broadcast bounds automata num_actions t l =
  fold (fn i => actions_by_state i (t i (nth l i)))
    (upt zero_nata (size_list automata))
    (map (fn _ => []) (upt zero_nata num_actions));

fun compute_upds_impl bounds init =
  map_filter
    (fn comb =>
      let
        val (g, (a, (r, (l, s)))) =
          fold (fn (q, (_, (g2, (_, (f2, (r2, l2)))))) =>
                 fn (g1, (a, (r1, (l, s)))) =>
                 (g1 @ g2, (a, (r1 @ r2, (list_update l q l2, mk_updsi s f2)))))
            comb init;
      in
        (if check_boundedi bounds s then SOME (g, (a, (r, (l, s)))) else NONE)
      end);

fun actions_by_statea num_actions xs =
  fold (fn t => fn acc =>
         list_update acc (fst (snd (snd t))) (t :: nth acc (fst (snd (snd t)))))
    xs (map (fn _ => []) (upt zero_nata num_actions));

fun get_committed broadcast bounds automata l =
  map_filter
    (fn p =>
      let
        val la = nth l p;
      in
        (if membera equal_nat (fst (nth automata p)) la then SOME (p, la)
          else NONE)
      end)
    (upt zero_nata (size_list automata));

fun bin_actions broadcast num_actions =
  filter (fn a => not (membera equal_nat broadcast a))
    (upt zero_nata num_actions);

fun make_combs broadcast bounds automata p a xs =
  let
    val ys =
      map_filter
        (fn i =>
          (if equal_nata i p then NONE
            else (if null (nth (nth xs i) a) then NONE
                   else SOME (map (fn aa => (i, aa)) (nth (nth xs i) a)))))
        (upt zero_nata (size_list automata));
  in
    (if null ys then [] else product_lists ys)
  end;

fun union_map_of A_ xs =
  fold (fn (x, y) => fn m =>
         (case m x of NONE => fun_upd A_ m x (SOME [y])
           | SOME ys => fun_upd A_ m x (SOME (y :: ys))))
    xs (fn _ => NONE);

fun trans_map automata i =
  let
    val m = union_map_of equal_nat (fst (snd (snd (nth automata i))));
  in
    (fn j => (case m j of NONE => [] | SOME xs => xs))
  end;

fun reset_canonical_upd_impl_int x =
  (fn n => fn ai => fn bib => fn bia => fn bi =>
    (fn f_ => fn () => f_
      ((mtx_set (heap_DBMEntry heap_int) (suc n) ai (bia, zero_nata) (Le bi))
      ()) ())
      (fn xa =>
        (fn f_ => fn () => f_
          ((mtx_set (heap_DBMEntry heap_int) (suc n) xa (zero_nata, bia)
             (Le (uminus_inta bi)))
          ()) ())
          (imp_for_inta one_nata (plus_nata bib one_nata)
            (fn xb => fn sigma =>
              (if equal_nata xb bia then (fn () => sigma)
                else (fn f_ => fn () => f_
                       ((mtx_get (heap_DBMEntry heap_int) (suc n) sigma
                          (zero_nata, xb))
                       ()) ())
                       (fn x_d =>
                         (fn f_ => fn () => f_
                           ((mtx_get (heap_DBMEntry heap_int) (suc n) sigma
                              (xb, zero_nata))
                           ()) ())
                           (fn x_e =>
                             (fn f_ => fn () => f_
                               ((mtx_set (heap_DBMEntry heap_int) (suc n) sigma
                                  (bia, xb) (dbm_add_int (Le bi) x_d))
                               ()) ())
                               (fn x_f =>
                                 mtx_set (heap_DBMEntry heap_int) (suc n) x_f
                                   (xb, bia)
                                   (dbm_add_int (Le (uminus_inta bi))
                                     x_e)))))))))
    x;

fun up_canonical_upd_impl_int x =
  (fn n => fn ai => fn bi =>
    imp_for_inta one_nata (plus_nata bi one_nata)
      (fn xa => fn sigma =>
        mtx_set (heap_DBMEntry heap_int) (suc n) sigma (xa, zero_nata) INF)
      ai)
    x;

fun abstra_upd_impl_int x =
  (fn n => fn ai => fn bi =>
    (case ai
      of LTa (x41a, x42a) =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (x41a, zero_nata)) ())
          ())
          (fn xa =>
            mtx_set (heap_DBMEntry heap_int) (suc n) bi (x41a, zero_nata)
              (min_int_entry xa (Lt x42a)))
      | LEa (x41a, x42a) =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (x41a, zero_nata)) ())
          ())
          (fn xa =>
            mtx_set (heap_DBMEntry heap_int) (suc n) bi (x41a, zero_nata)
              (min_int_entry xa (Le x42a)))
      | EQa (x41a, x42a) =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (zero_nata, x41a)) ())
          ())
          (fn xa =>
            (fn f_ => fn () => f_
              ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (x41a, zero_nata))
              ()) ())
              (fn x_a =>
                (fn f_ => fn () => f_
                  ((mtx_set (heap_DBMEntry heap_int) (suc n) bi
                     (zero_nata, x41a)
                     (min_int_entry xa (Le (uminus_inta x42a))))
                  ()) ())
                  (fn x_b =>
                    mtx_set (heap_DBMEntry heap_int) (suc n) x_b
                      (x41a, zero_nata) (min_int_entry x_a (Le x42a)))))
      | GTa (x41a, x42a) =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (zero_nata, x41a)) ())
          ())
          (fn xa =>
            mtx_set (heap_DBMEntry heap_int) (suc n) bi (zero_nata, x41a)
              (min_int_entry xa (Lt (uminus_inta x42a))))
      | GEa (x41a, x42a) =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (zero_nata, x41a)) ())
          ())
          (fn xa =>
            mtx_set (heap_DBMEntry heap_int) (suc n) bi (zero_nata, x41a)
              (min_int_entry xa (Le (uminus_inta x42a))))))
    x;

fun abstr_repair_impl_int x =
  (fn m => fn ai =>
    imp_nfoldli ai (fn _ => (fn () => true))
      (fn aia => fn bi =>
        (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bi) ()) ())
          (fn xa => repair_pair_impl_int m xa zero_nata (constraint_clk aia))))
    x;

fun e_op_impl x =
  (fn m => fn l_inv => fn r => fn g => fn l_inva => fn ma =>
    (fn f_ => fn () => f_ ((up_canonical_upd_impl_int m ma m) ()) ())
      (fn m1 =>
        (fn f_ => fn () => f_ ((abstr_repair_impl_int m l_inv m1) ()) ())
          (fn m2 =>
            (fn f_ => fn () => f_ ((check_diag_impl_int m m2) ()) ())
              (fn is_empty1 =>
                (fn f_ => fn () => f_
                  ((if is_empty1
                     then mtx_set (heap_DBMEntry heap_int) (suc m) m2
                            (zero_nata, zero_nata) (Lt zero_inta)
                     else abstr_repair_impl_int m g m2)
                  ()) ())
                  (fn m3 =>
                    (fn f_ => fn () => f_ ((check_diag_impl_int m m3) ()) ())
                      (fn is_empty3 =>
                        (if is_empty3
                          then mtx_set (heap_DBMEntry heap_int) (suc m) m3
                                 (zero_nata, zero_nata) (Lt zero_inta)
                          else (fn f_ => fn () => f_
                                 ((imp_nfoldli r (fn _ => (fn () => true))
                                    (fn xc => fn sigma =>
                                      reset_canonical_upd_impl_int m sigma m xc
zero_inta)
                                    m3)
                                 ()) ())
                                 (abstr_repair_impl_int m l_inva))))))))
    x;

fun succs_impl broadcast bounds automata m num_actions =
  let
    val trans_impl =
      let
        val trans_mapa = trans_map automata;
        val trans_i_map =
          (fn i => fn j =>
            map_filter
              (fn a =>
                (case a of (_, (_, (In _, (_, _)))) => NONE
                  | (_, (_, (Out _, (_, _)))) => NONE
                  | (b, (g, (Sil aa, (ma, l)))) =>
                    SOME (b, (g, (aa, (ma, l))))))
              (trans_mapa i j));
        val int_trans_from_loc_impl =
          (fn p => fn l => fn la => fn s =>
            let
              val a = trans_i_map p l;
            in
              map_filter
                (fn (b, (g, (aa, (f, (r, lb))))) =>
                  let
                    val sa = mk_updsi s f;
                  in
                    (if bvali (equal_int, linorder_int) s b andalso
                          check_boundedi bounds sa
                      then SOME (g, (Internal aa,
                                      (r, (list_update la p lb, sa))))
                      else NONE)
                  end)
                a
            end);
        val int_trans_from_vec_impl =
          (fn pairs => fn l => fn s =>
            maps (fn (p, la) => int_trans_from_loc_impl p la l s) pairs);
        val int_trans_from_all_impl =
          (fn l => fn s =>
            maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
              (upt zero_nata (size_list automata)));
        val trans_out_map =
          (fn i => fn j =>
            map_filter
              (fn a =>
                (case a of (_, (_, (In _, (_, _)))) => NONE
                  | (b, (g, (Out aa, (ma, l)))) => SOME (b, (g, (aa, (ma, l))))
                  | (_, (_, (Sil _, (_, _)))) => NONE))
              (trans_mapa i j));
        val trans_in_map =
          (fn i => fn j =>
            map_filter
              (fn a =>
                (case a
                  of (b, (g, (In aa, (ma, l)))) => SOME (b, (g, (aa, (ma, l))))
                  | (_, (_, (Out _, (_, _)))) => NONE
                  | (_, (_, (Sil _, (_, _)))) => NONE))
              (trans_mapa i j));
        val trans_out_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn a =>
                  (case a of (_, (_, (In _, (_, _)))) => NONE
                    | (b, (g, (Out aa, (ma, l)))) =>
                      (if membera equal_nat broadcast aa
                        then SOME (b, (g, (aa, (ma, l)))) else NONE)
                    | (_, (_, (Sil _, (_, _)))) => NONE))
                (trans_mapa i j)));
        val trans_in_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn a =>
                  (case a
                    of (b, (g, (In aa, (ma, l)))) =>
                      (if membera equal_nat broadcast aa
                        then SOME (b, (g, (aa, (ma, l)))) else NONE)
                    | (_, (_, (Out _, (_, _)))) => NONE
                    | (_, (_, (Sil _, (_, _)))) => NONE))
                (trans_mapa i j)));
        val broad_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_committed broadcast bounds automata l;
              val ina =
                map (fn p => trans_in_broad_grouped p (nth l p))
                  (upt zero_nata (size_list automata));
              val out =
                map (fn p => trans_out_broad_grouped p (nth l p))
                  (upt zero_nata (size_list automata));
              val inb =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  ina;
              val outa =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  out;
            in
              (if null pairs
                then maps (fn a =>
                            maps (fn p =>
                                   let
                                     val outs = nth (nth outa p) a;
                                   in
                                     (if null outs then []
                                       else let
      val combs = make_combs broadcast bounds automata p a inb;
      val outsa = map (fn aa => (p, aa)) outs;
      val combsa =
        (if null combs then map (fn x => [x]) outsa
          else maps (fn x => map (fn aa => x :: aa) combs) outsa);
      val init = ([], (Broad a, ([], (l, s))));
    in
      compute_upds_impl bounds init combsa
    end)
                                   end)
                              (upt zero_nata (size_list automata)))
                       (upt zero_nata num_actions)
                else maps (fn a =>
                            let
                              val ins_committed =
                                map_filter
                                  (fn (p, _) =>
                                    (if not (null (nth (nth inb p) a))
                                      then SOME p else NONE))
                                  pairs;
                              val always_committed =
                                less_nat one_nata (size_list ins_committed);
                            in
                              maps (fn p =>
                                     let
                                       val outs = nth (nth outa p) a;
                                     in
                                       (if null outs then []
 else (if not always_committed andalso
            ((equal_lista equal_nat ins_committed [p] orelse
               null ins_committed) andalso
              not (list_ex (fn (q, _) => equal_nata q p) pairs))
        then []
        else let
               val combs = make_combs broadcast bounds automata p a inb;
               val outsa = map (fn aa => (p, aa)) outs;
               val combsa =
                 (if null combs then map (fn x => [x]) outsa
                   else maps (fn x => map (fn aa => x :: aa) combs) outsa);
               val init = ([], (Broad a, ([], (l, s))));
             in
               compute_upds_impl bounds init combsa
             end))
                                     end)
                                (upt zero_nata (size_list automata))
                            end)
                       (upt zero_nata num_actions))
            end);
        val bin_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_committed broadcast bounds automata l;
              val ina =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_in_map l;
              val out =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_out_map l;
            in
              (if null pairs
                then maps (fn a =>
                            pairs_by_action_impl bounds l s (nth out a)
                              (nth ina a))
                       (bin_actions broadcast num_actions)
                else let
                       val in2 =
                         all_actions_from_vec num_actions trans_in_map pairs;
                       val out2 =
                         all_actions_from_vec num_actions trans_out_map pairs;
                     in
                       maps (fn a =>
                              pairs_by_action_impl bounds l s (nth out a)
                                (nth in2 a))
                         (bin_actions broadcast num_actions) @
                         maps (fn a =>
                                pairs_by_action_impl bounds l s (nth out2 a)
                                  (nth ina a))
                           (bin_actions broadcast num_actions)
                     end)
            end);
        val int_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_committed broadcast bounds automata l;
            in
              (if null pairs then int_trans_from_all_impl l s
                else int_trans_from_vec_impl pairs l s)
            end);
      in
        (fn st => int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st)
      end;
  in
    (fn n_ps => fn invs =>
      let
        val inv_fun =
          (fn (l, _) =>
            maps (fn i => sub (sub invs i) (nth l i)) (upt zero_nata n_ps));
        val e_op_impla =
          (fn l => fn r => fn g => fn la =>
            e_op_impl m (inv_fun l) r g (inv_fun la));
      in
        (fn l_s => fn ma =>
          (if null ma then (fn () => [])
            else imp_nfoldli (trans_impl l_s) (fn _ => (fn () => true))
                   (fn c => fn sigma =>
                     let
                       val (g, (_, (r, l_sa))) = c;
                     in
                       (fn f_ => fn () => f_
                         ((heap_map (amtx_copy (heap_DBMEntry heap_int)) ma) ())
                         ())
                         (fn maa =>
                           (fn f_ => fn () => f_
                             ((imp_nfoldli maa (fn _ => (fn () => true))
                                (fn xb => fn sigmaa =>
                                  (fn f_ => fn () => f_
                                    ((e_op_impla l_s r g l_sa xb) ()) ())
                                    (fn x_c =>
                                      (fn f_ => fn () => f_
((check_diag_impl_int m x_c) ()) ())
(fn x_e => (fn () => (if x_e then sigmaa else op_list_prepend x_c sigmaa)))))
                                [])
                             ()) ())
                             (fn ms =>
                               (fn () => (op_list_prepend (l_sa, ms) sigma))))
                     end)
                   []))
      end)
  end;

fun dbm_le_int (Lt a) (Lt b) = less_eq_int a b
  | dbm_le_int (Lt a) (Le b) = less_eq_int a b
  | dbm_le_int (Le a) (Lt b) = less_int a b
  | dbm_le_int (Le a) (Le b) = less_eq_int a b
  | dbm_le_int uu INF = true
  | dbm_le_int INF (Le v) = false
  | dbm_le_int INF (Lt v) = false;

fun array_all2 n p asa bs =
  let
    val d = minus_nata n one_nata;
  in
    (if less_nat d n
      then all_interval (equal_nat, interval_nat)
             (fn i => p (sub asa i) (sub bs i)) zero_nata d
      else true)
  end;

fun check_sexpi A_ Truea uu uv = true
  | check_sexpi A_ (Notb e) l s = not (check_sexpi A_ e l s)
  | check_sexpi A_ (Andb (e1, e2)) l s =
    check_sexpi A_ e1 l s andalso check_sexpi A_ e2 l s
  | check_sexpi A_ (Orb (e1, e2)) l s =
    check_sexpi A_ e1 l s orelse check_sexpi A_ e2 l s
  | check_sexpi A_ (Implya (e1, e2)) l s =
    (if check_sexpi A_ e1 l s then check_sexpi A_ e2 l s else true)
  | check_sexpi A_ (Eqb (i, x)) l s = equal_inta (nth s i) x
  | check_sexpi A_ (Leb (i, x)) l s = less_eq_int (nth s i) x
  | check_sexpi A_ (Ltc (i, x)) l s = less_int (nth s i) x
  | check_sexpi A_ (Gea (i, x)) l s = less_eq_int x (nth s i)
  | check_sexpi A_ (Gtb (i, x)) l s = less_int x (nth s i)
  | check_sexpi A_ (Loc (i, x)) l s = eq A_ (nth l i) x;

fun hd_of_formulai A_ (EX phi) l s = check_sexpi A_ phi l s
  | hd_of_formulai A_ (EG phi) l s = check_sexpi A_ phi l s
  | hd_of_formulai A_ (AX phi) l s = not (check_sexpi A_ phi l s)
  | hd_of_formulai A_ (AG phi) l s = not (check_sexpi A_ phi l s)
  | hd_of_formulai A_ (Leadsto (phi, uu)) l s = check_sexpi A_ phi l s;

fun split_size f width uu acc [] = [acc]
  | split_size f width n acc (x :: xs) =
    let
      val k = f x;
    in
      (if less_nat n width then split_size f width (plus_nata n k) (x :: acc) xs
        else acc :: split_size f width k [x] xs)
    end;

fun sum_list A_ xs =
  foldr (plus ((plus_semigroup_add o semigroup_add_monoid_add) A_)) xs
    (zero (zero_monoid_add A_));

fun split_ka k xs =
  let
    val width =
      divide_nat (sum_list monoid_add_nat (map (size_list o snd) xs)) k;
    val widtha =
      (if equal_nata (modulo_nat (size_list xs) k) zero_nata then width
        else plus_nata width one_nata);
  in
    map (map fst) (split_size (size_list o snd) widtha zero_nata [] xs)
  end;

fun default_map_of B_ a xs = map_default a (map_of B_ xs);

fun no_buechi_run_checker broadcast bounds automata m num_states num_actions l_0
  s_0 formula l_list m_list num_split =
  let
    val n_vsa = n_vs bounds;
    val n_ps = size_list automata;
    val invs =
      Vector.fromList
        (map (fn i =>
               let
                 val ma =
                   default_map_of equal_nat []
                     (snd (snd (snd (nth automata i))));
                 val mb =
                   Vector.fromList (map ma (upt zero_nata (num_states i)));
               in
                 mb
               end)
          (upt zero_nata n_ps));
    val succsi = succs_impl broadcast bounds automata m num_actions n_ps invs;
    val states_ia = map (states_i automata) (upt zero_nata n_ps);
    val check_state =
      (fn (l, s) =>
        equal_nata (size_list l) n_ps andalso
          let
            val d = minus_nata n_ps one_nata;
          in
            (if less_nat d n_ps
              then all_interval (equal_nat, interval_nat)
                     (fn i =>
                       member (ceq_nat, ccompare_nat) (nth l i)
                         (nth states_ia i))
                     zero_nata d
              else true)
          end andalso
          (equal_nata (size_list s) n_vsa andalso check_boundedi bounds s));
    val mi =
      hashmap_of_list
        (equal_prod (equal_list equal_nat) (equal_list equal_int),
          hashable_prod (hashable_list hashable_nat)
            (hashable_list hashable_int))
        (map (fn (k, dbms) =>
               (k, map (fn (ma, a) => (Vector.fromList ma, a)) dbms))
          m_list);
    val init_dbm =
      amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m) (Le zero_inta);
  in
    certify_no_buechi_run_pure
      (fn x =>
        (fn a => (fn f => f ()) a) o
          (fn xs =>
            let
              val li = id x;
            in
              (fn f_ => fn () => f_
                ((fold_map (array_unfreeze (heap_DBMEntry heap_int)) xs) ()) ())
                (fn xsi =>
                  (fn f_ => fn () => f_ ((succsi li xsi) ()) ())
                    (fold_map
                      (fn (lia, xsia) =>
                        (fn f_ => fn () => f_
                          ((fold_map (array_freeze (heap_DBMEntry heap_int))
                             xsia)
                          ()) ())
                          (fn xsa => (fn () => (id lia, xsa))))))
            end))
      l_list
      (fn asa => fn bs =>
        not (all_interval (equal_nat, interval_nat)
              (not o
                (fn i =>
                  dbm_lt_0
                    (sub asa (plus_nata (plus_nata i (times_nata i m)) i))))
              zero_nata m) orelse
          array_all2 (times_nata (suc m) (suc m)) dbm_le_int asa bs)
      (split_ka num_split m_list)
      (fn a =>
        (fn f => f ()) ((fn f_ => fn () => f_
                          (let
                             val (l, s) = a;
                           in
                             (fn f_ => fn () => f_
                               ((array_unfreeze (heap_DBMEntry heap_int) s) ())
                               ())
                               (fn sa => (fn () => (id l, sa)))
                           end
                          ()) ())
                         (fn (a1, a2) =>
                           (fn f_ => fn () => f_
                             ((imp_for_int zero_nata (plus_nata m one_nata)
                                (fn aa => (fn () => aa))
                                (fn xc => fn _ =>
                                  imp_for_int zero_nata (plus_nata m one_nata)
                                    (fn aa => (fn () => aa))
                                    (fn xf => fn _ =>
                                      imp_for_int zero_nata
(plus_nata m one_nata) (fn aa => (fn () => aa))
(fn xj => fn _ =>
  (fn f_ => fn () => f_ ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xj))
    ()) ())
    (fn x_i =>
      (fn f_ => fn () => f_
        ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xf)) ()) ())
        (fn x =>
          (fn f_ => fn () => f_
            ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xf, xj)) ()) ())
            (fn xa => (fn () => (dbm_le_int x_i (dbm_add_int x xa)))))))
true)
                                    true)
                                true)
                             ()) ())
                             (fn x =>
                               (fn f_ => fn () => f_ ((check_diag_impl_int m a2)
                                 ()) ())
                                 (fn xa =>
                                   (fn f_ => fn () => f_
                                     ((imp_for_int zero_nata
(plus_nata m one_nata) (fn aa => (fn () => aa))
(fn xc => fn _ =>
  (fn f_ => fn () => f_ ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xc))
    ()) ())
    (fn x_d => (fn () => (dbm_le_int x_d (Le zero_inta)))))
true)
                                     ()) ())
                                     (fn xb =>
                                       (fn f_ => fn () => f_
 ((imp_for_int zero_nata (plus_nata m one_nata) (fn aa => (fn () => aa))
    (fn xc => fn _ =>
      (fn f_ => fn () => f_
        ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (zero_nata, xc)) ()) ())
        (fn x_e => (fn () => (dbm_le_int x_e (Le zero_inta)))))
    true)
 ()) ())
 (fn xc =>
   (fn () =>
     (check_state a1 andalso ((x orelse xa) andalso (xb andalso xc)))))))))))
      (fn a =>
        (fn f => f ()) ((fn f_ => fn () => f_
                          (let
                             val (l, s) = a;
                           in
                             (fn f_ => fn () => f_
                               ((array_unfreeze (heap_DBMEntry heap_int) s) ())
                               ())
                               (fn sa => (fn () => (id l, sa)))
                           end
                          ()) ())
                         (fn xi =>
                           (fn () => let
                                       val ((aa, b), _) = xi;
                                     in
                                       hd_of_formulai equal_nat formula aa b
                                     end))))
      (fn k =>
        ahm_lookup (equal_proda (equal_list equal_nat) (equal_list equal_int))
          (bounded_hashcode_nat
            (hashable_prod (hashable_list hashable_nat)
              (hashable_list hashable_int)))
          k mi)
      ((fn f => f ()) ((fn f_ => fn () => f_
                         ((imp_nfoldli
                            [(l_0, map (the o map_of equal_nat s_0)
                                     (upt zero_nata n_vsa))]
                            (fn _ => (fn () => true))
                            (fn xc => fn sigma =>
                              (fn f_ => fn () => f_ (init_dbm ()) ())
                                (fn x =>
                                  (fn () =>
                                    (op_list_concat sigma
                                      (op_list_prepend (xc, x) [])))))
                            [])
                         ()) ())
                        (fold_map
                          (fn (l, s) =>
                            (fn f_ => fn () => f_
                              ((array_freeze (heap_DBMEntry heap_int) s) ()) ())
                              (fn sa => (fn () => (id l, sa)))))))
  end;

fun buechi_certificate_checker num_split m_list broadcast bounds automata m
  num_states num_actions k l_0 s_0 formula =
  let
    val l_list = map fst m_list;
  in
    (case certificate_checker_pre1 l_list m_list broadcast bounds automata m
            num_states num_actions k l_0 s_0 formula
      of true =>
        no_buechi_run_checker broadcast bounds automata m num_states num_actions
          l_0 s_0 formula l_list m_list num_split
      | false => let
                   val _ = writeln "Checking Buechi preconditions failed";
                 in
                   false
                 end)
  end;

fun set2_sexp (B1_, B2_, B3_) Truea = bot_set (B1_, B2_, B3_)
  | set2_sexp (B1_, B2_, B3_) (Notb x2) = set2_sexp (B1_, B2_, B3_) x2
  | set2_sexp (B1_, B2_, B3_) (Andb (x31, x32)) =
    sup_seta (B1_, B2_) (set2_sexp (B1_, B2_, B3_) x31)
      (set2_sexp (B1_, B2_, B3_) x32)
  | set2_sexp (B1_, B2_, B3_) (Orb (x41, x42)) =
    sup_seta (B1_, B2_) (set2_sexp (B1_, B2_, B3_) x41)
      (set2_sexp (B1_, B2_, B3_) x42)
  | set2_sexp (B1_, B2_, B3_) (Implya (x51, x52)) =
    sup_seta (B1_, B2_) (set2_sexp (B1_, B2_, B3_) x51)
      (set2_sexp (B1_, B2_, B3_) x52)
  | set2_sexp (B1_, B2_, B3_) (Eqb (x61, x62)) = bot_set (B1_, B2_, B3_)
  | set2_sexp (B1_, B2_, B3_) (Leb (x71, x72)) = bot_set (B1_, B2_, B3_)
  | set2_sexp (B1_, B2_, B3_) (Ltc (x81, x82)) = bot_set (B1_, B2_, B3_)
  | set2_sexp (B1_, B2_, B3_) (Gea (x91, x92)) = bot_set (B1_, B2_, B3_)
  | set2_sexp (B1_, B2_, B3_) (Gtb (x101, x102)) = bot_set (B1_, B2_, B3_)
  | set2_sexp (B1_, B2_, B3_) (Loc (x111, x112)) =
    insert (B1_, B2_) x112 (bot_set (B1_, B2_, B3_));

fun set2_formula (B1_, B2_, B3_) (EX x1) = set2_sexp (B1_, B2_, B3_) x1
  | set2_formula (B1_, B2_, B3_) (EG x2) = set2_sexp (B1_, B2_, B3_) x2
  | set2_formula (B1_, B2_, B3_) (AX x3) = set2_sexp (B1_, B2_, B3_) x3
  | set2_formula (B1_, B2_, B3_) (AG x4) = set2_sexp (B1_, B2_, B3_) x4
  | set2_formula (B1_, B2_, B3_) (Leadsto (x51, x52)) =
    sup_seta (B1_, B2_) (set2_sexp (B1_, B2_, B3_) x51)
      (set2_sexp (B1_, B2_, B3_) x52);

fun locs_of_sexp (A1_, A2_, A3_) (Notb e) = locs_of_sexp (A1_, A2_, A3_) e
  | locs_of_sexp (A1_, A2_, A3_) (Andb (e1, e2)) =
    sup_seta (A1_, A2_) (locs_of_sexp (A1_, A2_, A3_) e1)
      (locs_of_sexp (A1_, A2_, A3_) e2)
  | locs_of_sexp (A1_, A2_, A3_) (Orb (e1, e2)) =
    sup_seta (A1_, A2_) (locs_of_sexp (A1_, A2_, A3_) e1)
      (locs_of_sexp (A1_, A2_, A3_) e2)
  | locs_of_sexp (A1_, A2_, A3_) (Implya (e1, e2)) =
    sup_seta (A1_, A2_) (locs_of_sexp (A1_, A2_, A3_) e1)
      (locs_of_sexp (A1_, A2_, A3_) e2)
  | locs_of_sexp (A1_, A2_, A3_) (Loc (i, x)) =
    insert (A1_, A2_) i (bot_set (A1_, A2_, A3_))
  | locs_of_sexp (A1_, A2_, A3_) Truea = bot_set (A1_, A2_, A3_)
  | locs_of_sexp (A1_, A2_, A3_) (Eqb (v, va)) = bot_set (A1_, A2_, A3_)
  | locs_of_sexp (A1_, A2_, A3_) (Leb (v, va)) = bot_set (A1_, A2_, A3_)
  | locs_of_sexp (A1_, A2_, A3_) (Ltc (v, va)) = bot_set (A1_, A2_, A3_)
  | locs_of_sexp (A1_, A2_, A3_) (Gea (v, va)) = bot_set (A1_, A2_, A3_)
  | locs_of_sexp (A1_, A2_, A3_) (Gtb (v, va)) = bot_set (A1_, A2_, A3_);

fun locs_of_formula (A1_, A2_, A3_) (EX phi) = locs_of_sexp (A1_, A2_, A3_) phi
  | locs_of_formula (A1_, A2_, A3_) (EG phi) = locs_of_sexp (A1_, A2_, A3_) phi
  | locs_of_formula (A1_, A2_, A3_) (AX phi) = locs_of_sexp (A1_, A2_, A3_) phi
  | locs_of_formula (A1_, A2_, A3_) (AG phi) = locs_of_sexp (A1_, A2_, A3_) phi
  | locs_of_formula (A1_, A2_, A3_) (Leadsto (phi, psi)) =
    sup_seta (A1_, A2_) (locs_of_sexp (A1_, A2_, A3_) phi)
      (locs_of_sexp (A1_, A2_, A3_) psi);

fun prod_TA_act_set_impl (A1_, A2_, A3_) (broadcast, (automata, bounds)) =
  sup_seta (A1_, A2_)
    (foldl (sup_seta (A1_, A2_)) (bot_set (A1_, A2_, A3_))
      (foldl
        (fn a => fn x =>
          a @ map (fn (_, (_, (_, (aa, (_, (_, _)))))) =>
                    set_act (A1_, A2_, A3_) aa)
                let
                  val (_, (_, (trans, _))) = nth automata x;
                in
                  trans
                end)
        [] (upt zero_nata (size_list automata))))
    (set (A1_, A2_, A3_) broadcast);

fun check_renaming x =
  (fn broadcast => fn bounds => fn renum_acts => fn renum_vars =>
    fn renum_clocks => fn renum_states => fn automata => fn urge => fn phi =>
    fn l_0 => fn s_0 =>
    combinea
      [assert
         let
           val d = minus_nata (size_list automata) one_nata;
         in
           (if less_nat d (size_list automata)
             then all_interval (equal_nat, interval_nat)
                    (fn i =>
                      ball (ceq_nat, ccompare_nat)
                        (prod_TA_loc_set_impl
                          (ceq_nat, ccompare_nat, set_impl_nat)
                          (broadcast, (automata, bounds)))
                        (fn xa =>
                          ball (ceq_nat, ccompare_nat)
                            (prod_TA_loc_set_impl
                              (ceq_nat, ccompare_nat, set_impl_nat)
                              (broadcast, (automata, bounds)))
                            (fn y =>
                              (if equal_nata (renum_states i xa)
                                    (renum_states i y)
                                then equal_nata xa y else true))))
                    zero_nata d
             else true)
         end
         "Location renamings are injective",
        assert
          (inj_on (ceq_literal, ccompare_literal, equal_literal) equal_nat
            renum_clocks
            (insert (ceq_literal, ccompare_literal) urge
              (clk_set
                (ceq_literal, ccompare_literal, compare_literal, equal_literal,
                  set_impl_literal)
                automata)))
          "Clock renaming is injective",
        assert
          (inj_on (ceq_literal, ccompare_literal, equal_literal) equal_nat
            renum_vars
            (prop_TA_var_set_impl
              (ceq_literal, ccompare_literal, set_impl_literal)
              (broadcast, (automata, bounds))))
          "Variable renaming is injective",
        assert
          (inj_on (ceq_literal, ccompare_literal, equal_literal) equal_nat
            renum_acts
            (prod_TA_act_set_impl
              (ceq_literal, ccompare_literal, set_impl_literal)
              (broadcast, (automata, bounds))))
          "Action renaming is injective",
        assert
          (set_eq (cenum_literal, ceq_literal, ccompare_literal)
            (set (ceq_literal, ccompare_literal, set_impl_literal)
              (map fst bounds))
            (prop_TA_var_set_impl
              (ceq_literal, ccompare_literal, set_impl_literal)
              (broadcast, (automata, bounds))))
          "Bound set is exactly the variable set",
        assert
          (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (sup_setb
              (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
                set_impl_nat)
              (set (ceq_set
                      (cenum_nat, ceq_nat,
                        ccompare_cproper_interval cproper_interval_nat),
                     ccompare_set
                       (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                         set_impl_nat),
                     set_impl_set)
                (map (fn g =>
                       set (ceq_nat, ccompare_nat, set_impl_nat) (map fst g))
                  (map (snd o snd o snd) automata))))
            (prod_TA_loc_set_impl (ceq_nat, ccompare_nat, set_impl_nat)
              (broadcast, (automata, bounds))))
          "Invariant locations are contained in the location set",
        assert
          (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (sup_setb
              (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
                set_impl_nat)
              (set (ceq_set
                      (cenum_nat, ceq_nat,
                        ccompare_cproper_interval cproper_interval_nat),
                     ccompare_set
                       (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                         set_impl_nat),
                     set_impl_set)
                (map (set (ceq_nat, ccompare_nat, set_impl_nat) o fst)
                  automata)))
            (prod_TA_loc_set_impl (ceq_nat, ccompare_nat, set_impl_nat)
              (broadcast, (automata, bounds))))
          "Broadcast locations are containted in the location set",
        assert
          (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (sup_setb
              (finite_UNIV_nat, cenum_nat, ceq_nat, cproper_interval_nat,
                set_impl_nat)
              (set (ceq_set
                      (cenum_nat, ceq_nat,
                        ccompare_cproper_interval cproper_interval_nat),
                     ccompare_set
                       (finite_UNIV_nat, ceq_nat, cproper_interval_nat,
                         set_impl_nat),
                     set_impl_set)
                (map (fn xa =>
                       set (ceq_nat, ccompare_nat, set_impl_nat) (fst (snd xa)))
                  automata)))
            (prod_TA_loc_set_impl (ceq_nat, ccompare_nat, set_impl_nat)
              (broadcast, (automata, bounds))))
          "Urgent locations are containted in the location set",
        assert
          (not (member (ceq_literal, ccompare_literal) urge
                 (clk_set
                   (ceq_literal, ccompare_literal, compare_literal,
                     equal_literal, set_impl_literal)
                   automata)))
          "Urge not in clock set",
        assert
          (equal_nata (size_list l_0) (size_list automata) andalso
            let
              val d = minus_nata (size_list automata) one_nata;
            in
              (if less_nat d (size_list automata)
                then all_interval (equal_nat, interval_nat)
                       (fn i =>
                         member (ceq_nat, ccompare_nat) (nth l_0 i)
                           (foldl
                             (fn a => fn xa =>
                               sup_seta (ceq_nat, ccompare_nat) a
                                 let
                                   val (l, (_, (_, (_, (_, (_, la)))))) = xa;
                                 in
                                   insert (ceq_nat, ccompare_nat) l
                                     (insert (ceq_nat, ccompare_nat) la
                                       (set_empty (ceq_nat, ccompare_nat)
 (of_phantom set_impl_nata)))
                                 end)
                             (set_empty (ceq_nat, ccompare_nat)
                               (of_phantom set_impl_nata))
                             let
                               val (_, (_, (ts, _))) = nth automata i;
                             in
                               ts
                             end))
                       zero_nata d
                else true)
            end)
          "Initial location is in the state set",
        assert
          (set_eq (cenum_literal, ceq_literal, ccompare_literal)
            (set (ceq_literal, ccompare_literal, set_impl_literal)
              (map fst s_0))
            (prop_TA_var_set_impl
              (ceq_literal, ccompare_literal, set_impl_literal)
              (broadcast, (automata, bounds))))
          "Initial state has the correct domain",
        assert (distinct_ds (equal_literal, linorder_literal) (map fst s_0))
          "Initial state is unambiguous",
        assert
          (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (set2_formula (ceq_nat, ccompare_nat, set_impl_nat) phi)
            (prod_TA_loc_set_impl (ceq_nat, ccompare_nat, set_impl_nat)
              (broadcast, (automata, bounds))))
          "Formula locations are contained in the location set",
        assert
          (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (locs_of_formula (ceq_nat, ccompare_nat, set_impl_nat) phi)
            (atLeastLessThan
              (ceq_nat, ccompare_nat, equal_nat, interval_nat, set_impl_nat)
              zero_nata (size_list automata)))
          "Formula automata are contained in the automata set",
        assert
          (less_eq_set (cenum_literal, ceq_literal, ccompare_literal)
            (vars_of_formula (ceq_literal, ccompare_literal, set_impl_literal)
              phi)
            (prop_TA_var_set_impl
              (ceq_literal, ccompare_literal, set_impl_literal)
              (broadcast, (automata, bounds))))
          "Variables of the formula are contained in the variable set"])
    x;

fun check_precond2 x =
  (fn _ => fn bounds => fn automata => fn m => fn num_states => fn k =>
    fn l_0 => fn s_0 => fn formula =>
    combinea
      [assert
         let
           val d = minus_nata (size_list automata) one_nata;
         in
           (if less_nat d (size_list automata)
             then all_interval (equal_nat, interval_nat)
                    (fn i =>
                      list_all
                        (fn (l, g) =>
                          ball (ceq_prod ceq_nat ceq_int,
                                 ccompare_prod ccompare_nat ccompare_int)
                            (collect_clock_pairs
                              (ceq_nat, ccompare_nat, compare_nat, equal_nat,
                                set_impl_nat)
                              (ceq_int, ccompare_int, compare_int, equal_int,
                                set_impl_int)
                              g)
                            (fn (xa, ma) =>
                              less_eq_int ma
                                (int_of_nat (nth (nth (nth k i) l) xa))))
                        ((snd o snd o snd) (nth automata i)))
                    zero_nata d
             else true)
         end
         "Ceiling invariants",
        assert
          let
            val d = minus_nata (size_list automata) one_nata;
          in
            (if less_nat d (size_list automata)
              then all_interval (equal_nat, interval_nat)
                     (fn i =>
                       list_all
                         (fn (l, (_, (g, _))) =>
                           ball (ceq_prod ceq_nat ceq_int,
                                  ccompare_prod ccompare_nat ccompare_int)
                             (collect_clock_pairs
                               (ceq_nat, ccompare_nat, compare_nat, equal_nat,
                                 set_impl_nat)
                               (ceq_int, ccompare_int, compare_int, equal_int,
                                 set_impl_int)
                               g)
                             (fn (xa, ma) =>
                               less_eq_int ma
                                 (int_of_nat (nth (nth (nth k i) l) xa))))
                         ((fst o snd o snd) (nth automata i)))
                     zero_nata d
              else true)
          end
          "Ceiling transitions",
        assert
          let
            val d = minus_nata (size_list automata) one_nata;
          in
            (if less_nat d (size_list automata)
              then all_interval (equal_nat, interval_nat)
                     (fn i =>
                       list_all
                         (fn (l, (_, (_, (_, (_, (r, la)))))) =>
                           ball (ceq_nat, ccompare_nat)
                             (minus_set (ceq_nat, ccompare_nat)
                               (atLeastLessThan
                                 (ceq_nat, ccompare_nat, equal_nat,
                                   interval_nat, set_impl_nat)
                                 zero_nata (plus_nata m one_nata))
                               (set (ceq_nat, ccompare_nat, set_impl_nat) r))
                             (fn c =>
                               less_eq_nat (nth (nth (nth k i) la) c)
                                 (nth (nth (nth k i) l) c)))
                         ((fst o snd o snd) (nth automata i)))
                     zero_nata d
              else true)
          end
          "Ceiling resets",
        assert (equal_nata (size_list k) (size_list automata)) "Ceiling length",
        assert
          let
            val d = minus_nata (size_list automata) one_nata;
          in
            (if less_nat d (size_list automata)
              then all_interval (equal_nat, interval_nat)
                     (fn i => equal_nata (size_list (nth k i)) (num_states i))
                     zero_nata d
              else true)
          end
          "Ceiling length automata)",
        assert
          (list_all
            (list_all
              (fn xxs => equal_nata (size_list xxs) (plus_nata m one_nata)))
            k)
          "Ceiling length clocks",
        assert
          let
            val d = minus_nata (size_list automata) one_nata;
          in
            (if less_nat d (size_list automata)
              then all_interval (equal_nat, interval_nat)
                     (fn i =>
                       let
                         val da = minus_nata (num_states i) one_nata;
                       in
                         (if less_nat da (num_states i)
                           then all_interval (equal_nat, interval_nat)
                                  (fn l =>
                                    equal_nata (nth (nth (nth k i) l) zero_nata)
                                      zero_nata)
                                  zero_nata da
                           else true)
                       end)
                     zero_nata d
              else true)
          end
          "Ceiling zero clock",
        assert
          (list_all
            (fn (_, (_, (_, inv))) =>
              distinct_ds (equal_nat, linorder_nat) (map fst inv))
            automata)
          "Unambiguous invariants",
        assert
          (set_eq (cenum_nat, ceq_nat, ccompare_nat)
             (image
               (ceq_prod ceq_nat ceq_int,
                 ccompare_prod ccompare_nat ccompare_int)
               (ceq_nat, ccompare_nat, set_impl_nat) fst
               (set (ceq_prod ceq_nat ceq_int,
                      ccompare_prod ccompare_nat ccompare_int,
                      set_impl_prod set_impl_nat set_impl_int)
                 s_0))
             (image
               (ceq_prod ceq_nat (ceq_prod ceq_int ceq_int),
                 ccompare_prod ccompare_nat
                   (ccompare_prod ccompare_int ccompare_int))
               (ceq_nat, ccompare_nat, set_impl_nat) fst
               (set (ceq_prod ceq_nat (ceq_prod ceq_int ceq_int),
                      ccompare_prod ccompare_nat
                        (ccompare_prod ccompare_int ccompare_int),
                      set_impl_prod set_impl_nat
                        (set_impl_prod set_impl_int set_impl_int))
                 bounds)) andalso
            ball (ceq_nat, ccompare_nat)
              (image
                (ceq_prod ceq_nat ceq_int,
                  ccompare_prod ccompare_nat ccompare_int)
                (ceq_nat, ccompare_nat, set_impl_nat) fst
                (set (ceq_prod ceq_nat ceq_int,
                       ccompare_prod ccompare_nat ccompare_int,
                       set_impl_prod set_impl_nat set_impl_int)
                  s_0))
              (fn xa =>
                less_eq_int (fst (the (map_of equal_nat bounds xa)))
                  (the (map_of equal_nat s_0 xa)) andalso
                  less_eq_int (the (map_of equal_nat s_0 xa))
                    (snd (the (map_of equal_nat bounds xa)))))
          "Initial state bounded",
        assert (equal_nata (size_list l_0) (size_list automata))
          "Length of initial state",
        assert
          let
            val d = minus_nata (size_list automata) one_nata;
          in
            (if less_nat d (size_list automata)
              then all_interval (equal_nat, interval_nat)
                     (fn i =>
                       membera equal_nat
                         (map fst ((fst o snd o snd) (nth automata i)))
                         (nth l_0 i))
                     zero_nata d
              else true)
          end
          "Initial state has outgoing transitions",
        assert
          (less_eq_set (cenum_nat, ceq_nat, ccompare_nat)
            (vars_of_formula (ceq_nat, ccompare_nat, set_impl_nat) formula)
            (atLeastLessThan
              (ceq_nat, ccompare_nat, equal_nat, interval_nat, set_impl_nat)
              zero_nata (size_list bounds)))
          "Variable set of formula"])
    x;

fun check_precond1 broadcast bounds automata m num_states num_actions =
  combinea
    [assert (less_nat zero_nata m) "At least one clock",
      assert (less_nat zero_nata (size_list automata)) "At least one automaton",
      assert
        let
          val d = minus_nata (size_list automata) one_nata;
        in
          (if less_nat d (size_list automata)
            then all_interval (equal_nat, interval_nat)
                   (fn i =>
                     let
                       val (_, (_, (trans, _))) = nth automata i;
                     in
                       list_all
                         (fn (l, (_, (_, (_, (_, (_, la)))))) =>
                           less_nat l (num_states i) andalso
                             less_nat la (num_states i))
                         trans
                     end)
                   zero_nata d
            else true)
        end
        "Number of states is correct (transitions)",
      assert
        let
          val d = minus_nata (size_list automata) one_nata;
        in
          (if less_nat d (size_list automata)
            then all_interval (equal_nat, interval_nat)
                   (fn i =>
                     let
                       val (_, (_, (_, a))) = nth automata i;
                     in
                       list_all (fn (x, _) => less_nat x (num_states i)) a
                     end)
                   zero_nata d
            else true)
        end
        "Number of states is correct (invariants)",
      assert
        (list_all
          (fn (_, (_, (trans, _))) =>
            list_all
              (fn (_, (_, (_, (_, (f, (_, _)))))) =>
                list_all
                  (fn (x, upd) =>
                    less_nat x (n_vs bounds) andalso
                      ball (ceq_nat, ccompare_nat)
                        (vars_of_exp (ceq_nat, ccompare_nat, set_impl_nat) upd)
                        (fn i => less_nat i (n_vs bounds)))
                  f)
              trans)
          automata)
        "Variable set bounded (updates)",
      assert
        (list_all
          (fn (_, (_, (trans, _))) =>
            list_all
              (fn (_, (b, (_, (_, (_, (_, _)))))) =>
                ball (ceq_nat, ccompare_nat)
                  (vars_of_bexp (ceq_nat, ccompare_nat, set_impl_nat) b)
                  (fn i => less_nat i (n_vs bounds)))
              trans)
          automata)
        "Variable set bounded (guards)",
      assert
        let
          val d = minus_nata (n_vs bounds) one_nata;
        in
          (if less_nat d (n_vs bounds)
            then all_interval (equal_nat, interval_nat)
                   (fn i => equal_nata (fst (nth bounds i)) i) zero_nata d
            else true)
        end
        "Bounds first index",
      assert (list_all (fn a => less_nat a num_actions) broadcast)
        "Broadcast actions bounded",
      assert
        (list_all
          (fn (_, (_, (trans, _))) =>
            list_all
              (fn (_, (_, (_, (a, (_, (_, _)))))) =>
                pred_act (ceq_nat, ccompare_nat, set_impl_nat)
                  (fn aa => less_nat aa num_actions) a)
              trans)
          automata)
        "Actions bounded (transitions)",
      assert
        (list_all
          (fn (_, (_, (trans, _))) =>
            list_all
              (fn (_, (_, (g, (_, (_, (r, _)))))) =>
                list_all (fn c => less_nat zero_nata c andalso less_eq_nat c m)
                  r andalso
                  ball (ceq_prod ceq_nat ceq_int,
                         ccompare_prod ccompare_nat ccompare_int)
                    (collect_clock_pairs
                      (ceq_nat, ccompare_nat, compare_nat, equal_nat,
                        set_impl_nat)
                      (ceq_int, ccompare_int, compare_int, equal_int,
                        set_impl_int)
                      g)
                    (fn (c, x) =>
                      less_nat zero_nata c andalso
                        (less_eq_nat c m andalso less_eq_int zero_inta x)))
              trans)
          automata)
        "Clock set bounded (transitions)",
      assert
        (list_all
          (fn (_, (_, (_, a))) =>
            list_all
              (fn (_, g) =>
                ball (ceq_prod ceq_nat ceq_int,
                       ccompare_prod ccompare_nat ccompare_int)
                  (collect_clock_pairs
                    (ceq_nat, ccompare_nat, compare_nat, equal_nat,
                      set_impl_nat)
                    (ceq_int, ccompare_int, compare_int, equal_int,
                      set_impl_int)
                    g)
                  (fn (c, x) =>
                    less_nat zero_nata c andalso
                      (less_eq_nat c m andalso less_eq_int zero_inta x)))
              a)
          automata)
        "Clock set bounded (invariants)",
      assert
        (list_all
          (fn (_, (_, (trans, _))) =>
            list_all
              (fn a =>
                (case a
                  of (_, (_, (g, (In aa, (_, (_, _)))))) =>
                    (if membera equal_nat broadcast aa then null g else true)
                  | (_, (_, (_, (Out _, (_, (_, _)))))) => true
                  | (_, (_, (_, (Sil _, (_, (_, _)))))) => true))
              trans)
          automata)
        "Broadcast receivers are unguarded",
      assert (list_all (fn (_, (u, (_, _))) => null u) automata)
        "Urgency was removed"];

fun check_precond broadcast bounds automata m num_states num_actions k l_0 s_0
  formula =
  combine2 (check_precond1 broadcast bounds automata m num_states num_actions)
    (check_precond2 broadcast bounds automata m num_states k l_0 s_0 formula);

fun map_sexp uu uv uw Truea = Truea
  | map_sexp f g h (Notb e) = Notb (map_sexp f g h e)
  | map_sexp f g h (Andb (e1, e2)) = Andb (map_sexp f g h e1, map_sexp f g h e2)
  | map_sexp f g h (Orb (e1, e2)) = Orb (map_sexp f g h e1, map_sexp f g h e2)
  | map_sexp f g h (Implya (e1, e2)) =
    Implya (map_sexp f g h e1, map_sexp f g h e2)
  | map_sexp f g h (Eqb (i, x)) = Eqb (g i, h x)
  | map_sexp f g h (Ltc (i, x)) = Ltc (g i, h x)
  | map_sexp f g h (Leb (i, x)) = Leb (g i, h x)
  | map_sexp f g h (Gea (i, x)) = Gea (g i, h x)
  | map_sexp f g h (Gtb (i, x)) = Gtb (g i, h x)
  | map_sexp f g h (Loc (i, x)) = Loc (i, f i x);

fun map_formulaa f g h (EX phi) = EX (map_sexp f g h phi)
  | map_formulaa f g h (EG phi) = EG (map_sexp f g h phi)
  | map_formulaa f g h (AX phi) = AX (map_sexp f g h phi)
  | map_formulaa f g h (AG phi) = AG (map_sexp f g h phi)
  | map_formulaa f g h (Leadsto (phi, psi)) =
    Leadsto (map_sexp f g h phi, map_sexp f g h psi);

fun find_remove p = map_option (fn (xs, (x, ys)) => (x, xs @ ys)) o extract p;

fun merge_pairs A_ [] ys = ys
  | merge_pairs A_ ((k, v) :: xs) ys =
    (case find_remove (fn (ka, _) => eq A_ ka k) ys
      of NONE => (k, v) :: merge_pairs A_ xs ys
      | SOME ((_, va), ysa) => (k, v @ va) :: merge_pairs A_ xs ysa);

fun conv_urge C_ J_ urge =
  (fn (committed, (urgent, (trans, inv))) =>
    (committed,
      ([], (map (fn (l, (b, (g, (a, (f, (r, la)))))) =>
                  (l, (b, (g, (a, (f, (urge :: r, la)))))))
              trans,
             merge_pairs C_ (map (fn l => (l, [LEa (urge, zero J_)])) urgent)
               inv))));

fun is_result (Result x1) = true
  | is_result (Error x2) = false;

fun do_rename_mc C_ E_ F_ G_ f dc broadcast bounds automata k urge l_0 s_0
  formula m num_states num_actions renum_acts renum_vars renum_clocks
  renum_states inv_renum_states inv_renum_vars inv_renum_clocks =
  let
    val _ = writeln "Checking renaming";
    val formulaa = (if dc then EX (Notb Truea) else formula);
    val renaming_valid =
      check_renaming broadcast bounds renum_acts renum_vars renum_clocks
        renum_states automata urge formulaa l_0 s_0;
    val _ = writeln "Renaming network";
    val (broadcasta, (automataa, boundsa)) =
      rename_network countable_literal countable_literal countable_nat
        countable_literal broadcast bounds
        (map (conv_urge equal_nat zero_int urge) automata) renum_acts renum_vars
        renum_clocks renum_states;
    val _ =
      (fn _ => fn s => writeln (s ())) (Int_of_integer
 (4 : Int.int)) ((fn _ => (fn () => "Automata after renaming")) ());
    val _ =
      map (fn a =>
            (fn _ => fn s => writeln (s ())) (Int_of_integer
       (4 : Int.int)) ((fn _ =>
                            (fn () =>
                              (implode
                                (shows_prec_prod (show_list show_nat)
                                  (show_prod (show_list show_nat)
                                    (show_prod
                                      (show_list
(show_prod show_nat
  (show_prod (show_bexp show_nat show_int)
    (show_prod (show_list (show_acconstraint show_nat show_int))
      (show_prod (show_act show_nat)
        (show_prod (show_list (show_prod show_nat (show_exp show_nat show_int)))
          (show_prod (show_list show_nat) show_nat)))))))
                                      (show_list
(show_prod show_nat (show_list (show_acconstraint show_nat show_int))))))
                                  zero_nata a [])))) ()))
        automataa;
    val _ = writeln "Renaming formula";
    val formulab =
      (if dc then EX (Notb Truea)
        else map_formulaa renum_states renum_vars id formulaa);
    val _ = writeln "Renaming state";
    val l_0a = map_index zero_nata renum_states l_0;
    val s_0a = map (fn (x, a) => (renum_vars x, a)) s_0;
    val show_clock = (fn x => shows_prec G_ zero_nata x []) o inv_renum_clocks;
    val show_statea = show_state E_ F_ C_ inv_renum_states inv_renum_vars;
  in
    (if is_result renaming_valid
      then let
             val _ = writeln "Checking preconditions";
             val r =
               check_precond broadcasta boundsa automataa m num_states
                 num_actions k l_0a s_0a formulab;
             val _ =
               (case r of Result _ => ()
                 | Error es =>
                   let
                     val _ = writeln "";
                     val _ =
                       writeln "The following pre-conditions were not satisified:";
                     val _ = map (fn a => writeln a) es;
                   in
                     writeln ""
                   end);
             val _ = writeln "Running precond_mc";
             val a =
               f show_clock show_statea broadcasta boundsa automataa m
                 num_states
                 num_actions
                 k
                 l_0a
                 s_0a
                 formulab;
           in
             SOME a
           end
      else let
             val _ =
               writeln "The following conditions on the renaming were not satisfied:";
             val _ = map (fn a => writeln a) (the_errors renaming_valid);
           in
             NONE
           end)
  end;

fun rename_check_buechi num_split broadcast bounds automata k l_0 s_0 formula m
  num_states num_actions renum_acts renum_vars renum_clocks renum_states
  state_space =
  (case do_rename_mc show_int (show_list show_char) (show_list show_char)
          (show_list show_char)
          (fn _ => fn _ => buechi_certificate_checker num_split state_space)
          false broadcast bounds automata k "_urge" l_0 s_0 formula m num_states
          num_actions renum_acts renum_vars renum_clocks renum_states
          (fn _ => fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
          (fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
          (fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
    of NONE => Renaming_Failed | SOME true => Sat | SOME false => Unsat);

fun buechi_of (Buechi_Set x2) = x2;

fun reach_of (Reachable_Set x1) = x1;

fun check_diag_impl_inta x =
  (fn n => fn ai => fn bi =>
    imp_for_int zero_nata (suc ai) (fn sigma => (fn () => (not sigma)))
      (fn xb => fn sigma =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (xb, xb)) ()) ())
          (fn xa => (fn () => (dbm_lt_0 xa orelse sigma))))
      false)
    x;

fun dbm_subset_impl_inta x =
  (fn m => fn a => fn b =>
    imp_for_int zero_nata
      (times_nata (plus_nata m one_nata) (plus_nata m one_nata))
      (fn aa => (fn () => aa))
      (fn i => fn _ =>
        (fn f_ => fn () => f_ ((ntha (heap_DBMEntry heap_int) a i) ()) ())
          (fn xa =>
            (fn f_ => fn () => f_ ((ntha (heap_DBMEntry heap_int) b i) ()) ())
              (fn y => (fn () => (dbm_le_int xa y)))))
      true)
    x;

fun dbm_subset_impl_int x =
  (fn n => fn ai => fn bi =>
    (fn f_ => fn () => f_ ((check_diag_impl_inta n n ai) ()) ())
      (fn xa => (if xa then (fn () => true) else dbm_subset_impl_inta n ai bi)))
    x;

fun print_check_impl x = (fn ai => fn bi => (fn () => (print_check ai bi))) x;

fun certify_unreachable_impl_inner (A1_, A2_, A3_) B_ fi pi copyi lei succsi
  l_0i s_0i splitteri =
  (fn ai => fn bi =>
    (fn f_ => fn () => f_ ((start_timer_impl ()) ()) ())
      (fn _ =>
        (fn f_ => fn () => f_ (l_0i ()) ())
          (fn x =>
            (fn f_ => fn () => f_
              ((imp_nfoldli ai (fn sigma => (fn () => (not sigma)))
                 (fn xb => fn _ => (fn () => (eq A1_ xb x))) false)
              ()) ())
              (fn xa =>
                (fn f_ => fn () => f_ (l_0i ()) ())
                  (fn xaa =>
                    (fn f_ => fn () => f_ (s_0i ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_ ((pi (xaa, xb)) ()) ())
                          (fn xab =>
                            (fn f_ => fn () => f_ (l_0i ()) ())
                              (fn xba =>
                                (fn f_ => fn () => f_
                                  ((hms_lookup
                                     (ht_lookup (A1_, A2_, A3_) (heap_list B_))
                                     (heap_map copyi) xba bi)
                                  ()) ())
                                  (fn xbb =>
                                    (fn f_ => fn () => f_
                                      ((case xbb of NONE => (fn () => false)
 | SOME x_d =>
   (fn f_ => fn () => f_
     ((imp_nfoldli x_d (fn sigma => (fn () => (not sigma)))
        (fn xg => fn _ =>
          (fn f_ => fn () => f_ (s_0i ()) ()) (fn x_h => lei x_h xg))
        false)
     ()) ())
     (fn x_f =>
       (fn f_ => fn () => f_
         ((imp_nfoldli ai (fn a => (fn () => a))
            (fn xbc => fn _ =>
              (fn f_ => fn () => f_
                ((hms_lookup (ht_lookup (A1_, A2_, A3_) (heap_list B_))
                   (heap_map copyi) xbc bi)
                ()) ())
                (fn a =>
                  (case a of NONE => (fn () => true)
                    | SOME x_e =>
                      imp_nfoldli x_e (fn aa => (fn () => aa))
                        (fn xh => fn _ => pi (xbc, xh)) true)))
            true)
         ()) ())
         (fn x_g =>
           (fn f_ => fn () => f_
             ((print_check_impl "Start state is in state list" xa) ()) ())
             (fn _ =>
               (fn f_ => fn () => f_
                 ((print_check_impl "Start state fulfills property" xab) ()) ())
                 (fn _ =>
                   (fn f_ => fn () => f_
                     ((print_check_impl "Start state is subsumed" x_f) ()) ())
                     (fn _ =>
                       (fn f_ => fn () => f_
                         ((print_check_impl "Check property" x_g) ()) ())
                         (fn _ =>
                           (fn () =>
                             (xa andalso
                               (xab andalso (x_f andalso x_g)))))))))))
                                      ()) ())
                                      (fn xc =>
(fn f_ => fn () => f_
  ((if xc
     then (fn f_ => fn () => f_
            (((fn f_ => fn () => f_
                (((fn f => fn xs => fn () => Par_List.map (fn x => f x ()) xs) (fn
  l =>
 imp_nfoldli l (fn a => (fn () => a))
   (fn xac => fn _ =>
     (fn f_ => fn () => f_
       ((hms_lookup (ht_lookup (A1_, A2_, A3_) (heap_list B_)) (heap_map copyi)
          xac bi)
       ()) ())
       (fn a =>
         (case a of NONE => (fn () => true)
           | SOME x_c =>
             (fn f_ => fn () => f_ ((succsi xac x_c) ()) ())
               (fn x_d =>
                 imp_nfoldli x_d (fn aa => (fn () => aa))
                   (fn xg => fn _ =>
                     let
                       val (a1, a2) = xg;
                     in
                       (if op_list_is_empty a2 then (fn () => true)
                         else (fn f_ => fn () => f_
                                ((hms_lookup
                                   (ht_lookup (A1_, A2_, A3_) (heap_list B_))
                                   (heap_map copyi) a1 bi)
                                ()) ())
                                (fn aa =>
                                  (case aa of NONE => (fn () => false)
                                    | SOME x_k =>
                                      imp_nfoldli a2 (fn ab => (fn () => ab))
(fn xn => fn _ =>
  imp_nfoldli x_k (fn sigma => (fn () => (not sigma)))
    (fn xp => fn _ => lei xn xp) false)
true)))
                     end)
                   true))))
   true) (splitteri ai))
                ()) ())
               (fn bs => (fn () => (list_all id bs))))
            ()) ())
            (fn x_b =>
              (fn f_ => fn () => f_
                ((print_check_impl "State set invariant check" x_b) ()) ())
                (fn _ => (fn () => x_b)))
     else (fn () => false))
  ()) ())
  (fn x_a =>
    (fn f_ => fn () => f_
      ((save_time_impl "Time for state space invariant check") ()) ())
      (fn _ =>
        (fn f_ => fn () => f_ ((start_timer_impl ()) ()) ())
          (fn _ =>
            (fn f_ => fn () => f_
              ((imp_nfoldli ai (fn a => (fn () => a))
                 (fn xbc => fn _ =>
                   (fn f_ => fn () => f_
                     ((hms_lookup (ht_lookup (A1_, A2_, A3_) (heap_list B_))
                        (heap_map copyi) xbc bi)
                     ()) ())
                     (fn a =>
                       (case a of NONE => (fn () => true)
                         | SOME x_e =>
                           imp_nfoldli x_e (fn aa => (fn () => aa))
                             (fn xh => fn _ =>
                               (fn f_ => fn () => f_ ((fi (xbc, xh)) ()) ())
                                 (fn x_i => (fn () => (not x_i))))
                             true)))
                 true)
              ()) ())
              (fn x_d =>
                (fn f_ => fn () => f_
                  ((save_time_impl "Time to check final state predicate") ())
                  ())
                  (fn _ =>
                    (fn f_ => fn () => f_ ((print_check_impl "All check: " x_a)
                      ()) ())
                      (fn _ =>
                        (fn f_ => fn () => f_
                          ((print_check_impl "Target property check: " x_d) ())
                          ())
                          (fn _ =>
                            (fn () => (x_a andalso x_d)))))))))))))))))));

fun split_eq_width n = split_size (fn _ => one_nata) n zero_nata [];

fun split_k k xs =
  let
    val width = divide_nat (size_list xs) k;
    val widtha =
      (if equal_nata (modulo_nat (size_list xs) k) zero_nata then width
        else plus_nata width one_nata);
  in
    split_eq_width widtha xs
  end;

fun unreachability_checker broadcast bounds automata m num_states num_actions
  l_0 s_0 formula l_list m_list num_split =
  let
    val states_ia =
      map (states_i automata) (upt zero_nata (size_list automata));
    val check_states =
      (fn (l, s) =>
        equal_nata (size_list l) (size_list automata) andalso
          let
            val d = minus_nata (size_list automata) one_nata;
          in
            (if less_nat d (size_list automata)
              then all_interval (equal_nat, interval_nat)
                     (fn i =>
                       member (ceq_nat, ccompare_nat) (nth l i)
                         (nth states_ia i))
                     zero_nata d
              else true)
          end andalso
          (equal_nata (size_list s) (n_vs bounds) andalso
            check_boundedi bounds s));
    val fi = (fn xi => (fn () => let
                                   val ((a, b), _) = xi;
                                 in
                                   hd_of_formulai equal_nat formula a b
                                 end));
    val pi =
      (fn (a1, a2) =>
        (fn f_ => fn () => f_
          ((imp_for_int zero_nata (plus_nata m one_nata) (fn a => (fn () => a))
             (fn xc => fn _ =>
               imp_for_int zero_nata (plus_nata m one_nata)
                 (fn a => (fn () => a))
                 (fn xf => fn _ =>
                   imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xj => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xj))
                         ()) ())
                         (fn x_i =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (xc, xf))
                             ()) ())
                             (fn x =>
                               (fn f_ => fn () => f_
                                 ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                    (xf, xj))
                                 ()) ())
                                 (fn xa =>
                                   (fn () =>
                                     (dbm_le_int x_i (dbm_add_int x xa)))))))
                     true)
                 true)
             true)
          ()) ())
          (fn x =>
            (fn f_ => fn () => f_ ((check_diag_impl_int m a2) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_
                  ((imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xc => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xc))
                         ()) ())
                         (fn x_d => (fn () => (dbm_le_int x_d (Le zero_inta)))))
                     true)
                  ()) ())
                  (fn xb =>
                    (fn f_ => fn () => f_
                      ((imp_for_int zero_nata (plus_nata m one_nata)
                         (fn a => (fn () => a))
                         (fn xc => fn _ =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (zero_nata, xc))
                             ()) ())
                             (fn x_e =>
                               (fn () => (dbm_le_int x_e (Le zero_inta)))))
                         true)
                      ()) ())
                      (fn xc =>
                        (fn () =>
                          (check_states a1 andalso
                            ((x orelse xa) andalso (xb andalso xc)))))))));
    val copyi = amtx_copy (heap_DBMEntry heap_int);
    val lei = dbm_subset_impl_int m;
    val l_0i =
      (fn () =>
        (l_0, map (the o map_of equal_nat s_0) (upt zero_nata (n_vs bounds))));
    val s_0i =
      amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m) (Le zero_inta);
    val succsi =
      let
        val n_ps = size_list automata;
        val invs =
          Vector.fromList
            (map (fn i =>
                   let
                     val ma =
                       default_map_of equal_nat []
                         (snd (snd (snd (nth automata i))));
                     val mb =
                       Vector.fromList (map ma (upt zero_nata (num_states i)));
                   in
                     mb
                   end)
              (upt zero_nata n_ps));
        val inv_fun =
          (fn (l, _) =>
            maps (fn i => sub (sub invs i) (nth l i)) (upt zero_nata n_ps));
        val trans_mapa = trans_map automata;
        val trans_i_map =
          (fn i => fn j =>
            map_filter
              (fn a =>
                (case a of (_, (_, (In _, (_, _)))) => NONE
                  | (_, (_, (Out _, (_, _)))) => NONE
                  | (b, (g, (Sil aa, (ma, l)))) =>
                    SOME (b, (g, (aa, (ma, l))))))
              (trans_mapa i j));
        val int_trans_from_loc_impl =
          (fn p => fn l => fn la => fn s =>
            let
              val a = trans_i_map p l;
            in
              map_filter
                (fn (b, (g, (aa, (f, (r, lb))))) =>
                  let
                    val sa = mk_updsi s f;
                  in
                    (if bvali (equal_int, linorder_int) s b andalso
                          check_boundedi bounds sa
                      then SOME (g, (Internal aa,
                                      (r, (list_update la p lb, sa))))
                      else NONE)
                  end)
                a
            end);
        val int_trans_from_vec_impl =
          (fn pairs => fn l => fn s =>
            maps (fn (p, la) => int_trans_from_loc_impl p la l s) pairs);
        val int_trans_from_all_impl =
          (fn l => fn s =>
            maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
              (upt zero_nata n_ps));
        val trans_out_map =
          (fn i => fn j =>
            map_filter
              (fn a =>
                (case a of (_, (_, (In _, (_, _)))) => NONE
                  | (b, (g, (Out aa, (ma, l)))) => SOME (b, (g, (aa, (ma, l))))
                  | (_, (_, (Sil _, (_, _)))) => NONE))
              (trans_mapa i j));
        val trans_in_map =
          (fn i => fn j =>
            map_filter
              (fn a =>
                (case a
                  of (b, (g, (In aa, (ma, l)))) => SOME (b, (g, (aa, (ma, l))))
                  | (_, (_, (Out _, (_, _)))) => NONE
                  | (_, (_, (Sil _, (_, _)))) => NONE))
              (trans_mapa i j));
        val trans_out_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn a =>
                  (case a of (_, (_, (In _, (_, _)))) => NONE
                    | (b, (g, (Out aa, (ma, l)))) =>
                      (if membera equal_nat broadcast aa
                        then SOME (b, (g, (aa, (ma, l)))) else NONE)
                    | (_, (_, (Sil _, (_, _)))) => NONE))
                (trans_mapa i j)));
        val trans_in_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn a =>
                  (case a
                    of (b, (g, (In aa, (ma, l)))) =>
                      (if membera equal_nat broadcast aa
                        then SOME (b, (g, (aa, (ma, l)))) else NONE)
                    | (_, (_, (Out _, (_, _)))) => NONE
                    | (_, (_, (Sil _, (_, _)))) => NONE))
                (trans_mapa i j)));
        val broad_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_committed broadcast bounds automata l;
              val ina =
                map (fn p => trans_in_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val out =
                map (fn p => trans_out_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val inb =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  ina;
              val outa =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  out;
            in
              (if null pairs
                then maps (fn a =>
                            maps (fn p =>
                                   let
                                     val outs = nth (nth outa p) a;
                                   in
                                     (if null outs then []
                                       else let
      val combs = make_combs broadcast bounds automata p a inb;
      val outsa = map (fn aa => (p, aa)) outs;
      val combsa =
        (if null combs then map (fn x => [x]) outsa
          else maps (fn x => map (fn aa => x :: aa) combs) outsa);
      val init = ([], (Broad a, ([], (l, s))));
    in
      compute_upds_impl bounds init combsa
    end)
                                   end)
                              (upt zero_nata n_ps))
                       (upt zero_nata num_actions)
                else maps (fn a =>
                            let
                              val ins_committed =
                                map_filter
                                  (fn (p, _) =>
                                    (if not (null (nth (nth inb p) a))
                                      then SOME p else NONE))
                                  pairs;
                              val always_committed =
                                less_nat one_nata (size_list ins_committed);
                            in
                              maps (fn p =>
                                     let
                                       val outs = nth (nth outa p) a;
                                     in
                                       (if null outs then []
 else (if not always_committed andalso
            ((equal_lista equal_nat ins_committed [p] orelse
               null ins_committed) andalso
              not (list_ex (fn (q, _) => equal_nata q p) pairs))
        then []
        else let
               val combs = make_combs broadcast bounds automata p a inb;
               val outsa = map (fn aa => (p, aa)) outs;
               val combsa =
                 (if null combs then map (fn x => [x]) outsa
                   else maps (fn x => map (fn aa => x :: aa) combs) outsa);
               val init = ([], (Broad a, ([], (l, s))));
             in
               compute_upds_impl bounds init combsa
             end))
                                     end)
                                (upt zero_nata n_ps)
                            end)
                       (upt zero_nata num_actions))
            end);
        val bin_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_committed broadcast bounds automata l;
              val ina =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_in_map l;
              val out =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_out_map l;
            in
              (if null pairs
                then maps (fn a =>
                            pairs_by_action_impl bounds l s (nth out a)
                              (nth ina a))
                       (bin_actions broadcast num_actions)
                else let
                       val in2 =
                         all_actions_from_vec num_actions trans_in_map pairs;
                       val out2 =
                         all_actions_from_vec num_actions trans_out_map pairs;
                     in
                       maps (fn a =>
                              pairs_by_action_impl bounds l s (nth out a)
                                (nth in2 a))
                         (bin_actions broadcast num_actions) @
                         maps (fn a =>
                                pairs_by_action_impl bounds l s (nth out2 a)
                                  (nth ina a))
                           (bin_actions broadcast num_actions)
                     end)
            end);
        val int_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_committed broadcast bounds automata l;
            in
              (if null pairs then int_trans_from_all_impl l s
                else int_trans_from_vec_impl pairs l s)
            end);
        val trans_impl =
          (fn st =>
            int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st);
        val e_op_impl =
          (fn ai => fn bic => fn bib => fn bia => fn bi =>
            (fn f_ => fn () => f_ ((up_canonical_upd_impl_int m bi m) ()) ())
              (fn x =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli (inv_fun ai) (fn _ => (fn () => true))
                     (fn aia => fn bid =>
                       (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid)
                         ()) ())
                         (fn xa =>
                           repair_pair_impl_int m xa zero_nata
                             (constraint_clk aia)))
                     x)
                  ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((check_diag_impl_int m xa) ()) ())
                      (fn xaa =>
                        (fn f_ => fn () => f_
                          ((if xaa
                             then mtx_set (heap_DBMEntry heap_int) (suc m) xa
                                    (zero_nata, zero_nata) (Lt zero_inta)
                             else imp_nfoldli bib (fn _ => (fn () => true))
                                    (fn aia => fn bid =>
                                      (fn f_ => fn () => f_
((abstra_upd_impl_int m aia bid) ()) ())
(fn xb => repair_pair_impl_int m xb zero_nata (constraint_clk aia)))
                                    xa)
                          ()) ())
                          (fn x_a =>
                            (fn f_ => fn () => f_ ((check_diag_impl_int m x_a)
                              ()) ())
                              (fn x_b =>
                                (if x_b
                                  then mtx_set (heap_DBMEntry heap_int) (suc m)
 x_a (zero_nata, zero_nata) (Lt zero_inta)
                                  else (fn f_ => fn () => f_
 ((imp_nfoldli bic (fn _ => (fn () => true))
    (fn xc => fn sigma => reset_canonical_upd_impl_int m sigma m xc zero_inta)
    x_a)
 ()) ())
 (imp_nfoldli (inv_fun bia) (fn _ => (fn () => true))
   (fn aia => fn bid =>
     (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
       (fn xb =>
         repair_pair_impl_int m xb zero_nata (constraint_clk aia)))))))))));
      in
        (fn ai => fn bi =>
          (if null bi then (fn () => [])
            else imp_nfoldli (trans_impl ai) (fn _ => (fn () => true))
                   (fn xc => fn sigma =>
                     let
                       val (a1, (_, (a1b, a2b))) = xc;
                     in
                       (fn f_ => fn () => f_
                         ((heap_map (amtx_copy (heap_DBMEntry heap_int)) bi) ())
                         ())
                         (fn x =>
                           (fn f_ => fn () => f_
                             ((imp_nfoldli x (fn _ => (fn () => true))
                                (fn xb => fn sigmaa =>
                                  (fn f_ => fn () => f_
                                    ((pR_CONST e_op_impl ai a1b a1 a2b xb) ())
                                    ())
                                    (fn x_c =>
                                      (fn f_ => fn () => f_
((check_diag_impl_int m x_c) ()) ())
(fn x_e => (fn () => (if x_e then sigmaa else op_list_prepend x_c sigmaa)))))
                                [])
                             ()) ())
                             (fn x_d =>
                               (fn () => (op_list_prepend (a2b, x_d) sigma))))
                     end)
                   []))
      end;
    val _ = Timing.start_timer ();
  in
    (fn f_ => fn () => f_
      (((fn f_ => fn () => f_
          ((ht_new
             (hashable_prod (hashable_list hashable_nat)
                (hashable_list hashable_int),
               heap_prod (heap_list heap_nat) (heap_list heap_int))
             (heap_list (heap_array (typerep_DBMEntry typerep_int))))
          ()) ())
         (imp_nfoldli m_list (fn _ => (fn () => true))
           (fn xc => fn sigma =>
             (fn f_ => fn () => f_
               ((imp_nfoldli (snd xc) (fn _ => (fn () => true))
                  (fn xg => fn sigmaa =>
                    (fn f_ => fn () => f_ (((fn () => Array.fromList xg)) ())
                      ())
                      (fn x_g => (fn () => (x_g :: sigmaa))))
                  [])
               ()) ())
               (fn x_e =>
                 ht_update
                   (equal_prod (equal_list equal_nat) (equal_list equal_int),
                     hashable_prod (hashable_list hashable_nat)
                       (hashable_list hashable_int),
                     heap_prod (heap_list heap_nat) (heap_list heap_int))
                   (heap_list (heap_array (typerep_DBMEntry typerep_int)))
                   (fst xc) x_e sigma))))
      ()) ())
      (fn m_table =>
        let
          val _ = Timing.save_time "Time for loading certificate";
        in
          (fn f_ => fn () => f_
            ((certify_unreachable_impl_inner
               (equal_prod (equal_list equal_nat) (equal_list equal_int),
                 hashable_prod (hashable_list hashable_nat)
                   (hashable_list hashable_int),
                 heap_prod (heap_list heap_nat) (heap_list heap_int))
               (heap_array (typerep_DBMEntry typerep_int)) fi pi copyi lei
               succsi l_0i s_0i (split_k num_split) l_list m_table)
            ()) ())
            (fn a => (fn () => a))
        end)
  end;

fun make_stringa (A1_, A2_) show_clock show_num e i j =
  let
    val ia =
      (if less_nat zero_nata i then show_clock i
        else [Chara (false, false, false, false, true, true, false, false)]);
    val ja =
      (if less_nat zero_nata j then show_clock j
        else [Chara (false, false, false, false, true, true, false, false)]);
  in
    (case e
      of Le a =>
        ia @ [Chara (false, false, false, false, false, true, false, false),
               Chara (true, false, true, true, false, true, false, false),
               Chara (false, false, false, false, false, true, false, false)] @
               ja @ [Chara (false, false, false, false, false, true, false,
                             false),
                      Chara (false, false, true, true, true, true, false,
                              false),
                      Chara (true, false, true, true, true, true, false, false),
                      Chara (false, false, false, false, false, true, false,
                              false)] @
                      show_num a
      | Lt a =>
        ia @ [Chara (false, false, false, false, false, true, false, false),
               Chara (true, false, true, true, false, true, false, false),
               Chara (false, false, false, false, false, true, false, false)] @
               ja @ [Chara (false, false, false, false, false, true, false,
                             false),
                      Chara (false, false, true, true, true, true, false,
                              false),
                      Chara (false, false, false, false, false, true, false,
                              false)] @
                      show_num a
      | INF =>
        ia @ [Chara (false, false, false, false, false, true, false, false),
               Chara (true, false, true, true, false, true, false, false),
               Chara (false, false, false, false, false, true, false, false)] @
               ja @ [Chara (false, false, false, false, false, true, false,
                             false),
                      Chara (false, false, true, true, true, true, false,
                              false),
                      Chara (false, false, false, false, false, true, false,
                              false),
                      Chara (true, false, false, true, false, true, true,
                              false),
                      Chara (false, true, true, true, false, true, true, false),
                      Chara (false, true, true, false, false, true, true,
                              false)])
  end;

fun dbm_list_to_stringa (A1_, A2_) n show_clock show_num xs =
  app (concat o
         intersperse
           [Chara (false, false, true, true, false, true, false, false),
             Chara (false, false, false, false, false, true, false, false)] o
         rev o
         snd o
        snd)
    (fold (fn e => fn (i, (j, acc)) =>
            let
              val s = make_stringa (A1_, A2_) show_clock show_num e i j;
              val ja = modulo_nat (plus_nata j one_nata) (plus_nata n one_nata);
              val ia =
                (if equal_nata ja zero_nata then plus_nata i one_nata else i);
            in
              (ia, (ja, s :: acc))
            end)
      xs (zero_nata, (zero_nata, [])));

fun dbm_to_list_impl (A1_, A2_) n =
  (fn xi =>
    (fn f_ => fn () => f_
      ((imp_for_inta zero_nata (suc n)
         (fn xc =>
           imp_for_inta zero_nata (suc n)
             (fn xe => fn sigma =>
               (fn f_ => fn () => f_ ((mtx_get A2_ (suc n) xi (xc, xe)) ()) ())
                 (fn x_e => (fn () => (x_e :: sigma)))))
         [])
      ()) ())
      (fn x => (fn () => (op_list_rev x))));

fun show_dbm_impl_all (A1_, A2_, A3_) n show_clock show_num =
  (fn xi =>
    (fn f_ => fn () => f_
      ((dbm_to_list_impl
         (linordered_ab_monoid_add_DBMEntry
            (linordered_cancel_ab_monoid_add_linordered_ab_group_add A1_, A2_),
           heap_DBMEntry A3_)
         n xi)
      ()) ())
      (fn x =>
        (fn () => (dbm_list_to_stringa (A1_, A3_) n show_clock show_num x))));

fun check_invariant_fail_impl A_ (B1_, B2_, B3_) copyi lei succsi =
  (fn ai => fn bi =>
    imp_nfoldli ai (fn sigma => (fn () => (is_None sigma)))
      (fn xb => fn _ =>
        (fn f_ => fn () => f_
          ((hms_lookup (ht_lookup (B1_, B2_, B3_) (heap_list A_))
             (heap_map copyi) xb bi)
          ()) ())
          (fn x =>
            (fn f_ => fn () => f_
              ((case x of NONE => (fn () => NONE)
                 | SOME x_d =>
                   (fn f_ => fn () => f_ ((succsi xb x_d) ()) ())
                     (fn x_e =>
                       imp_nfoldli x_e (fn sigma => (fn () => (is_None sigma)))
                         (fn xh => fn _ =>
                           (fn f_ => fn () => f_
                             (let
                                val (a1, a2) = xh;
                              in
                                (if op_list_is_empty a2 then (fn () => NONE)
                                  else (fn f_ => fn () => f_
 ((imp_nfoldli ai (fn sigma => (fn () => (not sigma)))
    (fn xba => fn _ => (fn () => (eq B1_ xba a1))) false)
 ()) ())
 (fn x_k =>
   (if x_k
     then (fn f_ => fn () => f_
            ((hms_lookup (ht_lookup (B1_, B2_, B3_) (heap_list A_))
               (heap_map copyi) a1 bi)
            ()) ())
            (fn a =>
              (case a of NONE => (fn () => (SOME (Inl (Inr (xb, (a1, a2))))))
                | SOME x_m =>
                  (fn f_ => fn () => f_
                    ((imp_nfoldli a2 (fn sigma => (fn () => (is_None sigma)))
                       (fn xp => fn _ =>
                         (fn f_ => fn () => f_
                           ((imp_nfoldli x_m
                              (fn sigma => (fn () => (not sigma)))
                              (fn xr => fn _ =>
                                (fn f_ => fn () => f_ ((copyi xp) ()) ())
                                  (fn x_s => lei x_s xr))
                              false)
                           ()) ())
                           (fn x_q =>
                             (fn () => (if x_q then NONE else SOME xp))))
                       NONE)
                    ()) ())
                    (fn aa =>
                      (case aa of NONE => (fn () => NONE)
                        | SOME x_p =>
                          (fn f_ => fn () => f_
                            ((hms_lookup
                               (ht_lookup (B1_, B2_, B3_) (heap_list A_))
                               (heap_map copyi) xb bi)
                            ()) ())
                            (fn x_q =>
                              (fn () =>
                                (case x_q
                                  of NONE => SOME (Inl (Inr (xb, (a1, x_m))))
                                  | SOME x_r =>
                                    SOME (Inr
   (xb, (x_r, (a1, (x_p, x_m))))))))))))
     else (fn () => (SOME (Inl (Inl (xb, (a1, a2)))))))))
                              end
                             ()) ())
                             (fn x_i =>
                               (fn () =>
                                 (case x_i of NONE => NONE
                                   | SOME a => SOME a))))
                         NONE))
              ()) ())
              (fn x_c =>
                (fn () => (case x_c of NONE => NONE | SOME a => SOME a)))))
      NONE);

fun check_invariant_fail broadcast bounds automata m num_states num_actions
  show_clock show_state =
  (fn l_list => fn m_list =>
    let
      val copy = amtx_copy (heap_DBMEntry heap_int);
      val succs =
        let
          val n_ps = size_list automata;
          val invs =
            Vector.fromList
              (map (fn i =>
                     let
                       val ma =
                         default_map_of equal_nat []
                           (snd (snd (snd (nth automata i))));
                       val mb =
                         Vector.fromList
                           (map ma (upt zero_nata (num_states i)));
                     in
                       mb
                     end)
                (upt zero_nata n_ps));
          val inv_fun =
            (fn (l, _) =>
              maps (fn i => sub (sub invs i) (nth l i)) (upt zero_nata n_ps));
          val trans_mapa = trans_map automata;
          val trans_i_map =
            (fn i => fn j =>
              map_filter
                (fn a =>
                  (case a of (_, (_, (In _, (_, _)))) => NONE
                    | (_, (_, (Out _, (_, _)))) => NONE
                    | (b, (g, (Sil aa, (ma, l)))) =>
                      SOME (b, (g, (aa, (ma, l))))))
                (trans_mapa i j));
          val int_trans_from_loc_impl =
            (fn p => fn l => fn la => fn s =>
              let
                val a = trans_i_map p l;
              in
                map_filter
                  (fn (b, (g, (aa, (f, (r, lb))))) =>
                    let
                      val sa = mk_updsi s f;
                    in
                      (if bvali (equal_int, linorder_int) s b andalso
                            check_boundedi bounds sa
                        then SOME (g, (Internal aa,
(r, (list_update la p lb, sa))))
                        else NONE)
                    end)
                  a
              end);
          val int_trans_from_vec_impl =
            (fn pairs => fn l => fn s =>
              maps (fn (p, la) => int_trans_from_loc_impl p la l s) pairs);
          val int_trans_from_all_impl =
            (fn l => fn s =>
              maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
                (upt zero_nata n_ps));
          val trans_out_map =
            (fn i => fn j =>
              map_filter
                (fn a =>
                  (case a of (_, (_, (In _, (_, _)))) => NONE
                    | (b, (g, (Out aa, (ma, l)))) =>
                      SOME (b, (g, (aa, (ma, l))))
                    | (_, (_, (Sil _, (_, _)))) => NONE))
                (trans_mapa i j));
          val trans_in_map =
            (fn i => fn j =>
              map_filter
                (fn a =>
                  (case a
                    of (b, (g, (In aa, (ma, l)))) =>
                      SOME (b, (g, (aa, (ma, l))))
                    | (_, (_, (Out _, (_, _)))) => NONE
                    | (_, (_, (Sil _, (_, _)))) => NONE))
                (trans_mapa i j));
          val trans_out_broad_grouped =
            (fn i => fn j =>
              actions_by_statea num_actions
                (map_filter
                  (fn a =>
                    (case a of (_, (_, (In _, (_, _)))) => NONE
                      | (b, (g, (Out aa, (ma, l)))) =>
                        (if membera equal_nat broadcast aa
                          then SOME (b, (g, (aa, (ma, l)))) else NONE)
                      | (_, (_, (Sil _, (_, _)))) => NONE))
                  (trans_mapa i j)));
          val trans_in_broad_grouped =
            (fn i => fn j =>
              actions_by_statea num_actions
                (map_filter
                  (fn a =>
                    (case a
                      of (b, (g, (In aa, (ma, l)))) =>
                        (if membera equal_nat broadcast aa
                          then SOME (b, (g, (aa, (ma, l)))) else NONE)
                      | (_, (_, (Out _, (_, _)))) => NONE
                      | (_, (_, (Sil _, (_, _)))) => NONE))
                  (trans_mapa i j)));
          val broad_trans_impl =
            (fn (l, s) =>
              let
                val pairs = get_committed broadcast bounds automata l;
                val ina =
                  map (fn p => trans_in_broad_grouped p (nth l p))
                    (upt zero_nata n_ps);
                val out =
                  map (fn p => trans_out_broad_grouped p (nth l p))
                    (upt zero_nata n_ps);
                val inb =
                  map (map (filter
                             (fn (b, _) =>
                               bvali (equal_int, linorder_int) s b)))
                    ina;
                val outa =
                  map (map (filter
                             (fn (b, _) =>
                               bvali (equal_int, linorder_int) s b)))
                    out;
              in
                (if null pairs
                  then maps (fn a =>
                              maps (fn p =>
                                     let
                                       val outs = nth (nth outa p) a;
                                     in
                                       (if null outs then []
 else let
        val combs = make_combs broadcast bounds automata p a inb;
        val outsa = map (fn aa => (p, aa)) outs;
        val combsa =
          (if null combs then map (fn x => [x]) outsa
            else maps (fn x => map (fn aa => x :: aa) combs) outsa);
        val init = ([], (Broad a, ([], (l, s))));
      in
        compute_upds_impl bounds init combsa
      end)
                                     end)
                                (upt zero_nata n_ps))
                         (upt zero_nata num_actions)
                  else maps (fn a =>
                              let
                                val ins_committed =
                                  map_filter
                                    (fn (p, _) =>
                                      (if not (null (nth (nth inb p) a))
then SOME p else NONE))
                                    pairs;
                                val always_committed =
                                  less_nat one_nata (size_list ins_committed);
                              in
                                maps (fn p =>
                                       let
 val outs = nth (nth outa p) a;
                                       in
 (if null outs then []
   else (if not always_committed andalso
              ((equal_lista equal_nat ins_committed [p] orelse
                 null ins_committed) andalso
                not (list_ex (fn (q, _) => equal_nata q p) pairs))
          then []
          else let
                 val combs = make_combs broadcast bounds automata p a inb;
                 val outsa = map (fn aa => (p, aa)) outs;
                 val combsa =
                   (if null combs then map (fn x => [x]) outsa
                     else maps (fn x => map (fn aa => x :: aa) combs) outsa);
                 val init = ([], (Broad a, ([], (l, s))));
               in
                 compute_upds_impl bounds init combsa
               end))
                                       end)
                                  (upt zero_nata n_ps)
                              end)
                         (upt zero_nata num_actions))
              end);
          val bin_trans_impl =
            (fn (l, s) =>
              let
                val pairs = get_committed broadcast bounds automata l;
                val ina =
                  all_actions_by_state broadcast bounds automata num_actions
                    trans_in_map l;
                val out =
                  all_actions_by_state broadcast bounds automata num_actions
                    trans_out_map l;
              in
                (if null pairs
                  then maps (fn a =>
                              pairs_by_action_impl bounds l s (nth out a)
                                (nth ina a))
                         (bin_actions broadcast num_actions)
                  else let
                         val in2 =
                           all_actions_from_vec num_actions trans_in_map pairs;
                         val out2 =
                           all_actions_from_vec num_actions trans_out_map pairs;
                       in
                         maps (fn a =>
                                pairs_by_action_impl bounds l s (nth out a)
                                  (nth in2 a))
                           (bin_actions broadcast num_actions) @
                           maps (fn a =>
                                  pairs_by_action_impl bounds l s (nth out2 a)
                                    (nth ina a))
                             (bin_actions broadcast num_actions)
                       end)
              end);
          val int_trans_impl =
            (fn (l, s) =>
              let
                val pairs = get_committed broadcast bounds automata l;
              in
                (if null pairs then int_trans_from_all_impl l s
                  else int_trans_from_vec_impl pairs l s)
              end);
          val trans_impl =
            (fn st =>
              int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st);
          val e_op_impl =
            (fn ai => fn bic => fn bib => fn bia => fn bi =>
              (fn f_ => fn () => f_ ((up_canonical_upd_impl_int m bi m) ()) ())
                (fn x =>
                  (fn f_ => fn () => f_
                    ((imp_nfoldli (inv_fun ai) (fn _ => (fn () => true))
                       (fn aia => fn bid =>
                         (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid)
                           ()) ())
                           (fn xa =>
                             repair_pair_impl_int m xa zero_nata
                               (constraint_clk aia)))
                       x)
                    ()) ())
                    (fn xa =>
                      (fn f_ => fn () => f_ ((check_diag_impl_int m xa) ()) ())
                        (fn xaa =>
                          (fn f_ => fn () => f_
                            ((if xaa
                               then mtx_set (heap_DBMEntry heap_int) (suc m) xa
                                      (zero_nata, zero_nata) (Lt zero_inta)
                               else imp_nfoldli bib (fn _ => (fn () => true))
                                      (fn aia => fn bid =>
(fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
  (fn xb => repair_pair_impl_int m xb zero_nata (constraint_clk aia)))
                                      xa)
                            ()) ())
                            (fn x_a =>
                              (fn f_ => fn () => f_ ((check_diag_impl_int m x_a)
                                ()) ())
                                (fn x_b =>
                                  (if x_b
                                    then mtx_set (heap_DBMEntry heap_int)
   (suc m) x_a (zero_nata, zero_nata) (Lt zero_inta)
                                    else (fn f_ => fn () => f_
   ((imp_nfoldli bic (fn _ => (fn () => true))
      (fn xc => fn sigma => reset_canonical_upd_impl_int m sigma m xc zero_inta)
      x_a)
   ()) ())
   (imp_nfoldli (inv_fun bia) (fn _ => (fn () => true))
     (fn aia => fn bid =>
       (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
         (fn xb =>
           repair_pair_impl_int m xb zero_nata (constraint_clk aia)))))))))));
        in
          (fn ai => fn bi =>
            (if null bi then (fn () => [])
              else imp_nfoldli (trans_impl ai) (fn _ => (fn () => true))
                     (fn xc => fn sigma =>
                       let
                         val (a1, (_, (a1b, a2b))) = xc;
                       in
                         (fn f_ => fn () => f_
                           ((heap_map (amtx_copy (heap_DBMEntry heap_int)) bi)
                           ()) ())
                           (fn x =>
                             (fn f_ => fn () => f_
                               ((imp_nfoldli x (fn _ => (fn () => true))
                                  (fn xb => fn sigmaa =>
                                    (fn f_ => fn () => f_
                                      ((pR_CONST e_op_impl ai a1b a1 a2b xb) ())
                                      ())
                                      (fn x_c =>
(fn f_ => fn () => f_ ((check_diag_impl_int m x_c) ()) ())
  (fn x_e => (fn () => (if x_e then sigmaa else op_list_prepend x_c sigmaa)))))
                                  [])
                               ()) ())
                               (fn x_d =>
                                 (fn () => (op_list_prepend (a2b, x_d) sigma))))
                       end)
                     []))
        end;
      val lei = dbm_subset_impl_int m;
      val show_statea = (fn l => let
                                   val s = show_state l;
                                   val a = implode s;
                                 in
                                   (fn () => a)
                                 end);
      val show_dbm =
        show_dbm_impl_all (linordered_ab_group_add_int, equal_int, heap_int) m
          show_clock (fn x => shows_prec_int zero_nata x []);
    in
      (fn f_ => fn () => f_
        (((fn f_ => fn () => f_
            ((ht_new
               (hashable_prod (hashable_list hashable_nat)
                  (hashable_list hashable_int),
                 heap_prod (heap_list heap_nat) (heap_list heap_int))
               (heap_list (heap_array (typerep_DBMEntry typerep_int))))
            ()) ())
           (imp_nfoldli m_list (fn _ => (fn () => true))
             (fn xc => fn sigma =>
               (fn f_ => fn () => f_
                 ((imp_nfoldli (snd xc) (fn _ => (fn () => true))
                    (fn xg => fn sigmaa =>
                      (fn f_ => fn () => f_ (((fn () => Array.fromList xg)) ())
                        ())
                        (fn x_g => (fn () => (x_g :: sigmaa))))
                    [])
                 ()) ())
                 (fn x_e =>
                   ht_update
                     (equal_prod (equal_list equal_nat) (equal_list equal_int),
                       hashable_prod (hashable_list hashable_nat)
                         (hashable_list hashable_int),
                       heap_prod (heap_list heap_nat) (heap_list heap_int))
                     (heap_list (heap_array (typerep_DBMEntry typerep_int)))
                     (fst xc) x_e sigma))))
        ()) ())
        (fn m_table =>
          (fn f_ => fn () => f_
            ((check_invariant_fail_impl
               (heap_array (typerep_DBMEntry typerep_int))
               (equal_prod (equal_list equal_nat) (equal_list equal_int),
                 hashable_prod (hashable_list hashable_nat)
                   (hashable_list hashable_int),
                 heap_prod (heap_list heap_nat) (heap_list heap_int))
               copy lei succs l_list m_table)
            ()) ())
            (fn a =>
              (case a of NONE => (fn () => ())
                | SOME (Inl (Inl (l, (la, xs)))) =>
                  let
                    val _ = writeln "The successor is not contained in L:";
                  in
                    (fn f_ => fn () => f_ ((show_statea l) ()) ())
                      (fn s =>
                        let
                          val _ = writeln ("  " ^ s);
                        in
                          (fn f_ => fn () => f_ ((show_statea la) ()) ())
                            (fn sa =>
                              let
                                val _ = writeln ("  " ^ sa);
                              in
                                (fn f_ => fn () => f_
                                  ((fold_map
                                     (fn ma =>
                                       (fn f_ => fn () => f_ ((show_dbm ma) ())
 ())
 (fn sb => let
             val _ = writeln (" " ^ implode sb);
           in
             (fn () => ())
           end))
                                     xs)
                                  ()) ())
                                  (fn _ => (fn () => ()))
                              end)
                        end)
                  end
                | SOME (Inl (Inr (l, (la, xs)))) =>
                  let
                    val _ = writeln "The successor is not empty:";
                  in
                    (fn f_ => fn () => f_ ((show_statea l) ()) ())
                      (fn s =>
                        let
                          val _ = writeln ("  " ^ s);
                        in
                          (fn f_ => fn () => f_ ((show_statea la) ()) ())
                            (fn sa =>
                              let
                                val _ = writeln ("  " ^ sa);
                              in
                                (fn f_ => fn () => f_
                                  ((fold_map
                                     (fn ma =>
                                       (fn f_ => fn () => f_ ((show_dbm ma) ())
 ())
 (fn sb => let
             val _ = writeln (" " ^ implode sb);
           in
             (fn () => ())
           end))
                                     xs)
                                  ()) ())
                                  (fn _ => (fn () => ()))
                              end)
                        end)
                  end
                | SOME (Inr (l, (asa, (la, (ma, xs))))) =>
                  (fn f_ => fn () => f_ ((show_statea l) ()) ())
                    (fn s1 =>
                      (fn f_ => fn () => f_ ((show_statea la) ()) ())
                        (fn s2 =>
                          (fn f_ => fn () => f_ ((show_dbm ma) ()) ())
                            (fn s3 =>
                              let
                                val _ =
                                  writeln ("\nA successor of the zones for:\n  " ^
    s1);
                              in
                                (fn f_ => fn () => f_
                                  ((fold_map
                                     (fn mb =>
                                       (fn f_ => fn () => f_ ((show_dbm mb) ())
 ())
 (fn s => let
            val _ = writeln ("\n" ^ implode s);
          in
            (fn () => ())
          end))
                                     asa)
                                  ()) ())
                                  (fn _ =>
                                    let
                                      val _ =
writeln ("\nis not subsumed:\n  " ^ s2 ^ "\n");
                                      val _ = writeln (implode s3 ^ "\n");
                                      val _ =
writeln "These are the candidate dbms:";
                                    in
                                      (fn f_ => fn () => f_
((fold_map
   (fn mb =>
     (fn f_ => fn () => f_ ((show_dbm mb) ()) ())
       (fn s => let
                  val _ = writeln ("\n" ^ implode s);
                in
                  (fn () => ())
                end))
   xs)
()) ())
(fn _ => let
           val _ = writeln "";
         in
           (fn () => ())
         end)
                                    end)
                              end))))))
    end);

fun abstr_upd_impl_int x =
  (fn n => fn ai =>
    imp_nfoldli ai (fn _ => (fn () => true)) (abstra_upd_impl_int n))
    x;

fun abstr_FW_impl_int x =
  (fn n => fn ai => fn bi =>
    (fn f_ => fn () => f_ ((abstr_upd_impl_int n ai bi) ()) ())
      (fw_impl_inta n))
    x;

fun down_impl_int x =
  (fn n =>
    imp_for_inta one_nata (suc n)
      (fn xb => fn sigma =>
        (fn f_ => fn () => f_
          ((imp_for_inta one_nata (suc n)
             (fn xe => fn sigmaa =>
               (fn f_ => fn () => f_
                 ((mtx_get (heap_DBMEntry heap_int) (suc n) sigma (xe, xb)) ())
                 ())
                 (fn x_f => (fn () => (min_int_entry x_f sigmaa))))
             (Le zero_inta))
          ()) ())
          (mtx_set (heap_DBMEntry heap_int) (suc n) sigma (zero_nata, xb))))
    x;

fun print_line_impl x = (fn xi => (fn () => (writeln xi))) x;

fun mk_st_string s1 s2 = "<" ^ s1 ^ ", " ^ s2 ^ ">";

fun check_prop_fail_impl (A1_, A2_, A3_) B_ pi copyi show_dbm_impl show_loc_impl
  = (fn ai => fn bi =>
      (fn f_ => fn () => f_
        ((imp_nfoldli ai (fn sigma => (fn () => (is_None sigma)))
           (fn xb => fn _ =>
             (fn f_ => fn () => f_
               ((hms_lookup (ht_lookup (A1_, A2_, A3_) (heap_list B_))
                  (heap_map copyi) xb bi)
               ()) ())
               (fn x =>
                 (fn f_ => fn () => f_
                   ((case x of NONE => (fn () => NONE)
                      | SOME x_e =>
                        (fn f_ => fn () => f_
                          ((imp_nfoldli x_e
                             (fn sigma => (fn () => (is_None sigma)))
                             (fn xh => fn _ =>
                               (fn f_ => fn () => f_ ((copyi xh) ()) ())
                                 (fn xa =>
                                   (fn f_ => fn () => f_ ((pi (xb, xa)) ()) ())
                                     (fn x_i =>
                                       (fn () =>
 (if x_i then NONE else SOME xh)))))
                             NONE)
                          ()) ())
                          (fn x_g =>
                            (fn () =>
                              (case x_g of NONE => NONE
                                | SOME x_h => SOME (xb, x_h)))))
                   ()) ())
                   (fn x_c =>
                     (fn () => (case x_c of NONE => NONE | SOME a => SOME a)))))
           NONE)
        ()) ())
        (fn a =>
          (case a of NONE => (fn () => NONE)
            | SOME (a1, a2) =>
              (fn f_ => fn () => f_ ((copyi a2) ()) ())
                (fn x =>
                  (fn f_ => fn () => f_
                    (((fn f_ => fn () => f_ ((show_loc_impl a1) ()) ())
                       (fn xa =>
                         (fn f_ => fn () => f_ ((show_dbm_impl x) ()) ())
                           (fn x_a => (fn () => (mk_st_string xa x_a)))))
                    ()) ())
                    (fn x_c =>
                      (fn f_ => fn () => f_
                        ((print_line_impl "Prop failed for: ") ()) ())
                        (fn _ =>
                          (fn f_ => fn () => f_ ((print_line_impl x_c) ()) ())
                            (fn _ => (fn () => (SOME (a1, a2))))))))));

fun show_dbm_impl (A1_, A2_, A3_) n show_clock show_num =
  (fn xi =>
    (fn f_ => fn () => f_
      ((dbm_to_list_impl
         (linordered_ab_monoid_add_DBMEntry
            (linordered_cancel_ab_monoid_add_linordered_ab_group_add A1_, A2_),
           heap_DBMEntry A3_)
         n xi)
      ()) ())
      (fn x =>
        (fn () =>
          (dbm_list_to_string (A1_, A2_, A3_) n show_clock show_num x))));

fun pre_reset_list_impl n =
  (fn ai => fn bi =>
    imp_nfoldli bi (fn _ => (fn () => true))
      (fn x => fn sigma => pre_reset_impl n sigma x) ai);

fun get_entries_impl_int x =
  (fn n => fn xi =>
    (fn f_ => fn () => f_
      ((imp_for_inta zero_nata (suc n)
         (fn xc => fn sigma =>
           (fn f_ => fn () => f_
             ((imp_for_inta zero_nata (suc n)
                (fn xf => fn sigmaa =>
                  (fn f_ => fn () => f_
                    ((mtx_get (heap_DBMEntry heap_int) (suc n) xi (xc, xf)) ())
                    ())
                    (fn xa =>
                      (fn () =>
                        ((if (less_nat zero_nata xc orelse
                               less_nat zero_nata xf) andalso
                               not (equal_DBMEntry equal_int xa INF)
                           then op_list_prepend (xc, xf) op_list_empty
                           else op_list_empty) ::
                          sigmaa))))
                op_list_empty)
             ()) ())
             (fn xa =>
               (fn f_ => fn () => f_
                 ((imp_nfoldli (op_list_rev (op_list_rev xa))
                    (fn _ => (fn () => true))
                    (fn xf => fn sigmaa => (fn () => (xf @ sigmaa)))
                    op_list_empty)
                 ()) ())
                 (fn x_c => (fn () => (x_c :: sigma)))))
         op_list_empty)
      ()) ())
      (fn xa =>
        imp_nfoldli (op_list_rev (op_list_rev xa)) (fn _ => (fn () => true))
          (fn xc => fn sigma => (fn () => (xc @ sigma))) op_list_empty))
    x;

fun dbm_minus_canonical_impl x =
  (fn n => fn ai => fn bi =>
    (fn f_ => fn () => f_ ((get_entries_impl_int n bi) ()) ())
      (fn xa =>
        (fn f_ => fn () => f_
          ((imp_nfoldli xa (fn _ => (fn () => true))
             (fn xb => fn sigma =>
               (fn f_ => fn () => f_
                 ((upd_entries_impl n (fst xb) (snd xb) bi ai) ()) ())
                 (fn xc =>
                   (fn f_ => fn () => f_
                     ((imp_nfoldli xc (fn _ => (fn () => true))
                        (fn xe => fn sigmaa => (fn () => (xe :: sigmaa)))
                        op_list_empty)
                     ()) ())
                     (fn x_c => (fn () => (x_c @ sigma)))))
             op_list_empty)
          ()) ())
          (fn xb =>
            (fn f_ => fn () => f_
              ((imp_nfoldli xb (fn _ => (fn () => true))
                 (fn xba => fn sigma => (fn () => (xba :: sigma)))
                 op_list_empty)
              ()) ())
              (fn xc =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli xc (fn _ => (fn () => true))
                     (fn xba => fn sigma =>
                       (fn f_ => fn () => f_ ((check_diag_impl_inta n n xba) ())
                         ())
                         (fn xd =>
                           (fn () =>
                             (if not xd then op_list_prepend xba sigma
                               else sigma))))
                     op_list_empty)
                  ()) ())
                  (fn xd =>
                    imp_nfoldli xd (fn _ => (fn () => true))
                      (fn xba => fn sigma => (fn () => (xba :: sigma)))
                      op_list_empty)))))
    x;

fun dbm_subset_fed_impl n =
  (fn ai => fn bi =>
    (fn f_ => fn () => f_
      ((imp_nfoldli bi (fn _ => (fn () => true))
         (fn xa => fn sigma =>
           (fn f_ => fn () => f_ ((check_diag_impl_inta n n xa) ()) ())
             (fn x =>
               (fn () => (if not x then op_list_prepend xa sigma else sigma))))
         op_list_empty)
      ()) ())
      (fn x =>
        let
          val xa = op_list_rev x;
        in
          (if op_list_is_empty xa then check_diag_impl_inta n n ai
            else (fn f_ => fn () => f_
                   ((imp_nfoldli xa (fn sigma => (fn () => (not sigma)))
                      (fn xc => fn sigma =>
                        (fn f_ => fn () => f_ ((dbm_subset_impl_inta n ai xc)
                          ()) ())
                          (fn x_d => (fn () => (if x_d then true else sigma))))
                      false)
                   ()) ())
                   (fn x_b =>
                     (if x_b then (fn () => true)
                       else (fn f_ => fn () => f_
                              ((imp_nfoldli xa (fn _ => (fn () => true))
                                 (fn xd => fn sigma =>
                                   dbm_minus_canonical_impl n sigma xd)
                                 (op_list_prepend ai op_list_empty))
                              ()) ())
                              (fn x_c => (fn () => (op_list_is_empty x_c))))))
        end));

fun check_deadlock_fail broadcast bounds automata m num_states num_actions
  show_clock show_state =
  (fn l_list => fn m_list =>
    let
      val p_impl =
        (fn (a, b) =>
          let
            val n_ps = size_list automata;
            val invs =
              Vector.fromList
                (map (fn i =>
                       let
                         val ma =
                           default_map_of equal_nat []
                             (snd (snd (snd (nth automata i))));
                         val mb =
                           Vector.fromList
                             (map ma (upt zero_nata (num_states i)));
                       in
                         mb
                       end)
                  (upt zero_nata n_ps));
            val inv_fun =
              (fn (l, _) =>
                maps (fn i => sub (sub invs i) (nth l i)) (upt zero_nata n_ps));
            val trans_impl =
              let
                val trans_mapa = trans_map automata;
                val trans_i_map =
                  (fn i => fn j =>
                    map_filter
                      (fn aa =>
                        (case aa of (_, (_, (In _, (_, _)))) => NONE
                          | (_, (_, (Out _, (_, _)))) => NONE
                          | (ba, (g, (Sil ab, (ma, l)))) =>
                            SOME (ba, (g, (ab, (ma, l))))))
                      (trans_mapa i j));
                val int_trans_from_loc_impl =
                  (fn p => fn l => fn la => fn s =>
                    let
                      val aa = trans_i_map p l;
                    in
                      map_filter
                        (fn (ba, (g, (ab, (f, (r, lb))))) =>
                          let
                            val sa = mk_updsi s f;
                          in
                            (if bvali (equal_int, linorder_int) s ba andalso
                                  check_boundedi bounds sa
                              then SOME (g,
  (Internal ab, (r, (list_update la p lb, sa))))
                              else NONE)
                          end)
                        aa
                    end);
                val int_trans_from_vec_impl =
                  (fn pairs => fn l => fn s =>
                    maps (fn (p, la) => int_trans_from_loc_impl p la l s)
                      pairs);
                val int_trans_from_all_impl =
                  (fn l => fn s =>
                    maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
                      (upt zero_nata n_ps));
                val trans_out_map =
                  (fn i => fn j =>
                    map_filter
                      (fn aa =>
                        (case aa of (_, (_, (In _, (_, _)))) => NONE
                          | (ba, (g, (Out ab, (ma, l)))) =>
                            SOME (ba, (g, (ab, (ma, l))))
                          | (_, (_, (Sil _, (_, _)))) => NONE))
                      (trans_mapa i j));
                val trans_in_map =
                  (fn i => fn j =>
                    map_filter
                      (fn aa =>
                        (case aa
                          of (ba, (g, (In ab, (ma, l)))) =>
                            SOME (ba, (g, (ab, (ma, l))))
                          | (_, (_, (Out _, (_, _)))) => NONE
                          | (_, (_, (Sil _, (_, _)))) => NONE))
                      (trans_mapa i j));
                val trans_out_broad_grouped =
                  (fn i => fn j =>
                    actions_by_statea num_actions
                      (map_filter
                        (fn aa =>
                          (case aa of (_, (_, (In _, (_, _)))) => NONE
                            | (ba, (g, (Out ab, (ma, l)))) =>
                              (if membera equal_nat broadcast ab
                                then SOME (ba, (g, (ab, (ma, l)))) else NONE)
                            | (_, (_, (Sil _, (_, _)))) => NONE))
                        (trans_mapa i j)));
                val trans_in_broad_grouped =
                  (fn i => fn j =>
                    actions_by_statea num_actions
                      (map_filter
                        (fn aa =>
                          (case aa
                            of (ba, (g, (In ab, (ma, l)))) =>
                              (if membera equal_nat broadcast ab
                                then SOME (ba, (g, (ab, (ma, l)))) else NONE)
                            | (_, (_, (Out _, (_, _)))) => NONE
                            | (_, (_, (Sil _, (_, _)))) => NONE))
                        (trans_mapa i j)));
                val broad_trans_impl =
                  (fn (l, s) =>
                    let
                      val pairs = get_committed broadcast bounds automata l;
                      val ina =
                        map (fn p => trans_in_broad_grouped p (nth l p))
                          (upt zero_nata n_ps);
                      val out =
                        map (fn p => trans_out_broad_grouped p (nth l p))
                          (upt zero_nata n_ps);
                      val inb =
                        map (map (filter
                                   (fn (ba, _) =>
                                     bvali (equal_int, linorder_int) s ba)))
                          ina;
                      val outa =
                        map (map (filter
                                   (fn (ba, _) =>
                                     bvali (equal_int, linorder_int) s ba)))
                          out;
                    in
                      (if null pairs
                        then maps (fn aa =>
                                    maps (fn p =>
   let
     val outs = nth (nth outa p) aa;
   in
     (if null outs then []
       else let
              val combs = make_combs broadcast bounds automata p aa inb;
              val outsa = map (fn ab => (p, ab)) outs;
              val combsa =
                (if null combs then map (fn x => [x]) outsa
                  else maps (fn x => map (fn ab => x :: ab) combs) outsa);
              val init = ([], (Broad aa, ([], (l, s))));
            in
              compute_upds_impl bounds init combsa
            end)
   end)
                                      (upt zero_nata n_ps))
                               (upt zero_nata num_actions)
                        else maps (fn aa =>
                                    let
                                      val ins_committed =
map_filter
  (fn (p, _) => (if not (null (nth (nth inb p) aa)) then SOME p else NONE))
  pairs;
                                      val always_committed =
less_nat one_nata (size_list ins_committed);
                                    in
                                      maps
(fn p =>
  let
    val outs = nth (nth outa p) aa;
  in
    (if null outs then []
      else (if not always_committed andalso
                 ((equal_lista equal_nat ins_committed [p] orelse
                    null ins_committed) andalso
                   not (list_ex (fn (q, _) => equal_nata q p) pairs))
             then []
             else let
                    val combs = make_combs broadcast bounds automata p aa inb;
                    val outsa = map (fn ab => (p, ab)) outs;
                    val combsa =
                      (if null combs then map (fn x => [x]) outsa
                        else maps (fn x => map (fn ab => x :: ab) combs) outsa);
                    val init = ([], (Broad aa, ([], (l, s))));
                  in
                    compute_upds_impl bounds init combsa
                  end))
  end)
(upt zero_nata n_ps)
                                    end)
                               (upt zero_nata num_actions))
                    end);
                val bin_trans_impl =
                  (fn (l, s) =>
                    let
                      val pairs = get_committed broadcast bounds automata l;
                      val ina =
                        all_actions_by_state broadcast bounds automata
                          num_actions trans_in_map l;
                      val out =
                        all_actions_by_state broadcast bounds automata
                          num_actions trans_out_map l;
                    in
                      (if null pairs
                        then maps (fn aa =>
                                    pairs_by_action_impl bounds l s (nth out aa)
                                      (nth ina aa))
                               (bin_actions broadcast num_actions)
                        else let
                               val in2 =
                                 all_actions_from_vec num_actions trans_in_map
                                   pairs;
                               val out2 =
                                 all_actions_from_vec num_actions trans_out_map
                                   pairs;
                             in
                               maps (fn aa =>
                                      pairs_by_action_impl bounds l s
(nth out aa) (nth in2 aa))
                                 (bin_actions broadcast num_actions) @
                                 maps (fn aa =>
pairs_by_action_impl bounds l s (nth out2 aa) (nth ina aa))
                                   (bin_actions broadcast num_actions)
                             end)
                    end);
                val int_trans_impl =
                  (fn (l, s) =>
                    let
                      val pairs = get_committed broadcast bounds automata l;
                    in
                      (if null pairs then int_trans_from_all_impl l s
                        else int_trans_from_vec_impl pairs l s)
                    end);
              in
                (fn st =>
                  int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st)
              end;
          in
            (fn ai => fn bi =>
              (fn f_ => fn () => f_
                ((imp_nfoldli (trans_impl ai) (fn _ => (fn () => true))
                   (fn xb => fn sigma =>
                     (fn f_ => fn () => f_
                       ((v_dbm_impl
                          (linordered_cancel_ab_monoid_add_int, heap_int) m)
                       ()) ())
                       (fn x =>
                         (fn f_ => fn () => f_
                           ((abstr_FW_impl_int m (inv_fun (snd (snd (snd xb))))
                              x)
                           ()) ())
                           (fn xa =>
                             (fn f_ => fn () => f_
                               ((pre_reset_list_impl m xa (fst (snd (snd xb))))
                               ()) ())
                               (fn xc =>
                                 (fn f_ => fn () => f_
                                   ((abstr_FW_impl_int m (fst xb) xc) ()) ())
                                   (fn xd =>
                                     (fn f_ => fn () => f_
                                       ((abstr_FW_impl_int m (inv_fun ai) xd)
                                       ()) ())
                                       (fn xe =>
 (fn f_ => fn () => f_ ((down_impl_int m xe) ()) ())
   (fn x_c => (fn () => (x_c :: sigma)))))))))
                   [])
                ()) ())
                (fn x => dbm_subset_fed_impl m bi (op_list_rev x)))
          end
            a
            b);
      val copy = amtx_copy (heap_DBMEntry heap_int);
      val show_dbm =
        (fn ma =>
          (fn f_ => fn () => f_
            ((show_dbm_impl (linordered_ab_group_add_int, equal_int, heap_int) m
               show_clock (fn x => shows_prec_int zero_nata x []) ma)
            ()) ())
            (fn s => (fn () => (implode s))));
      val show_statea = (fn l => let
                                   val s = show_state l;
                                   val a = implode s;
                                 in
                                   (fn () => a)
                                 end);
    in
      (fn f_ => fn () => f_
        (((fn f_ => fn () => f_
            ((ht_new
               (hashable_prod (hashable_list hashable_nat)
                  (hashable_list hashable_int),
                 heap_prod (heap_list heap_nat) (heap_list heap_int))
               (heap_list (heap_array (typerep_DBMEntry typerep_int))))
            ()) ())
           (imp_nfoldli m_list (fn _ => (fn () => true))
             (fn xc => fn sigma =>
               (fn f_ => fn () => f_
                 ((imp_nfoldli (snd xc) (fn _ => (fn () => true))
                    (fn xg => fn sigmaa =>
                      (fn f_ => fn () => f_ (((fn () => Array.fromList xg)) ())
                        ())
                        (fn x_g => (fn () => (x_g :: sigmaa))))
                    [])
                 ()) ())
                 (fn x_e =>
                   ht_update
                     (equal_prod (equal_list equal_nat) (equal_list equal_int),
                       hashable_prod (hashable_list hashable_nat)
                         (hashable_list hashable_int),
                       heap_prod (heap_list heap_nat) (heap_list heap_int))
                     (heap_list (heap_array (typerep_DBMEntry typerep_int)))
                     (fst xc) x_e sigma))))
        ()) ())
        (fn m_table =>
          (fn f_ => fn () => f_
            ((check_prop_fail_impl
               (equal_prod (equal_list equal_nat) (equal_list equal_int),
                 hashable_prod (hashable_list hashable_nat)
                   (hashable_list hashable_int),
                 heap_prod (heap_list heap_nat) (heap_list heap_int))
               (heap_array (typerep_DBMEntry typerep_int)) p_impl copy show_dbm
               show_statea l_list m_table)
            ()) ())
            (fn a =>
              (case a of NONE => (fn () => ())
                | SOME (l, ma) =>
                  let
                    val _ = writeln "\nThe following state is deadlocked";
                  in
                    (fn f_ => fn () => f_ ((show_statea l) ()) ())
                      (fn s =>
                        let
                          val _ = writeln s;
                        in
                          (fn f_ => fn () => f_
                            ((show_dbm_impl_all
                               (linordered_ab_group_add_int, equal_int,
                                 heap_int)
                               m show_clock
                               (fn x => shows_prec_int zero_nata x []) ma)
                            ()) ())
                            (fn sa => let
val _ = writeln (implode sa);
                                      in
(fn () => ())
                                      end)
                        end)
                  end)))
    end);

fun check_diag_nonpos (A1_, A2_, A3_, A4_) n m =
  imp_for_int zero_nata (plus_nata n one_nata) (fn a => (fn () => a))
    (fn xc => fn _ =>
      (fn f_ => fn () => f_ ((mtx_get (heap_DBMEntry A3_) (suc n) m (xc, xc))
        ()) ())
        (fn x_d =>
          (fn () => (less_eq_DBMEntry (A2_, A4_) x_d (Le (zero A1_))))))
    true;

fun check_nonneg (A1_, A2_, A3_, A4_) n m =
  imp_for_int zero_nata (plus_nata n one_nata) (fn a => (fn () => a))
    (fn xc => fn _ =>
      (fn f_ => fn () => f_
        ((mtx_get (heap_DBMEntry A3_) (suc n) m (zero_nata, xc)) ()) ())
        (fn x_e =>
          (fn () => (less_eq_DBMEntry (A2_, A4_) x_e (Le (zero A1_))))))
    true;

fun check_prop_fail broadcast bounds automata m show_clock show_state =
  let
    val states_ia =
      map (states_i automata) (upt zero_nata (size_list automata));
    val check_states =
      (fn (l, s) =>
        equal_nata (size_list l) (size_list automata) andalso
          let
            val d = minus_nata (size_list automata) one_nata;
          in
            (if less_nat d (size_list automata)
              then all_interval (equal_nat, interval_nat)
                     (fn i =>
                       member (ceq_nat, ccompare_nat) (nth l i)
                         (nth states_ia i))
                     zero_nata d
              else true)
          end andalso
          (equal_nata (size_list s) (n_vs bounds) andalso
            check_boundedi bounds s));
  in
    (fn l_list => fn m_list =>
      let
        val p_impl =
          (fn (a1, a2) =>
            (fn f_ => fn () => f_
              ((imp_for_int zero_nata (plus_nata m one_nata)
                 (fn a => (fn () => a))
                 (fn xc => fn _ =>
                   imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xf => fn _ =>
                       imp_for_int zero_nata (plus_nata m one_nata)
                         (fn a => (fn () => a))
                         (fn xj => fn _ =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (xc, xj))
                             ()) ())
                             (fn x_i =>
                               (fn f_ => fn () => f_
                                 ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                    (xc, xf))
                                 ()) ())
                                 (fn x =>
                                   (fn f_ => fn () => f_
                                     ((mtx_get (heap_DBMEntry heap_int) (suc m)
a2 (xf, xj))
                                     ()) ())
                                     (fn xa =>
                                       (fn () =>
 (dbm_le_int x_i (dbm_add_int x xa)))))))
                         true)
                     true)
                 true)
              ()) ())
              (fn x =>
                (fn f_ => fn () => f_ ((check_diag_impl_int m a2) ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_
                      ((imp_for_int zero_nata (plus_nata m one_nata)
                         (fn a => (fn () => a))
                         (fn xc => fn _ =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (xc, xc))
                             ()) ())
                             (fn x_d =>
                               (fn () => (dbm_le_int x_d (Le zero_inta)))))
                         true)
                      ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_
                          ((imp_for_int zero_nata (plus_nata m one_nata)
                             (fn a => (fn () => a))
                             (fn xc => fn _ =>
                               (fn f_ => fn () => f_
                                 ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                    (zero_nata, xc))
                                 ()) ())
                                 (fn x_e =>
                                   (fn () => (dbm_le_int x_e (Le zero_inta)))))
                             true)
                          ()) ())
                          (fn xc =>
                            (fn () =>
                              (check_states a1 andalso
                                ((x orelse xa) andalso (xb andalso xc)))))))));
        val copy = amtx_copy (heap_DBMEntry heap_int);
        val show_dbm =
          (fn ma =>
            (fn f_ => fn () => f_
              ((show_dbm_impl (linordered_ab_group_add_int, equal_int, heap_int)
                 m show_clock (fn x => shows_prec_int zero_nata x []) ma)
              ()) ())
              (fn s => (fn () => (implode s))));
        val show_statea = (fn l => let
                                     val s = show_state l;
                                     val a = implode s;
                                   in
                                     (fn () => a)
                                   end);
      in
        (fn f_ => fn () => f_
          (((fn f_ => fn () => f_
              ((ht_new
                 (hashable_prod (hashable_list hashable_nat)
                    (hashable_list hashable_int),
                   heap_prod (heap_list heap_nat) (heap_list heap_int))
                 (heap_list (heap_array (typerep_DBMEntry typerep_int))))
              ()) ())
             (imp_nfoldli m_list (fn _ => (fn () => true))
               (fn xc => fn sigma =>
                 (fn f_ => fn () => f_
                   ((imp_nfoldli (snd xc) (fn _ => (fn () => true))
                      (fn xg => fn sigmaa =>
                        (fn f_ => fn () => f_ (((fn () => Array.fromList xg))
                          ()) ())
                          (fn x_g => (fn () => (x_g :: sigmaa))))
                      [])
                   ()) ())
                   (fn x_e =>
                     ht_update
                       (equal_prod (equal_list equal_nat)
                          (equal_list equal_int),
                         hashable_prod (hashable_list hashable_nat)
                           (hashable_list hashable_int),
                         heap_prod (heap_list heap_nat) (heap_list heap_int))
                       (heap_list (heap_array (typerep_DBMEntry typerep_int)))
                       (fst xc) x_e sigma))))
          ()) ())
          (fn m_table =>
            (fn f_ => fn () => f_
              ((check_prop_fail_impl
                 (equal_prod (equal_list equal_nat) (equal_list equal_int),
                   hashable_prod (hashable_list hashable_nat)
                     (hashable_list hashable_int),
                   heap_prod (heap_list heap_nat) (heap_list heap_int))
                 (heap_array (typerep_DBMEntry typerep_int)) p_impl copy
                 show_dbm show_statea l_list m_table)
              ()) ())
              (fn a =>
                (case a of NONE => (fn () => ())
                  | SOME (l, ma) =>
                    let
                      val b = check_states l;
                      val _ =
                        writeln (if b then "State passed" else "State failed");
                    in
                      (fn f_ => fn () => f_ ((check_diag_impl_int m ma) ()) ())
                        (fn ba =>
                          let
                            val _ =
                              writeln (if ba then "DBM passed diag"
else "DBM failed diag");
                          in
                            (fn f_ => fn () => f_
                              ((check_diag_nonpos
                                 (zero_int, equal_int, heap_int, linorder_int) m
                                 ma)
                              ()) ())
                              (fn bb =>
                                let
                                  val _ =
                                    writeln (if bb then "DBM passed diag nonpos"
      else "DBM failed diag nonpos");
                                in
                                  (fn f_ => fn () => f_
                                    ((check_nonneg
                                       (zero_int, equal_int, heap_int,
 linorder_int)
                                       m ma)
                                    ()) ())
                                    (fn bc =>
                                      let
val _ = writeln (if bc then "DBM passed nonneg" else "DBM failed nonneg");
                                      in
(fn f_ => fn () => f_
  ((show_dbm_impl_all (linordered_ab_group_add_int, equal_int, heap_int) m
     show_clock (fn x => shows_prec_int zero_nata x []) ma)
  ()) ())
  (fn s => let
             val _ = writeln ("DBM: " ^ implode s);
           in
             (fn () => ())
           end)
                                      end)
                                end)
                          end)
                    end)))
      end)
  end;

fun certificate_checker_dbg num_split dc show_clock show_state m_list broadcast
  bounds automata m num_states num_actions k l_0 s_0 formula =
  let
    val _ = Timing.start_timer ();
    val check1 =
      simple_Network_Impl_nat_ceiling_start_state broadcast bounds automata m
        num_states num_actions k l_0 s_0 formula;
    val _ = Timing.save_time "Time to check ceiling";
    val l_list = map fst m_list;
    val n_ps = size_list automata;
    val n_vsa = n_vs bounds;
    val states_ia = map (states_i automata) (upt zero_nata n_ps);
    val _ = Timing.start_timer ();
    val check2 =
      list_all
        (fn (l, s) =>
          equal_nata (size_list l) n_ps andalso
            (let
               val d = minus_nata n_ps one_nata;
             in
               (if less_nat d n_ps
                 then all_interval (equal_nat, interval_nat)
                        (fn i =>
                          member (ceq_nat, ccompare_nat) (nth l i)
                            (nth states_ia i))
                        zero_nata d
                 else true)
             end andalso
              (equal_nata (size_list s) n_vsa andalso check_boundedi bounds s)))
        l_list;
    val _ = Timing.save_time "Time to check states";
    val check3 =
      (case formula of EX _ => true | EG _ => false | AX _ => false
        | AG _ => false | Leadsto (_, _) => false);
  in
    (if check1 andalso (check2 andalso check3)
      then (fn f_ => fn () => f_
             ((check_prop_fail broadcast bounds automata m show_clock show_state
                l_list m_list)
             ()) ())
             (fn _ =>
               (fn f_ => fn () => f_
                 ((check_invariant_fail broadcast bounds automata m num_states
                    num_actions show_clock show_state l_list m_list)
                 ()) ())
                 (fn _ =>
                   (fn f_ => fn () => f_
                     ((if dc
                        then check_deadlock_fail broadcast bounds automata m
                               num_states num_actions show_clock show_state
                               l_list m_list
                        else (fn () => ()))
                     ()) ())
                     (fn _ =>
                       (fn f_ => fn () => f_
                         ((unreachability_checker broadcast bounds automata m
                            num_states num_actions l_0 s_0 formula l_list m_list
                            num_split)
                         ()) ())
                         (fn r => (fn () => (SOME r))))))
      else (fn () => NONE))
  end;

fun rename_check_dbg A_ B_ C_ num_split dc broadcast bounds automata k l_0 s_0
  formula m num_states num_actions renum_acts renum_vars renum_clocks
  renum_states inv_renum_states inv_renum_vars inv_renum_clocks state_space =
  (case do_rename_mc show_int A_ B_ C_
          (fn show_clock => fn show_state =>
            certificate_checker_dbg num_split dc show_clock show_state
              state_space)
          dc broadcast bounds automata k "_urge" l_0 s_0 formula m num_states
          num_actions renum_acts renum_vars renum_clocks renum_states
          inv_renum_states inv_renum_vars inv_renum_clocks
    of NONE => (fn () => Renaming_Failed)
    | SOME r =>
      (fn f_ => fn () => f_ (r ()) ())
        (fn a =>
          (case a of NONE => (fn () => Preconds_Unsat)
            | SOME true => (fn () => Sat) | SOME false => (fn () => Unsat))));

fun certificate_checker3 _ _ _ _ _ _ _ _ _ _ _ _ _ = raise Fail
  "Simple_Network_Language_Certificate_Checking.certificate_checker3";

fun rename_check3 num_split dc broadcast bounds automata k l_0 s_0 formula m
  num_states num_actions renum_acts renum_vars renum_clocks renum_states
  state_space =
  (case do_rename_mc show_int (show_list show_char) (show_list show_char)
          (show_list show_char)
          (fn _ => fn _ => certificate_checker3 num_split dc state_space) dc
          broadcast bounds automata k "_urge" l_0 s_0 formula m num_states
          num_actions renum_acts renum_vars renum_clocks renum_states
          (fn _ => fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
          (fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
          (fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
    of NONE => Renaming_Failed | SOME true => Sat | SOME false => Unsat);

fun check_final_impl (A1_, A2_, A3_) B_ fi copyi =
  (fn ai => fn bi =>
    imp_nfoldli ai (fn a => (fn () => a))
      (fn xb => fn _ =>
        (fn f_ => fn () => f_
          ((hms_lookup (ht_lookup (A1_, A2_, A3_) (heap_list B_))
             (heap_map copyi) xb bi)
          ()) ())
          (fn a =>
            (case a of NONE => (fn () => true)
              | SOME x_e =>
                imp_nfoldli x_e (fn aa => (fn () => aa))
                  (fn xh => fn _ =>
                    (fn f_ => fn () => f_ ((fi (xb, xh)) ()) ())
                      (fn x_i => (fn () => (not x_i))))
                  true)))
      true);

fun certify_unreachable_impl2 (A1_, A2_, A3_) B_ fi pi copyi lei succsi l_0i
  s_0i splitteri l_list m_table =
  let
    val _ = Timing.start_timer ();
    val b1 =
      (fn f => f ()) ((fn f_ => fn () => f_ (m_table ()) ())
                       (fn m =>
                         (fn f_ => fn () => f_ (l_0i ()) ())
                           (fn x =>
                             (fn f_ => fn () => f_
                               ((imp_nfoldli l_list
                                  (fn sigma => (fn () => (not sigma)))
                                  (fn xb => fn _ => (fn () => (eq A1_ xb x)))
                                  false)
                               ()) ())
                               (fn xa =>
                                 (fn f_ => fn () => f_ (l_0i ()) ())
                                   (fn xaa =>
                                     (fn f_ => fn () => f_ (s_0i ()) ())
                                       (fn xb =>
 (fn f_ => fn () => f_ ((pi (xaa, xb)) ()) ())
   (fn x_a =>
     (fn f_ => fn () => f_ (l_0i ()) ())
       (fn xab =>
         (fn f_ => fn () => f_
           ((hms_lookup (ht_lookup (A1_, A2_, A3_) (heap_list B_))
              (heap_map copyi) xab m)
           ()) ())
           (fn a =>
             (case a of NONE => (fn () => false)
               | SOME x_d =>
                 (fn f_ => fn () => f_
                   ((imp_nfoldli x_d (fn sigma => (fn () => (not sigma)))
                      (fn xg => fn _ =>
                        (fn f_ => fn () => f_ (s_0i ()) ())
                          (fn x_h => lei x_h xg))
                      false)
                   ()) ())
                   (fn x_f =>
                     (fn f_ => fn () => f_
                       ((imp_nfoldli l_list (fn aa => (fn () => aa))
                          (fn xba => fn _ =>
                            (fn f_ => fn () => f_
                              ((hms_lookup
                                 (ht_lookup (A1_, A2_, A3_) (heap_list B_))
                                 (heap_map copyi) xba m)
                              ()) ())
                              (fn aa =>
                                (case aa of NONE => (fn () => true)
                                  | SOME x_e =>
                                    imp_nfoldli x_e (fn ab => (fn () => ab))
                                      (fn xh => fn _ => pi (xba, xh)) true)))
                          true)
                       ()) ())
                       (fn x_g =>
                         (fn f_ => fn () => f_
                           ((print_check_impl "Start state is in state list" xa)
                           ()) ())
                           (fn _ =>
                             (fn f_ => fn () => f_
                               ((print_check_impl
                                  "Start state fulfills property" x_a)
                               ()) ())
                               (fn _ =>
                                 (fn f_ => fn () => f_
                                   ((print_check_impl "Start state is subsumed"
                                      x_f)
                                   ()) ())
                                   (fn _ =>
                                     (fn f_ => fn () => f_
                                       ((print_check_impl "Check property" x_g)
                                       ()) ())
                                       (fn _ =>
 (fn () => (xa andalso (x_a andalso (x_f andalso x_g))))))))))))))))))));
    val _ = Timing.save_time "Time for checking basic preconditions";
    val _ = Timing.start_timer ();
    val xs =
      run_map_heap
        (fn li =>
          (fn f_ => fn () => f_ (m_table ()) ())
            (fn m =>
              imp_nfoldli li (fn a => (fn () => a))
                (fn xa => fn _ =>
                  (fn f_ => fn () => f_
                    ((hms_lookup (ht_lookup (A1_, A2_, A3_) (heap_list B_))
                       (heap_map copyi) xa m)
                    ()) ())
                    (fn a =>
                      (case a of NONE => (fn () => true)
                        | SOME x_c =>
                          (fn f_ => fn () => f_ ((succsi xa x_c) ()) ())
                            (fn x_d =>
                              imp_nfoldli x_d (fn aa => (fn () => aa))
                                (fn xg => fn _ =>
                                  let
                                    val (a1, a2) = xg;
                                  in
                                    (if op_list_is_empty a2 then (fn () => true)
                                      else (fn f_ => fn () => f_
     ((hms_lookup (ht_lookup (A1_, A2_, A3_) (heap_list B_)) (heap_map copyi) a1
        m)
     ()) ())
     (fn aa =>
       (case aa of NONE => (fn () => false)
         | SOME x_k =>
           imp_nfoldli a2 (fn ab => (fn () => ab))
             (fn xn => fn _ =>
               imp_nfoldli x_k (fn sigma => (fn () => (not sigma)))
                 (fn xp => fn _ => lei xn xp) false)
             true)))
                                  end)
                                true))))
                true))
        (splitteri l_list);
    val b2 = list_all id xs;
    val _ = Timing.save_time "Time for state space invariant check";
    val _ = print_check "State set invariant check" b2;
    val _ = Timing.start_timer ();
    val b3 =
      (fn f => f ()) ((fn f_ => fn () => f_ (m_table ()) ())
                       (check_final_impl (A1_, A2_, A3_) B_ fi copyi l_list));
    val _ = Timing.save_time "Time to check final state predicate";
    val _ = print_check "All check: " (b1 andalso b2);
    val _ = print_check "Target property check: " b3;
  in
    b1 andalso (b2 andalso b3)
  end;

fun unreachability_checker2 broadcast bounds automata m num_states num_actions
  l_0 s_0 formula l_list m_list num_split =
  let
    val states_ia =
      map (states_i automata) (upt zero_nata (size_list automata));
    val check_states =
      (fn (l, s) =>
        equal_nata (size_list l) (size_list automata) andalso
          let
            val d = minus_nata (size_list automata) one_nata;
          in
            (if less_nat d (size_list automata)
              then all_interval (equal_nat, interval_nat)
                     (fn i =>
                       member (ceq_nat, ccompare_nat) (nth l i)
                         (nth states_ia i))
                     zero_nata d
              else true)
          end andalso
          (equal_nata (size_list s) (n_vs bounds) andalso
            check_boundedi bounds s));
    val fi = (fn xi => (fn () => let
                                   val ((a, b), _) = xi;
                                 in
                                   hd_of_formulai equal_nat formula a b
                                 end));
    val pi =
      (fn (a1, a2) =>
        (fn f_ => fn () => f_
          ((imp_for_int zero_nata (plus_nata m one_nata) (fn a => (fn () => a))
             (fn xc => fn _ =>
               imp_for_int zero_nata (plus_nata m one_nata)
                 (fn a => (fn () => a))
                 (fn xf => fn _ =>
                   imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xj => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xj))
                         ()) ())
                         (fn x_i =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (xc, xf))
                             ()) ())
                             (fn x =>
                               (fn f_ => fn () => f_
                                 ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                    (xf, xj))
                                 ()) ())
                                 (fn xa =>
                                   (fn () =>
                                     (dbm_le_int x_i (dbm_add_int x xa)))))))
                     true)
                 true)
             true)
          ()) ())
          (fn x =>
            (fn f_ => fn () => f_ ((check_diag_impl_int m a2) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_
                  ((imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xc => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xc))
                         ()) ())
                         (fn x_d => (fn () => (dbm_le_int x_d (Le zero_inta)))))
                     true)
                  ()) ())
                  (fn xb =>
                    (fn f_ => fn () => f_
                      ((imp_for_int zero_nata (plus_nata m one_nata)
                         (fn a => (fn () => a))
                         (fn xc => fn _ =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (zero_nata, xc))
                             ()) ())
                             (fn x_e =>
                               (fn () => (dbm_le_int x_e (Le zero_inta)))))
                         true)
                      ()) ())
                      (fn xc =>
                        (fn () =>
                          (check_states a1 andalso
                            ((x orelse xa) andalso (xb andalso xc)))))))));
    val copyi = amtx_copy (heap_DBMEntry heap_int);
    val lei = dbm_subset_impl_int m;
    val l_0i =
      (fn () =>
        (l_0, map (the o map_of equal_nat s_0) (upt zero_nata (n_vs bounds))));
    val s_0i =
      amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m) (Le zero_inta);
    val succsi =
      let
        val n_ps = size_list automata;
        val invs =
          Vector.fromList
            (map (fn i =>
                   let
                     val ma =
                       default_map_of equal_nat []
                         (snd (snd (snd (nth automata i))));
                     val mb =
                       Vector.fromList (map ma (upt zero_nata (num_states i)));
                   in
                     mb
                   end)
              (upt zero_nata n_ps));
        val inv_fun =
          (fn (l, _) =>
            maps (fn i => sub (sub invs i) (nth l i)) (upt zero_nata n_ps));
        val trans_mapa = trans_map automata;
        val trans_i_map =
          (fn i => fn j =>
            map_filter
              (fn a =>
                (case a of (_, (_, (In _, (_, _)))) => NONE
                  | (_, (_, (Out _, (_, _)))) => NONE
                  | (b, (g, (Sil aa, (ma, l)))) =>
                    SOME (b, (g, (aa, (ma, l))))))
              (trans_mapa i j));
        val int_trans_from_loc_impl =
          (fn p => fn l => fn la => fn s =>
            let
              val a = trans_i_map p l;
            in
              map_filter
                (fn (b, (g, (aa, (f, (r, lb))))) =>
                  let
                    val sa = mk_updsi s f;
                  in
                    (if bvali (equal_int, linorder_int) s b andalso
                          check_boundedi bounds sa
                      then SOME (g, (Internal aa,
                                      (r, (list_update la p lb, sa))))
                      else NONE)
                  end)
                a
            end);
        val int_trans_from_vec_impl =
          (fn pairs => fn l => fn s =>
            maps (fn (p, la) => int_trans_from_loc_impl p la l s) pairs);
        val int_trans_from_all_impl =
          (fn l => fn s =>
            maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
              (upt zero_nata n_ps));
        val trans_out_map =
          (fn i => fn j =>
            map_filter
              (fn a =>
                (case a of (_, (_, (In _, (_, _)))) => NONE
                  | (b, (g, (Out aa, (ma, l)))) => SOME (b, (g, (aa, (ma, l))))
                  | (_, (_, (Sil _, (_, _)))) => NONE))
              (trans_mapa i j));
        val trans_in_map =
          (fn i => fn j =>
            map_filter
              (fn a =>
                (case a
                  of (b, (g, (In aa, (ma, l)))) => SOME (b, (g, (aa, (ma, l))))
                  | (_, (_, (Out _, (_, _)))) => NONE
                  | (_, (_, (Sil _, (_, _)))) => NONE))
              (trans_mapa i j));
        val trans_out_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn a =>
                  (case a of (_, (_, (In _, (_, _)))) => NONE
                    | (b, (g, (Out aa, (ma, l)))) =>
                      (if membera equal_nat broadcast aa
                        then SOME (b, (g, (aa, (ma, l)))) else NONE)
                    | (_, (_, (Sil _, (_, _)))) => NONE))
                (trans_mapa i j)));
        val trans_in_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn a =>
                  (case a
                    of (b, (g, (In aa, (ma, l)))) =>
                      (if membera equal_nat broadcast aa
                        then SOME (b, (g, (aa, (ma, l)))) else NONE)
                    | (_, (_, (Out _, (_, _)))) => NONE
                    | (_, (_, (Sil _, (_, _)))) => NONE))
                (trans_mapa i j)));
        val broad_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_committed broadcast bounds automata l;
              val ina =
                map (fn p => trans_in_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val out =
                map (fn p => trans_out_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val inb =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  ina;
              val outa =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  out;
            in
              (if null pairs
                then maps (fn a =>
                            maps (fn p =>
                                   let
                                     val outs = nth (nth outa p) a;
                                   in
                                     (if null outs then []
                                       else let
      val combs = make_combs broadcast bounds automata p a inb;
      val outsa = map (fn aa => (p, aa)) outs;
      val combsa =
        (if null combs then map (fn x => [x]) outsa
          else maps (fn x => map (fn aa => x :: aa) combs) outsa);
      val init = ([], (Broad a, ([], (l, s))));
    in
      compute_upds_impl bounds init combsa
    end)
                                   end)
                              (upt zero_nata n_ps))
                       (upt zero_nata num_actions)
                else maps (fn a =>
                            let
                              val ins_committed =
                                map_filter
                                  (fn (p, _) =>
                                    (if not (null (nth (nth inb p) a))
                                      then SOME p else NONE))
                                  pairs;
                              val always_committed =
                                less_nat one_nata (size_list ins_committed);
                            in
                              maps (fn p =>
                                     let
                                       val outs = nth (nth outa p) a;
                                     in
                                       (if null outs then []
 else (if not always_committed andalso
            ((equal_lista equal_nat ins_committed [p] orelse
               null ins_committed) andalso
              not (list_ex (fn (q, _) => equal_nata q p) pairs))
        then []
        else let
               val combs = make_combs broadcast bounds automata p a inb;
               val outsa = map (fn aa => (p, aa)) outs;
               val combsa =
                 (if null combs then map (fn x => [x]) outsa
                   else maps (fn x => map (fn aa => x :: aa) combs) outsa);
               val init = ([], (Broad a, ([], (l, s))));
             in
               compute_upds_impl bounds init combsa
             end))
                                     end)
                                (upt zero_nata n_ps)
                            end)
                       (upt zero_nata num_actions))
            end);
        val bin_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_committed broadcast bounds automata l;
              val ina =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_in_map l;
              val out =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_out_map l;
            in
              (if null pairs
                then maps (fn a =>
                            pairs_by_action_impl bounds l s (nth out a)
                              (nth ina a))
                       (bin_actions broadcast num_actions)
                else let
                       val in2 =
                         all_actions_from_vec num_actions trans_in_map pairs;
                       val out2 =
                         all_actions_from_vec num_actions trans_out_map pairs;
                     in
                       maps (fn a =>
                              pairs_by_action_impl bounds l s (nth out a)
                                (nth in2 a))
                         (bin_actions broadcast num_actions) @
                         maps (fn a =>
                                pairs_by_action_impl bounds l s (nth out2 a)
                                  (nth ina a))
                           (bin_actions broadcast num_actions)
                     end)
            end);
        val int_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_committed broadcast bounds automata l;
            in
              (if null pairs then int_trans_from_all_impl l s
                else int_trans_from_vec_impl pairs l s)
            end);
        val trans_impl =
          (fn st =>
            int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st);
        val e_op_impl =
          (fn ai => fn bic => fn bib => fn bia => fn bi =>
            (fn f_ => fn () => f_ ((up_canonical_upd_impl_int m bi m) ()) ())
              (fn x =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli (inv_fun ai) (fn _ => (fn () => true))
                     (fn aia => fn bid =>
                       (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid)
                         ()) ())
                         (fn xa =>
                           repair_pair_impl_int m xa zero_nata
                             (constraint_clk aia)))
                     x)
                  ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((check_diag_impl_int m xa) ()) ())
                      (fn xaa =>
                        (fn f_ => fn () => f_
                          ((if xaa
                             then mtx_set (heap_DBMEntry heap_int) (suc m) xa
                                    (zero_nata, zero_nata) (Lt zero_inta)
                             else imp_nfoldli bib (fn _ => (fn () => true))
                                    (fn aia => fn bid =>
                                      (fn f_ => fn () => f_
((abstra_upd_impl_int m aia bid) ()) ())
(fn xb => repair_pair_impl_int m xb zero_nata (constraint_clk aia)))
                                    xa)
                          ()) ())
                          (fn x_a =>
                            (fn f_ => fn () => f_ ((check_diag_impl_int m x_a)
                              ()) ())
                              (fn x_b =>
                                (if x_b
                                  then mtx_set (heap_DBMEntry heap_int) (suc m)
 x_a (zero_nata, zero_nata) (Lt zero_inta)
                                  else (fn f_ => fn () => f_
 ((imp_nfoldli bic (fn _ => (fn () => true))
    (fn xc => fn sigma => reset_canonical_upd_impl_int m sigma m xc zero_inta)
    x_a)
 ()) ())
 (imp_nfoldli (inv_fun bia) (fn _ => (fn () => true))
   (fn aia => fn bid =>
     (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
       (fn xb =>
         repair_pair_impl_int m xb zero_nata (constraint_clk aia)))))))))));
      in
        (fn ai => fn bi =>
          (if null bi then (fn () => [])
            else imp_nfoldli (trans_impl ai) (fn _ => (fn () => true))
                   (fn xc => fn sigma =>
                     let
                       val (a1, (_, (a1b, a2b))) = xc;
                     in
                       (fn f_ => fn () => f_
                         ((heap_map (amtx_copy (heap_DBMEntry heap_int)) bi) ())
                         ())
                         (fn x =>
                           (fn f_ => fn () => f_
                             ((imp_nfoldli x (fn _ => (fn () => true))
                                (fn xb => fn sigmaa =>
                                  (fn f_ => fn () => f_
                                    ((pR_CONST e_op_impl ai a1b a1 a2b xb) ())
                                    ())
                                    (fn x_c =>
                                      (fn f_ => fn () => f_
((check_diag_impl_int m x_c) ()) ())
(fn x_e => (fn () => (if x_e then sigmaa else op_list_prepend x_c sigmaa)))))
                                [])
                             ()) ())
                             (fn x_d =>
                               (fn () => (op_list_prepend (a2b, x_d) sigma))))
                     end)
                   []))
      end;
    val a =
      (fn f_ => fn () => f_
        ((ht_new
           (hashable_prod (hashable_list hashable_nat)
              (hashable_list hashable_int),
             heap_prod (heap_list heap_nat) (heap_list heap_int))
           (heap_list (heap_array (typerep_DBMEntry typerep_int))))
        ()) ())
        (imp_nfoldli m_list (fn _ => (fn () => true))
          (fn xc => fn sigma =>
            (fn f_ => fn () => f_
              ((imp_nfoldli (snd xc) (fn _ => (fn () => true))
                 (fn xg => fn sigmaa =>
                   (fn f_ => fn () => f_ (((fn () => Array.fromList xg)) ()) ())
                     (fn x_g => (fn () => (x_g :: sigmaa))))
                 [])
              ()) ())
              (fn x_e =>
                ht_update
                  (equal_prod (equal_list equal_nat) (equal_list equal_int),
                    hashable_prod (hashable_list hashable_nat)
                      (hashable_list hashable_int),
                    heap_prod (heap_list heap_nat) (heap_list heap_int))
                  (heap_list (heap_array (typerep_DBMEntry typerep_int)))
                  (fst xc) x_e sigma)));
  in
    certify_unreachable_impl2
      (equal_prod (equal_list equal_nat) (equal_list equal_int),
        hashable_prod (hashable_list hashable_nat) (hashable_list hashable_int),
        heap_prod (heap_list heap_nat) (heap_list heap_int))
      (heap_array (typerep_DBMEntry typerep_int)) fi pi copyi lei succsi l_0i
      s_0i (split_k num_split) l_list a
  end;

fun certificate_checker_pre l_list m_list broadcast bounds automata m num_states
  num_actions k l_0 s_0 formula =
  let
    val _ = Timing.start_timer ();
    val check1 =
      simple_Network_Impl_nat_ceiling_start_state broadcast bounds automata m
        num_states num_actions k l_0 s_0 formula;
    val _ = Timing.save_time "Time to check ceiling";
    val n_ps = size_list automata;
    val n_vsa = n_vs bounds;
    val states_ia = map (states_i automata) (upt zero_nata n_ps);
    val _ = Timing.start_timer ();
    val check2 =
      list_all
        (fn (l, s) =>
          equal_nata (size_list l) n_ps andalso
            (let
               val d = minus_nata n_ps one_nata;
             in
               (if less_nat d n_ps
                 then all_interval (equal_nat, interval_nat)
                        (fn i =>
                          member (ceq_nat, ccompare_nat) (nth l i)
                            (nth states_ia i))
                        zero_nata d
                 else true)
             end andalso
              (equal_nata (size_list s) n_vsa andalso check_boundedi bounds s)))
        l_list;
    val _ = Timing.save_time "Time to check states";
    val _ = Timing.start_timer ();
    val n_sq = times_nata (suc m) (suc m);
    val check3 =
      list_all
        (fn (_, a) => list_all (fn ma => equal_nata (size_list ma) n_sq) a)
        m_list;
    val _ = Timing.save_time "Time to check DBMs";
    val check4 =
      (case formula of EX _ => true | EG _ => false | AX _ => false
        | AG _ => false | Leadsto (_, _) => false);
  in
    check1 andalso (check2 andalso (check3 andalso check4))
  end;

fun no_deadlock_certifier2 broadcast bounds automata m num_states num_actions
  l_0 s_0 l_list m_list num_split =
  let
    val states_ia =
      map (states_i automata) (upt zero_nata (size_list automata));
    val check_states =
      (fn (l, s) =>
        equal_nata (size_list l) (size_list automata) andalso
          let
            val d = minus_nata (size_list automata) one_nata;
          in
            (if less_nat d (size_list automata)
              then all_interval (equal_nat, interval_nat)
                     (fn i =>
                       member (ceq_nat, ccompare_nat) (nth l i)
                         (nth states_ia i))
                     zero_nata d
              else true)
          end andalso
          (equal_nata (size_list s) (n_vs bounds) andalso
            check_boundedi bounds s));
    val fi =
      (fn (l, ma) =>
        (fn f_ => fn () => f_
          ((let
              val n_ps = size_list automata;
              val invs =
                Vector.fromList
                  (map (fn i =>
                         let
                           val mb =
                             default_map_of equal_nat []
                               (snd (snd (snd (nth automata i))));
                           val mc =
                             Vector.fromList
                               (map mb (upt zero_nata (num_states i)));
                         in
                           mc
                         end)
                    (upt zero_nata n_ps));
              val inv_fun =
                (fn (la, _) =>
                  maps (fn i => sub (sub invs i) (nth la i))
                    (upt zero_nata n_ps));
              val trans_impl =
                let
                  val trans_mapa = trans_map automata;
                  val trans_i_map =
                    (fn i => fn j =>
                      map_filter
                        (fn a =>
                          (case a of (_, (_, (In _, (_, _)))) => NONE
                            | (_, (_, (Out _, (_, _)))) => NONE
                            | (b, (g, (Sil aa, (mb, la)))) =>
                              SOME (b, (g, (aa, (mb, la))))))
                        (trans_mapa i j));
                  val int_trans_from_loc_impl =
                    (fn p => fn la => fn laa => fn s =>
                      let
                        val a = trans_i_map p la;
                      in
                        map_filter
                          (fn (b, (g, (aa, (f, (r, lb))))) =>
                            let
                              val sa = mk_updsi s f;
                            in
                              (if bvali (equal_int, linorder_int) s b andalso
                                    check_boundedi bounds sa
                                then SOME (g,
    (Internal aa, (r, (list_update laa p lb, sa))))
                                else NONE)
                            end)
                          a
                      end);
                  val int_trans_from_vec_impl =
                    (fn pairs => fn la => fn s =>
                      maps (fn (p, laa) => int_trans_from_loc_impl p laa la s)
                        pairs);
                  val int_trans_from_all_impl =
                    (fn la => fn s =>
                      maps (fn p => int_trans_from_loc_impl p (nth la p) la s)
                        (upt zero_nata n_ps));
                  val trans_out_map =
                    (fn i => fn j =>
                      map_filter
                        (fn a =>
                          (case a of (_, (_, (In _, (_, _)))) => NONE
                            | (b, (g, (Out aa, (mb, la)))) =>
                              SOME (b, (g, (aa, (mb, la))))
                            | (_, (_, (Sil _, (_, _)))) => NONE))
                        (trans_mapa i j));
                  val trans_in_map =
                    (fn i => fn j =>
                      map_filter
                        (fn a =>
                          (case a
                            of (b, (g, (In aa, (mb, la)))) =>
                              SOME (b, (g, (aa, (mb, la))))
                            | (_, (_, (Out _, (_, _)))) => NONE
                            | (_, (_, (Sil _, (_, _)))) => NONE))
                        (trans_mapa i j));
                  val trans_out_broad_grouped =
                    (fn i => fn j =>
                      actions_by_statea num_actions
                        (map_filter
                          (fn a =>
                            (case a of (_, (_, (In _, (_, _)))) => NONE
                              | (b, (g, (Out aa, (mb, la)))) =>
                                (if membera equal_nat broadcast aa
                                  then SOME (b, (g, (aa, (mb, la)))) else NONE)
                              | (_, (_, (Sil _, (_, _)))) => NONE))
                          (trans_mapa i j)));
                  val trans_in_broad_grouped =
                    (fn i => fn j =>
                      actions_by_statea num_actions
                        (map_filter
                          (fn a =>
                            (case a
                              of (b, (g, (In aa, (mb, la)))) =>
                                (if membera equal_nat broadcast aa
                                  then SOME (b, (g, (aa, (mb, la)))) else NONE)
                              | (_, (_, (Out _, (_, _)))) => NONE
                              | (_, (_, (Sil _, (_, _)))) => NONE))
                          (trans_mapa i j)));
                  val broad_trans_impl =
                    (fn (la, s) =>
                      let
                        val pairs = get_committed broadcast bounds automata la;
                        val ina =
                          map (fn p => trans_in_broad_grouped p (nth la p))
                            (upt zero_nata n_ps);
                        val out =
                          map (fn p => trans_out_broad_grouped p (nth la p))
                            (upt zero_nata n_ps);
                        val inb =
                          map (map (filter
                                     (fn (b, _) =>
                                       bvali (equal_int, linorder_int) s b)))
                            ina;
                        val outa =
                          map (map (filter
                                     (fn (b, _) =>
                                       bvali (equal_int, linorder_int) s b)))
                            out;
                      in
                        (if null pairs
                          then maps (fn a =>
                                      maps
(fn p =>
  let
    val outs = nth (nth outa p) a;
  in
    (if null outs then []
      else let
             val combs = make_combs broadcast bounds automata p a inb;
             val outsa = map (fn aa => (p, aa)) outs;
             val combsa =
               (if null combs then map (fn x => [x]) outsa
                 else maps (fn x => map (fn aa => x :: aa) combs) outsa);
             val init = ([], (Broad a, ([], (la, s))));
           in
             compute_upds_impl bounds init combsa
           end)
  end)
(upt zero_nata n_ps))
                                 (upt zero_nata num_actions)
                          else maps (fn a =>
                                      let
val ins_committed =
  map_filter
    (fn (p, _) => (if not (null (nth (nth inb p) a)) then SOME p else NONE))
    pairs;
val always_committed = less_nat one_nata (size_list ins_committed);
                                      in
maps (fn p =>
       let
         val outs = nth (nth outa p) a;
       in
         (if null outs then []
           else (if not always_committed andalso
                      ((equal_lista equal_nat ins_committed [p] orelse
                         null ins_committed) andalso
                        not (list_ex (fn (q, _) => equal_nata q p) pairs))
                  then []
                  else let
                         val combs =
                           make_combs broadcast bounds automata p a inb;
                         val outsa = map (fn aa => (p, aa)) outs;
                         val combsa =
                           (if null combs then map (fn x => [x]) outsa
                             else maps (fn x => map (fn aa => x :: aa) combs)
                                    outsa);
                         val init = ([], (Broad a, ([], (la, s))));
                       in
                         compute_upds_impl bounds init combsa
                       end))
       end)
  (upt zero_nata n_ps)
                                      end)
                                 (upt zero_nata num_actions))
                      end);
                  val bin_trans_impl =
                    (fn (la, s) =>
                      let
                        val pairs = get_committed broadcast bounds automata la;
                        val ina =
                          all_actions_by_state broadcast bounds automata
                            num_actions trans_in_map la;
                        val out =
                          all_actions_by_state broadcast bounds automata
                            num_actions trans_out_map la;
                      in
                        (if null pairs
                          then maps (fn a =>
                                      pairs_by_action_impl bounds la s
(nth out a) (nth ina a))
                                 (bin_actions broadcast num_actions)
                          else let
                                 val in2 =
                                   all_actions_from_vec num_actions trans_in_map
                                     pairs;
                                 val out2 =
                                   all_actions_from_vec num_actions
                                     trans_out_map pairs;
                               in
                                 maps (fn a =>
pairs_by_action_impl bounds la s (nth out a) (nth in2 a))
                                   (bin_actions broadcast num_actions) @
                                   maps (fn a =>
  pairs_by_action_impl bounds la s (nth out2 a) (nth ina a))
                                     (bin_actions broadcast num_actions)
                               end)
                      end);
                  val int_trans_impl =
                    (fn (la, s) =>
                      let
                        val pairs = get_committed broadcast bounds automata la;
                      in
                        (if null pairs then int_trans_from_all_impl la s
                          else int_trans_from_vec_impl pairs la s)
                      end);
                in
                  (fn st =>
                    int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st)
                end;
            in
              (fn ai => fn bi =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli (trans_impl ai) (fn _ => (fn () => true))
                     (fn xb => fn sigma =>
                       (fn f_ => fn () => f_
                         ((v_dbm_impl
                            (linordered_cancel_ab_monoid_add_int, heap_int) m)
                         ()) ())
                         (fn x =>
                           (fn f_ => fn () => f_
                             ((abstr_FW_impl_int m
                                (inv_fun (snd (snd (snd xb)))) x)
                             ()) ())
                             (fn xa =>
                               (fn f_ => fn () => f_
                                 ((pre_reset_list_impl m xa
                                    (fst (snd (snd xb))))
                                 ()) ())
                                 (fn xc =>
                                   (fn f_ => fn () => f_
                                     ((abstr_FW_impl_int m (fst xb) xc) ()) ())
                                     (fn xd =>
                                       (fn f_ => fn () => f_
 ((abstr_FW_impl_int m (inv_fun ai) xd) ()) ())
 (fn xe =>
   (fn f_ => fn () => f_ ((down_impl_int m xe) ()) ())
     (fn x_c => (fn () => (x_c :: sigma)))))))))
                     [])
                  ()) ())
                  (fn x => dbm_subset_fed_impl m bi (op_list_rev x)))
            end
              l
             ma)
          ()) ())
          (fn r => (fn () => (not r))));
    val pi =
      (fn (a1, a2) =>
        (fn f_ => fn () => f_
          ((imp_for_int zero_nata (plus_nata m one_nata) (fn a => (fn () => a))
             (fn xc => fn _ =>
               imp_for_int zero_nata (plus_nata m one_nata)
                 (fn a => (fn () => a))
                 (fn xf => fn _ =>
                   imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xj => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xj))
                         ()) ())
                         (fn x_i =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (xc, xf))
                             ()) ())
                             (fn x =>
                               (fn f_ => fn () => f_
                                 ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                    (xf, xj))
                                 ()) ())
                                 (fn xa =>
                                   (fn () =>
                                     (dbm_le_int x_i (dbm_add_int x xa)))))))
                     true)
                 true)
             true)
          ()) ())
          (fn x =>
            (fn f_ => fn () => f_ ((check_diag_impl_int m a2) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_
                  ((imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xc => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xc))
                         ()) ())
                         (fn x_d => (fn () => (dbm_le_int x_d (Le zero_inta)))))
                     true)
                  ()) ())
                  (fn xb =>
                    (fn f_ => fn () => f_
                      ((imp_for_int zero_nata (plus_nata m one_nata)
                         (fn a => (fn () => a))
                         (fn xc => fn _ =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (zero_nata, xc))
                             ()) ())
                             (fn x_e =>
                               (fn () => (dbm_le_int x_e (Le zero_inta)))))
                         true)
                      ()) ())
                      (fn xc =>
                        (fn () =>
                          (check_states a1 andalso
                            ((x orelse xa) andalso (xb andalso xc)))))))));
    val copyi = amtx_copy (heap_DBMEntry heap_int);
    val lei = dbm_subset_impl_int m;
    val l_0i =
      (fn () =>
        (l_0, map (the o map_of equal_nat s_0) (upt zero_nata (n_vs bounds))));
    val s_0i =
      amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m) (Le zero_inta);
    val succsi =
      let
        val n_ps = size_list automata;
        val invs =
          Vector.fromList
            (map (fn i =>
                   let
                     val ma =
                       default_map_of equal_nat []
                         (snd (snd (snd (nth automata i))));
                     val mb =
                       Vector.fromList (map ma (upt zero_nata (num_states i)));
                   in
                     mb
                   end)
              (upt zero_nata n_ps));
        val inv_fun =
          (fn (l, _) =>
            maps (fn i => sub (sub invs i) (nth l i)) (upt zero_nata n_ps));
        val trans_mapa = trans_map automata;
        val trans_i_map =
          (fn i => fn j =>
            map_filter
              (fn a =>
                (case a of (_, (_, (In _, (_, _)))) => NONE
                  | (_, (_, (Out _, (_, _)))) => NONE
                  | (b, (g, (Sil aa, (ma, l)))) =>
                    SOME (b, (g, (aa, (ma, l))))))
              (trans_mapa i j));
        val int_trans_from_loc_impl =
          (fn p => fn l => fn la => fn s =>
            let
              val a = trans_i_map p l;
            in
              map_filter
                (fn (b, (g, (aa, (f, (r, lb))))) =>
                  let
                    val sa = mk_updsi s f;
                  in
                    (if bvali (equal_int, linorder_int) s b andalso
                          check_boundedi bounds sa
                      then SOME (g, (Internal aa,
                                      (r, (list_update la p lb, sa))))
                      else NONE)
                  end)
                a
            end);
        val int_trans_from_vec_impl =
          (fn pairs => fn l => fn s =>
            maps (fn (p, la) => int_trans_from_loc_impl p la l s) pairs);
        val int_trans_from_all_impl =
          (fn l => fn s =>
            maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
              (upt zero_nata n_ps));
        val trans_out_map =
          (fn i => fn j =>
            map_filter
              (fn a =>
                (case a of (_, (_, (In _, (_, _)))) => NONE
                  | (b, (g, (Out aa, (ma, l)))) => SOME (b, (g, (aa, (ma, l))))
                  | (_, (_, (Sil _, (_, _)))) => NONE))
              (trans_mapa i j));
        val trans_in_map =
          (fn i => fn j =>
            map_filter
              (fn a =>
                (case a
                  of (b, (g, (In aa, (ma, l)))) => SOME (b, (g, (aa, (ma, l))))
                  | (_, (_, (Out _, (_, _)))) => NONE
                  | (_, (_, (Sil _, (_, _)))) => NONE))
              (trans_mapa i j));
        val trans_out_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn a =>
                  (case a of (_, (_, (In _, (_, _)))) => NONE
                    | (b, (g, (Out aa, (ma, l)))) =>
                      (if membera equal_nat broadcast aa
                        then SOME (b, (g, (aa, (ma, l)))) else NONE)
                    | (_, (_, (Sil _, (_, _)))) => NONE))
                (trans_mapa i j)));
        val trans_in_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn a =>
                  (case a
                    of (b, (g, (In aa, (ma, l)))) =>
                      (if membera equal_nat broadcast aa
                        then SOME (b, (g, (aa, (ma, l)))) else NONE)
                    | (_, (_, (Out _, (_, _)))) => NONE
                    | (_, (_, (Sil _, (_, _)))) => NONE))
                (trans_mapa i j)));
        val broad_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_committed broadcast bounds automata l;
              val ina =
                map (fn p => trans_in_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val out =
                map (fn p => trans_out_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val inb =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  ina;
              val outa =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  out;
            in
              (if null pairs
                then maps (fn a =>
                            maps (fn p =>
                                   let
                                     val outs = nth (nth outa p) a;
                                   in
                                     (if null outs then []
                                       else let
      val combs = make_combs broadcast bounds automata p a inb;
      val outsa = map (fn aa => (p, aa)) outs;
      val combsa =
        (if null combs then map (fn x => [x]) outsa
          else maps (fn x => map (fn aa => x :: aa) combs) outsa);
      val init = ([], (Broad a, ([], (l, s))));
    in
      compute_upds_impl bounds init combsa
    end)
                                   end)
                              (upt zero_nata n_ps))
                       (upt zero_nata num_actions)
                else maps (fn a =>
                            let
                              val ins_committed =
                                map_filter
                                  (fn (p, _) =>
                                    (if not (null (nth (nth inb p) a))
                                      then SOME p else NONE))
                                  pairs;
                              val always_committed =
                                less_nat one_nata (size_list ins_committed);
                            in
                              maps (fn p =>
                                     let
                                       val outs = nth (nth outa p) a;
                                     in
                                       (if null outs then []
 else (if not always_committed andalso
            ((equal_lista equal_nat ins_committed [p] orelse
               null ins_committed) andalso
              not (list_ex (fn (q, _) => equal_nata q p) pairs))
        then []
        else let
               val combs = make_combs broadcast bounds automata p a inb;
               val outsa = map (fn aa => (p, aa)) outs;
               val combsa =
                 (if null combs then map (fn x => [x]) outsa
                   else maps (fn x => map (fn aa => x :: aa) combs) outsa);
               val init = ([], (Broad a, ([], (l, s))));
             in
               compute_upds_impl bounds init combsa
             end))
                                     end)
                                (upt zero_nata n_ps)
                            end)
                       (upt zero_nata num_actions))
            end);
        val bin_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_committed broadcast bounds automata l;
              val ina =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_in_map l;
              val out =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_out_map l;
            in
              (if null pairs
                then maps (fn a =>
                            pairs_by_action_impl bounds l s (nth out a)
                              (nth ina a))
                       (bin_actions broadcast num_actions)
                else let
                       val in2 =
                         all_actions_from_vec num_actions trans_in_map pairs;
                       val out2 =
                         all_actions_from_vec num_actions trans_out_map pairs;
                     in
                       maps (fn a =>
                              pairs_by_action_impl bounds l s (nth out a)
                                (nth in2 a))
                         (bin_actions broadcast num_actions) @
                         maps (fn a =>
                                pairs_by_action_impl bounds l s (nth out2 a)
                                  (nth ina a))
                           (bin_actions broadcast num_actions)
                     end)
            end);
        val int_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_committed broadcast bounds automata l;
            in
              (if null pairs then int_trans_from_all_impl l s
                else int_trans_from_vec_impl pairs l s)
            end);
        val trans_impl =
          (fn st =>
            int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st);
        val e_op_impl =
          (fn ai => fn bic => fn bib => fn bia => fn bi =>
            (fn f_ => fn () => f_ ((up_canonical_upd_impl_int m bi m) ()) ())
              (fn x =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli (inv_fun ai) (fn _ => (fn () => true))
                     (fn aia => fn bid =>
                       (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid)
                         ()) ())
                         (fn xa =>
                           repair_pair_impl_int m xa zero_nata
                             (constraint_clk aia)))
                     x)
                  ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((check_diag_impl_int m xa) ()) ())
                      (fn xaa =>
                        (fn f_ => fn () => f_
                          ((if xaa
                             then mtx_set (heap_DBMEntry heap_int) (suc m) xa
                                    (zero_nata, zero_nata) (Lt zero_inta)
                             else imp_nfoldli bib (fn _ => (fn () => true))
                                    (fn aia => fn bid =>
                                      (fn f_ => fn () => f_
((abstra_upd_impl_int m aia bid) ()) ())
(fn xb => repair_pair_impl_int m xb zero_nata (constraint_clk aia)))
                                    xa)
                          ()) ())
                          (fn x_a =>
                            (fn f_ => fn () => f_ ((check_diag_impl_int m x_a)
                              ()) ())
                              (fn x_b =>
                                (if x_b
                                  then mtx_set (heap_DBMEntry heap_int) (suc m)
 x_a (zero_nata, zero_nata) (Lt zero_inta)
                                  else (fn f_ => fn () => f_
 ((imp_nfoldli bic (fn _ => (fn () => true))
    (fn xc => fn sigma => reset_canonical_upd_impl_int m sigma m xc zero_inta)
    x_a)
 ()) ())
 (imp_nfoldli (inv_fun bia) (fn _ => (fn () => true))
   (fn aia => fn bid =>
     (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
       (fn xb =>
         repair_pair_impl_int m xb zero_nata (constraint_clk aia)))))))))));
      in
        (fn ai => fn bi =>
          (if null bi then (fn () => [])
            else imp_nfoldli (trans_impl ai) (fn _ => (fn () => true))
                   (fn xc => fn sigma =>
                     let
                       val (a1, (_, (a1b, a2b))) = xc;
                     in
                       (fn f_ => fn () => f_
                         ((heap_map (amtx_copy (heap_DBMEntry heap_int)) bi) ())
                         ())
                         (fn x =>
                           (fn f_ => fn () => f_
                             ((imp_nfoldli x (fn _ => (fn () => true))
                                (fn xb => fn sigmaa =>
                                  (fn f_ => fn () => f_
                                    ((pR_CONST e_op_impl ai a1b a1 a2b xb) ())
                                    ())
                                    (fn x_c =>
                                      (fn f_ => fn () => f_
((check_diag_impl_int m x_c) ()) ())
(fn x_e => (fn () => (if x_e then sigmaa else op_list_prepend x_c sigmaa)))))
                                [])
                             ()) ())
                             (fn x_d =>
                               (fn () => (op_list_prepend (a2b, x_d) sigma))))
                     end)
                   []))
      end;
    val a =
      (fn f_ => fn () => f_
        ((ht_new
           (hashable_prod (hashable_list hashable_nat)
              (hashable_list hashable_int),
             heap_prod (heap_list heap_nat) (heap_list heap_int))
           (heap_list (heap_array (typerep_DBMEntry typerep_int))))
        ()) ())
        (imp_nfoldli m_list (fn _ => (fn () => true))
          (fn xc => fn sigma =>
            (fn f_ => fn () => f_
              ((imp_nfoldli (snd xc) (fn _ => (fn () => true))
                 (fn xg => fn sigmaa =>
                   (fn f_ => fn () => f_ (((fn () => Array.fromList xg)) ()) ())
                     (fn x_g => (fn () => (x_g :: sigmaa))))
                 [])
              ()) ())
              (fn x_e =>
                ht_update
                  (equal_prod (equal_list equal_nat) (equal_list equal_int),
                    hashable_prod (hashable_list hashable_nat)
                      (hashable_list hashable_int),
                    heap_prod (heap_list heap_nat) (heap_list heap_int))
                  (heap_list (heap_array (typerep_DBMEntry typerep_int)))
                  (fst xc) x_e sigma)));
  in
    certify_unreachable_impl2
      (equal_prod (equal_list equal_nat) (equal_list equal_int),
        hashable_prod (hashable_list hashable_nat) (hashable_list hashable_int),
        heap_prod (heap_list heap_nat) (heap_list heap_int))
      (heap_array (typerep_DBMEntry typerep_int)) fi pi copyi lei succsi l_0i
      s_0i (split_k num_split) l_list a
  end;

fun certificate_checker2 num_split dc m_list broadcast bounds automata m
  num_states num_actions k l_0 s_0 formula =
  let
    val l_list = map fst m_list;
  in
    (case certificate_checker_pre l_list m_list broadcast bounds automata m
            num_states num_actions k l_0 s_0 formula
      of true =>
        (if dc
          then no_deadlock_certifier2 broadcast bounds automata m num_states
                 num_actions l_0 s_0 l_list m_list num_split
          else unreachability_checker2 broadcast bounds automata m num_states
                 num_actions l_0 s_0 formula l_list m_list num_split)
      | false => false)
  end;

fun rename_check2 num_split dc broadcast bounds automata k l_0 s_0 formula m
  num_states num_actions renum_acts renum_vars renum_clocks renum_states
  state_space =
  (case do_rename_mc show_int (show_list show_char) (show_list show_char)
          (show_list show_char)
          (fn _ => fn _ => certificate_checker2 num_split dc state_space) dc
          broadcast bounds automata k "_urge" l_0 s_0 formula m num_states
          num_actions renum_acts renum_vars renum_clocks renum_states
          (fn _ => fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
          (fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
          (fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
    of NONE => Renaming_Failed | SOME true => Sat | SOME false => Unsat);

fun no_deadlock_certifier broadcast bounds automata m num_states num_actions l_0
  s_0 l_list m_list num_split =
  let
    val states_ia =
      map (states_i automata) (upt zero_nata (size_list automata));
    val check_states =
      (fn (l, s) =>
        equal_nata (size_list l) (size_list automata) andalso
          let
            val d = minus_nata (size_list automata) one_nata;
          in
            (if less_nat d (size_list automata)
              then all_interval (equal_nat, interval_nat)
                     (fn i =>
                       member (ceq_nat, ccompare_nat) (nth l i)
                         (nth states_ia i))
                     zero_nata d
              else true)
          end andalso
          (equal_nata (size_list s) (n_vs bounds) andalso
            check_boundedi bounds s));
    val fi =
      (fn (l, ma) =>
        (fn f_ => fn () => f_
          ((let
              val n_ps = size_list automata;
              val invs =
                Vector.fromList
                  (map (fn i =>
                         let
                           val mb =
                             default_map_of equal_nat []
                               (snd (snd (snd (nth automata i))));
                           val mc =
                             Vector.fromList
                               (map mb (upt zero_nata (num_states i)));
                         in
                           mc
                         end)
                    (upt zero_nata n_ps));
              val inv_fun =
                (fn (la, _) =>
                  maps (fn i => sub (sub invs i) (nth la i))
                    (upt zero_nata n_ps));
              val trans_impl =
                let
                  val trans_mapa = trans_map automata;
                  val trans_i_map =
                    (fn i => fn j =>
                      map_filter
                        (fn a =>
                          (case a of (_, (_, (In _, (_, _)))) => NONE
                            | (_, (_, (Out _, (_, _)))) => NONE
                            | (b, (g, (Sil aa, (mb, la)))) =>
                              SOME (b, (g, (aa, (mb, la))))))
                        (trans_mapa i j));
                  val int_trans_from_loc_impl =
                    (fn p => fn la => fn laa => fn s =>
                      let
                        val a = trans_i_map p la;
                      in
                        map_filter
                          (fn (b, (g, (aa, (f, (r, lb))))) =>
                            let
                              val sa = mk_updsi s f;
                            in
                              (if bvali (equal_int, linorder_int) s b andalso
                                    check_boundedi bounds sa
                                then SOME (g,
    (Internal aa, (r, (list_update laa p lb, sa))))
                                else NONE)
                            end)
                          a
                      end);
                  val int_trans_from_vec_impl =
                    (fn pairs => fn la => fn s =>
                      maps (fn (p, laa) => int_trans_from_loc_impl p laa la s)
                        pairs);
                  val int_trans_from_all_impl =
                    (fn la => fn s =>
                      maps (fn p => int_trans_from_loc_impl p (nth la p) la s)
                        (upt zero_nata n_ps));
                  val trans_out_map =
                    (fn i => fn j =>
                      map_filter
                        (fn a =>
                          (case a of (_, (_, (In _, (_, _)))) => NONE
                            | (b, (g, (Out aa, (mb, la)))) =>
                              SOME (b, (g, (aa, (mb, la))))
                            | (_, (_, (Sil _, (_, _)))) => NONE))
                        (trans_mapa i j));
                  val trans_in_map =
                    (fn i => fn j =>
                      map_filter
                        (fn a =>
                          (case a
                            of (b, (g, (In aa, (mb, la)))) =>
                              SOME (b, (g, (aa, (mb, la))))
                            | (_, (_, (Out _, (_, _)))) => NONE
                            | (_, (_, (Sil _, (_, _)))) => NONE))
                        (trans_mapa i j));
                  val trans_out_broad_grouped =
                    (fn i => fn j =>
                      actions_by_statea num_actions
                        (map_filter
                          (fn a =>
                            (case a of (_, (_, (In _, (_, _)))) => NONE
                              | (b, (g, (Out aa, (mb, la)))) =>
                                (if membera equal_nat broadcast aa
                                  then SOME (b, (g, (aa, (mb, la)))) else NONE)
                              | (_, (_, (Sil _, (_, _)))) => NONE))
                          (trans_mapa i j)));
                  val trans_in_broad_grouped =
                    (fn i => fn j =>
                      actions_by_statea num_actions
                        (map_filter
                          (fn a =>
                            (case a
                              of (b, (g, (In aa, (mb, la)))) =>
                                (if membera equal_nat broadcast aa
                                  then SOME (b, (g, (aa, (mb, la)))) else NONE)
                              | (_, (_, (Out _, (_, _)))) => NONE
                              | (_, (_, (Sil _, (_, _)))) => NONE))
                          (trans_mapa i j)));
                  val broad_trans_impl =
                    (fn (la, s) =>
                      let
                        val pairs = get_committed broadcast bounds automata la;
                        val ina =
                          map (fn p => trans_in_broad_grouped p (nth la p))
                            (upt zero_nata n_ps);
                        val out =
                          map (fn p => trans_out_broad_grouped p (nth la p))
                            (upt zero_nata n_ps);
                        val inb =
                          map (map (filter
                                     (fn (b, _) =>
                                       bvali (equal_int, linorder_int) s b)))
                            ina;
                        val outa =
                          map (map (filter
                                     (fn (b, _) =>
                                       bvali (equal_int, linorder_int) s b)))
                            out;
                      in
                        (if null pairs
                          then maps (fn a =>
                                      maps
(fn p =>
  let
    val outs = nth (nth outa p) a;
  in
    (if null outs then []
      else let
             val combs = make_combs broadcast bounds automata p a inb;
             val outsa = map (fn aa => (p, aa)) outs;
             val combsa =
               (if null combs then map (fn x => [x]) outsa
                 else maps (fn x => map (fn aa => x :: aa) combs) outsa);
             val init = ([], (Broad a, ([], (la, s))));
           in
             compute_upds_impl bounds init combsa
           end)
  end)
(upt zero_nata n_ps))
                                 (upt zero_nata num_actions)
                          else maps (fn a =>
                                      let
val ins_committed =
  map_filter
    (fn (p, _) => (if not (null (nth (nth inb p) a)) then SOME p else NONE))
    pairs;
val always_committed = less_nat one_nata (size_list ins_committed);
                                      in
maps (fn p =>
       let
         val outs = nth (nth outa p) a;
       in
         (if null outs then []
           else (if not always_committed andalso
                      ((equal_lista equal_nat ins_committed [p] orelse
                         null ins_committed) andalso
                        not (list_ex (fn (q, _) => equal_nata q p) pairs))
                  then []
                  else let
                         val combs =
                           make_combs broadcast bounds automata p a inb;
                         val outsa = map (fn aa => (p, aa)) outs;
                         val combsa =
                           (if null combs then map (fn x => [x]) outsa
                             else maps (fn x => map (fn aa => x :: aa) combs)
                                    outsa);
                         val init = ([], (Broad a, ([], (la, s))));
                       in
                         compute_upds_impl bounds init combsa
                       end))
       end)
  (upt zero_nata n_ps)
                                      end)
                                 (upt zero_nata num_actions))
                      end);
                  val bin_trans_impl =
                    (fn (la, s) =>
                      let
                        val pairs = get_committed broadcast bounds automata la;
                        val ina =
                          all_actions_by_state broadcast bounds automata
                            num_actions trans_in_map la;
                        val out =
                          all_actions_by_state broadcast bounds automata
                            num_actions trans_out_map la;
                      in
                        (if null pairs
                          then maps (fn a =>
                                      pairs_by_action_impl bounds la s
(nth out a) (nth ina a))
                                 (bin_actions broadcast num_actions)
                          else let
                                 val in2 =
                                   all_actions_from_vec num_actions trans_in_map
                                     pairs;
                                 val out2 =
                                   all_actions_from_vec num_actions
                                     trans_out_map pairs;
                               in
                                 maps (fn a =>
pairs_by_action_impl bounds la s (nth out a) (nth in2 a))
                                   (bin_actions broadcast num_actions) @
                                   maps (fn a =>
  pairs_by_action_impl bounds la s (nth out2 a) (nth ina a))
                                     (bin_actions broadcast num_actions)
                               end)
                      end);
                  val int_trans_impl =
                    (fn (la, s) =>
                      let
                        val pairs = get_committed broadcast bounds automata la;
                      in
                        (if null pairs then int_trans_from_all_impl la s
                          else int_trans_from_vec_impl pairs la s)
                      end);
                in
                  (fn st =>
                    int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st)
                end;
            in
              (fn ai => fn bi =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli (trans_impl ai) (fn _ => (fn () => true))
                     (fn xb => fn sigma =>
                       (fn f_ => fn () => f_
                         ((v_dbm_impl
                            (linordered_cancel_ab_monoid_add_int, heap_int) m)
                         ()) ())
                         (fn x =>
                           (fn f_ => fn () => f_
                             ((abstr_FW_impl_int m
                                (inv_fun (snd (snd (snd xb)))) x)
                             ()) ())
                             (fn xa =>
                               (fn f_ => fn () => f_
                                 ((pre_reset_list_impl m xa
                                    (fst (snd (snd xb))))
                                 ()) ())
                                 (fn xc =>
                                   (fn f_ => fn () => f_
                                     ((abstr_FW_impl_int m (fst xb) xc) ()) ())
                                     (fn xd =>
                                       (fn f_ => fn () => f_
 ((abstr_FW_impl_int m (inv_fun ai) xd) ()) ())
 (fn xe =>
   (fn f_ => fn () => f_ ((down_impl_int m xe) ()) ())
     (fn x_c => (fn () => (x_c :: sigma)))))))))
                     [])
                  ()) ())
                  (fn x => dbm_subset_fed_impl m bi (op_list_rev x)))
            end
              l
             ma)
          ()) ())
          (fn r => (fn () => (not r))));
    val pi =
      (fn (a1, a2) =>
        (fn f_ => fn () => f_
          ((imp_for_int zero_nata (plus_nata m one_nata) (fn a => (fn () => a))
             (fn xc => fn _ =>
               imp_for_int zero_nata (plus_nata m one_nata)
                 (fn a => (fn () => a))
                 (fn xf => fn _ =>
                   imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xj => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xj))
                         ()) ())
                         (fn x_i =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (xc, xf))
                             ()) ())
                             (fn x =>
                               (fn f_ => fn () => f_
                                 ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                    (xf, xj))
                                 ()) ())
                                 (fn xa =>
                                   (fn () =>
                                     (dbm_le_int x_i (dbm_add_int x xa)))))))
                     true)
                 true)
             true)
          ()) ())
          (fn x =>
            (fn f_ => fn () => f_ ((check_diag_impl_int m a2) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_
                  ((imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xc => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xc))
                         ()) ())
                         (fn x_d => (fn () => (dbm_le_int x_d (Le zero_inta)))))
                     true)
                  ()) ())
                  (fn xb =>
                    (fn f_ => fn () => f_
                      ((imp_for_int zero_nata (plus_nata m one_nata)
                         (fn a => (fn () => a))
                         (fn xc => fn _ =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (zero_nata, xc))
                             ()) ())
                             (fn x_e =>
                               (fn () => (dbm_le_int x_e (Le zero_inta)))))
                         true)
                      ()) ())
                      (fn xc =>
                        (fn () =>
                          (check_states a1 andalso
                            ((x orelse xa) andalso (xb andalso xc)))))))));
    val copyi = amtx_copy (heap_DBMEntry heap_int);
    val lei = dbm_subset_impl_int m;
    val l_0i =
      (fn () =>
        (l_0, map (the o map_of equal_nat s_0) (upt zero_nata (n_vs bounds))));
    val s_0i =
      amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m) (Le zero_inta);
    val succsi =
      let
        val n_ps = size_list automata;
        val invs =
          Vector.fromList
            (map (fn i =>
                   let
                     val ma =
                       default_map_of equal_nat []
                         (snd (snd (snd (nth automata i))));
                     val mb =
                       Vector.fromList (map ma (upt zero_nata (num_states i)));
                   in
                     mb
                   end)
              (upt zero_nata n_ps));
        val inv_fun =
          (fn (l, _) =>
            maps (fn i => sub (sub invs i) (nth l i)) (upt zero_nata n_ps));
        val trans_mapa = trans_map automata;
        val trans_i_map =
          (fn i => fn j =>
            map_filter
              (fn a =>
                (case a of (_, (_, (In _, (_, _)))) => NONE
                  | (_, (_, (Out _, (_, _)))) => NONE
                  | (b, (g, (Sil aa, (ma, l)))) =>
                    SOME (b, (g, (aa, (ma, l))))))
              (trans_mapa i j));
        val int_trans_from_loc_impl =
          (fn p => fn l => fn la => fn s =>
            let
              val a = trans_i_map p l;
            in
              map_filter
                (fn (b, (g, (aa, (f, (r, lb))))) =>
                  let
                    val sa = mk_updsi s f;
                  in
                    (if bvali (equal_int, linorder_int) s b andalso
                          check_boundedi bounds sa
                      then SOME (g, (Internal aa,
                                      (r, (list_update la p lb, sa))))
                      else NONE)
                  end)
                a
            end);
        val int_trans_from_vec_impl =
          (fn pairs => fn l => fn s =>
            maps (fn (p, la) => int_trans_from_loc_impl p la l s) pairs);
        val int_trans_from_all_impl =
          (fn l => fn s =>
            maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
              (upt zero_nata n_ps));
        val trans_out_map =
          (fn i => fn j =>
            map_filter
              (fn a =>
                (case a of (_, (_, (In _, (_, _)))) => NONE
                  | (b, (g, (Out aa, (ma, l)))) => SOME (b, (g, (aa, (ma, l))))
                  | (_, (_, (Sil _, (_, _)))) => NONE))
              (trans_mapa i j));
        val trans_in_map =
          (fn i => fn j =>
            map_filter
              (fn a =>
                (case a
                  of (b, (g, (In aa, (ma, l)))) => SOME (b, (g, (aa, (ma, l))))
                  | (_, (_, (Out _, (_, _)))) => NONE
                  | (_, (_, (Sil _, (_, _)))) => NONE))
              (trans_mapa i j));
        val trans_out_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn a =>
                  (case a of (_, (_, (In _, (_, _)))) => NONE
                    | (b, (g, (Out aa, (ma, l)))) =>
                      (if membera equal_nat broadcast aa
                        then SOME (b, (g, (aa, (ma, l)))) else NONE)
                    | (_, (_, (Sil _, (_, _)))) => NONE))
                (trans_mapa i j)));
        val trans_in_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn a =>
                  (case a
                    of (b, (g, (In aa, (ma, l)))) =>
                      (if membera equal_nat broadcast aa
                        then SOME (b, (g, (aa, (ma, l)))) else NONE)
                    | (_, (_, (Out _, (_, _)))) => NONE
                    | (_, (_, (Sil _, (_, _)))) => NONE))
                (trans_mapa i j)));
        val broad_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_committed broadcast bounds automata l;
              val ina =
                map (fn p => trans_in_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val out =
                map (fn p => trans_out_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val inb =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  ina;
              val outa =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  out;
            in
              (if null pairs
                then maps (fn a =>
                            maps (fn p =>
                                   let
                                     val outs = nth (nth outa p) a;
                                   in
                                     (if null outs then []
                                       else let
      val combs = make_combs broadcast bounds automata p a inb;
      val outsa = map (fn aa => (p, aa)) outs;
      val combsa =
        (if null combs then map (fn x => [x]) outsa
          else maps (fn x => map (fn aa => x :: aa) combs) outsa);
      val init = ([], (Broad a, ([], (l, s))));
    in
      compute_upds_impl bounds init combsa
    end)
                                   end)
                              (upt zero_nata n_ps))
                       (upt zero_nata num_actions)
                else maps (fn a =>
                            let
                              val ins_committed =
                                map_filter
                                  (fn (p, _) =>
                                    (if not (null (nth (nth inb p) a))
                                      then SOME p else NONE))
                                  pairs;
                              val always_committed =
                                less_nat one_nata (size_list ins_committed);
                            in
                              maps (fn p =>
                                     let
                                       val outs = nth (nth outa p) a;
                                     in
                                       (if null outs then []
 else (if not always_committed andalso
            ((equal_lista equal_nat ins_committed [p] orelse
               null ins_committed) andalso
              not (list_ex (fn (q, _) => equal_nata q p) pairs))
        then []
        else let
               val combs = make_combs broadcast bounds automata p a inb;
               val outsa = map (fn aa => (p, aa)) outs;
               val combsa =
                 (if null combs then map (fn x => [x]) outsa
                   else maps (fn x => map (fn aa => x :: aa) combs) outsa);
               val init = ([], (Broad a, ([], (l, s))));
             in
               compute_upds_impl bounds init combsa
             end))
                                     end)
                                (upt zero_nata n_ps)
                            end)
                       (upt zero_nata num_actions))
            end);
        val bin_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_committed broadcast bounds automata l;
              val ina =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_in_map l;
              val out =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_out_map l;
            in
              (if null pairs
                then maps (fn a =>
                            pairs_by_action_impl bounds l s (nth out a)
                              (nth ina a))
                       (bin_actions broadcast num_actions)
                else let
                       val in2 =
                         all_actions_from_vec num_actions trans_in_map pairs;
                       val out2 =
                         all_actions_from_vec num_actions trans_out_map pairs;
                     in
                       maps (fn a =>
                              pairs_by_action_impl bounds l s (nth out a)
                                (nth in2 a))
                         (bin_actions broadcast num_actions) @
                         maps (fn a =>
                                pairs_by_action_impl bounds l s (nth out2 a)
                                  (nth ina a))
                           (bin_actions broadcast num_actions)
                     end)
            end);
        val int_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_committed broadcast bounds automata l;
            in
              (if null pairs then int_trans_from_all_impl l s
                else int_trans_from_vec_impl pairs l s)
            end);
        val trans_impl =
          (fn st =>
            int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st);
        val e_op_impl =
          (fn ai => fn bic => fn bib => fn bia => fn bi =>
            (fn f_ => fn () => f_ ((up_canonical_upd_impl_int m bi m) ()) ())
              (fn x =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli (inv_fun ai) (fn _ => (fn () => true))
                     (fn aia => fn bid =>
                       (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid)
                         ()) ())
                         (fn xa =>
                           repair_pair_impl_int m xa zero_nata
                             (constraint_clk aia)))
                     x)
                  ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((check_diag_impl_int m xa) ()) ())
                      (fn xaa =>
                        (fn f_ => fn () => f_
                          ((if xaa
                             then mtx_set (heap_DBMEntry heap_int) (suc m) xa
                                    (zero_nata, zero_nata) (Lt zero_inta)
                             else imp_nfoldli bib (fn _ => (fn () => true))
                                    (fn aia => fn bid =>
                                      (fn f_ => fn () => f_
((abstra_upd_impl_int m aia bid) ()) ())
(fn xb => repair_pair_impl_int m xb zero_nata (constraint_clk aia)))
                                    xa)
                          ()) ())
                          (fn x_a =>
                            (fn f_ => fn () => f_ ((check_diag_impl_int m x_a)
                              ()) ())
                              (fn x_b =>
                                (if x_b
                                  then mtx_set (heap_DBMEntry heap_int) (suc m)
 x_a (zero_nata, zero_nata) (Lt zero_inta)
                                  else (fn f_ => fn () => f_
 ((imp_nfoldli bic (fn _ => (fn () => true))
    (fn xc => fn sigma => reset_canonical_upd_impl_int m sigma m xc zero_inta)
    x_a)
 ()) ())
 (imp_nfoldli (inv_fun bia) (fn _ => (fn () => true))
   (fn aia => fn bid =>
     (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
       (fn xb =>
         repair_pair_impl_int m xb zero_nata (constraint_clk aia)))))))))));
      in
        (fn ai => fn bi =>
          (if null bi then (fn () => [])
            else imp_nfoldli (trans_impl ai) (fn _ => (fn () => true))
                   (fn xc => fn sigma =>
                     let
                       val (a1, (_, (a1b, a2b))) = xc;
                     in
                       (fn f_ => fn () => f_
                         ((heap_map (amtx_copy (heap_DBMEntry heap_int)) bi) ())
                         ())
                         (fn x =>
                           (fn f_ => fn () => f_
                             ((imp_nfoldli x (fn _ => (fn () => true))
                                (fn xb => fn sigmaa =>
                                  (fn f_ => fn () => f_
                                    ((pR_CONST e_op_impl ai a1b a1 a2b xb) ())
                                    ())
                                    (fn x_c =>
                                      (fn f_ => fn () => f_
((check_diag_impl_int m x_c) ()) ())
(fn x_e => (fn () => (if x_e then sigmaa else op_list_prepend x_c sigmaa)))))
                                [])
                             ()) ())
                             (fn x_d =>
                               (fn () => (op_list_prepend (a2b, x_d) sigma))))
                     end)
                   []))
      end;
    val _ = Timing.start_timer ();
  in
    (fn f_ => fn () => f_
      (((fn f_ => fn () => f_
          ((ht_new
             (hashable_prod (hashable_list hashable_nat)
                (hashable_list hashable_int),
               heap_prod (heap_list heap_nat) (heap_list heap_int))
             (heap_list (heap_array (typerep_DBMEntry typerep_int))))
          ()) ())
         (imp_nfoldli m_list (fn _ => (fn () => true))
           (fn xc => fn sigma =>
             (fn f_ => fn () => f_
               ((imp_nfoldli (snd xc) (fn _ => (fn () => true))
                  (fn xg => fn sigmaa =>
                    (fn f_ => fn () => f_ (((fn () => Array.fromList xg)) ())
                      ())
                      (fn x_g => (fn () => (x_g :: sigmaa))))
                  [])
               ()) ())
               (fn x_e =>
                 ht_update
                   (equal_prod (equal_list equal_nat) (equal_list equal_int),
                     hashable_prod (hashable_list hashable_nat)
                       (hashable_list hashable_int),
                     heap_prod (heap_list heap_nat) (heap_list heap_int))
                   (heap_list (heap_array (typerep_DBMEntry typerep_int)))
                   (fst xc) x_e sigma))))
      ()) ())
      (fn m_table =>
        let
          val _ = Timing.save_time "Time for loading certificate";
        in
          (fn f_ => fn () => f_
            ((certify_unreachable_impl_inner
               (equal_prod (equal_list equal_nat) (equal_list equal_int),
                 hashable_prod (hashable_list hashable_nat)
                   (hashable_list hashable_int),
                 heap_prod (heap_list heap_nat) (heap_list heap_int))
               (heap_array (typerep_DBMEntry typerep_int)) fi pi copyi lei
               succsi l_0i s_0i (split_k num_split) l_list m_table)
            ()) ())
            (fn a => (fn () => a))
        end)
  end;

fun certificate_checker num_split dc m_list broadcast bounds automata m
  num_states num_actions k l_0 s_0 formula =
  let
    val l_list = map fst m_list;
  in
    (case certificate_checker_pre l_list m_list broadcast bounds automata m
            num_states num_actions k l_0 s_0 formula
      of true =>
        (fn f_ => fn () => f_
          ((if dc
             then no_deadlock_certifier broadcast bounds automata m num_states
                    num_actions l_0 s_0 l_list m_list num_split
             else unreachability_checker broadcast bounds automata m num_states
                    num_actions l_0 s_0 formula l_list m_list num_split)
          ()) ())
          (fn r => (fn () => (SOME r)))
      | false => (fn () => NONE))
  end;

fun rename_check num_split dc broadcast bounds automata k l_0 s_0 formula m
  num_states num_actions renum_acts renum_vars renum_clocks renum_states
  state_space =
  (case do_rename_mc show_int (show_list show_char) (show_list show_char)
          (show_list show_char)
          (fn _ => fn _ => certificate_checker num_split dc state_space) dc
          broadcast bounds automata k "_urge" l_0 s_0 formula m num_states
          num_actions renum_acts renum_vars renum_clocks renum_states
          (fn _ => fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
          (fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
          (fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
    of NONE => (fn () => Renaming_Failed)
    | SOME r =>
      (fn f_ => fn () => f_ (r ()) ())
        (fn a =>
          (case a of NONE => (fn () => Preconds_Unsat)
            | SOME true => (fn () => Sat) | SOME false => (fn () => Unsat))));

fun certificate_check A_ B_ C_ mode num_split dc state_space broadcast bounds
  automata k l_0 s_0 formula m num_states num_actions renum_acts renum_vars
  renum_clocks renum_states inv_renum_states inv_renum_vars inv_renum_clocks =
  (case mode
    of Impl1 =>
      rename_check num_split dc broadcast bounds automata k l_0 s_0 formula m
        num_states num_actions renum_acts renum_vars renum_clocks renum_states
        (reach_of state_space)
    | Impl2 =>
      (fn () =>
        (rename_check2 num_split dc broadcast bounds automata k l_0 s_0 formula
          m num_states num_actions renum_acts renum_vars renum_clocks
          renum_states (reach_of state_space)))
    | Impl3 =>
      (fn () =>
        (rename_check3 num_split dc broadcast bounds automata k l_0 s_0 formula
          m num_states num_actions renum_acts renum_vars renum_clocks
          renum_states (reach_of state_space)))
    | Buechi =>
      (fn () =>
        (rename_check_buechi num_split broadcast bounds automata k l_0 s_0
          formula m num_states num_actions renum_acts renum_vars renum_clocks
          renum_states (buechi_of state_space)))
    | Debug =>
      rename_check_dbg A_ B_ C_ num_split dc broadcast bounds automata k l_0 s_0
        formula m num_states num_actions renum_acts renum_vars renum_clocks
        renum_states inv_renum_states inv_renum_vars inv_renum_clocks
        (reach_of state_space));

fun convert_check mode num_split dc model renaming state_space show_cert =
  (case binda (compute_model model renaming)
          (fn (broadcast,
                (bounds,
                  (automata,
                    (urgent_locations,
                      (k, (l_0, (s_0, (formula,
(m, (num_states,
      (num_actions,
        (renum_acts,
          (renum_vars,
            (renum_clocks,
              (renum_states,
                (inv_renum_states,
                  (inv_renum_vars, inv_renum_clocks)))))))))))))))))
             =>
            let
              val is_urgent =
                (fn (l, _) =>
                  list_ex (fn (la, urgent) => membera equal_int urgent la)
                    (zip l (map (map int_of_nat) urgent_locations)));
              val inv_renum_clocksa =
                (fn i =>
                  (if equal_nata i m then "_urge" else inv_renum_clocks i));
              val t = Time.now ();
              val state_spacea = convert_state_space m is_urgent state_space;
              val ta = (fn x => fn y => Time.- (x, y)) (Time.now ()) t;
              val _ =
                writeln ("Time for converting state space: " ^
                          (fn x => Time.toString x) ta);
              val _ = Timing.start_timer ();
              val _ =
                Timing.save_time "Time for converting DBMs in certificate";
              val _ =
                writeln ("Number of discrete states: " ^
                          show_lit show_nat (len_of_state_space state_spacea));
              val _ =
                (if show_cert
                  then let
                         val _ = print_sep ();
                         val _ = writeln "Certificate";
                         val _ = print_sep ();
                         val _ =
                           show_state_space m inv_renum_states inv_renum_vars
                             inv_renum_clocksa state_spacea;
                         val _ = print_sep ();
                       in
                         (fn () => ())
                       end
                  else (fn () => ()));
            in
              Result
                (certificate_check show_nat show_literal show_literal mode
                  num_split dc state_spacea broadcast bounds automata k l_0 s_0
                  formula m num_states num_actions renum_acts renum_vars
                  renum_clocks renum_states inv_renum_states inv_renum_vars
                  inv_renum_clocksa)
            end)
    of Result c =>
      let
        val t = Time.now ();
      in
        (fn f_ => fn () => f_ (c ()) ())
          (fn check =>
            let
              val _ =
                (case check
                  of Renaming_Failed => let
  val _ = writeln "Renaming failed";
in
  (fn () => ())
end
                  | Preconds_Unsat =>
                    let
                      val _ = writeln "Preconditions were not met";
                    in
                      (fn () => ())
                    end
                  | Sat => let
                             val _ = writeln "Certificate was accepted";
                           in
                             (fn () => ())
                           end
                  | Unsat => let
                               val _ = writeln "Certificate was rejected";
                             in
                               (fn () => ())
                             end);
              val ta = (fn x => fn y => Time.- (x, y)) (Time.now ()) t;
              val _ =
                writeln ("Time for certificate checking: " ^
                          (fn x => Time.toString x) ta);
            in
              (fn () => (Result check))
            end)
      end
    | Error es => (fn () => (Error es)));

fun dc_to_lb (DurationConstraint (EQ, ConstantExpr x)) = SOME (GE x)
  | dc_to_lb (DurationConstraint (GEQ, ConstantExpr x)) = SOME (GE x)
  | dc_to_lb (DurationConstraint (LEQ, va)) = NONE
  | dc_to_lb (DurationConstraint (GEQ, DurationExpr)) = NONE
  | dc_to_lb (DurationConstraint (GEQ, AddExpr (v, vb))) = NONE
  | dc_to_lb (DurationConstraint (GEQ, SubExpr (v, vb))) = NONE
  | dc_to_lb (DurationConstraint (GEQ, MulExpr (v, vb))) = NONE
  | dc_to_lb (DurationConstraint (GEQ, DivExpr (v, vb))) = NONE
  | dc_to_lb (DurationConstraint (GEQ, SinExpr v)) = NONE
  | dc_to_lb (DurationConstraint (GEQ, CosExpr v)) = NONE
  | dc_to_lb (DurationConstraint (GEQ, ExpExpr v)) = NONE
  | dc_to_lb (DurationConstraint (GEQ, PiExpr)) = NONE
  | dc_to_lb (DurationConstraint (GEQ, FunctionExpr v)) = NONE
  | dc_to_lb (DurationConstraint (v, DurationExpr)) = NONE
  | dc_to_lb (DurationConstraint (v, AddExpr (vb, vc))) = NONE
  | dc_to_lb (DurationConstraint (v, SubExpr (vb, vc))) = NONE
  | dc_to_lb (DurationConstraint (v, MulExpr (vb, vc))) = NONE
  | dc_to_lb (DurationConstraint (v, DivExpr (vb, vc))) = NONE
  | dc_to_lb (DurationConstraint (v, SinExpr vb)) = NONE
  | dc_to_lb (DurationConstraint (v, CosExpr vb)) = NONE
  | dc_to_lb (DurationConstraint (v, ExpExpr vb)) = NONE
  | dc_to_lb (DurationConstraint (v, PiExpr)) = NONE
  | dc_to_lb (DurationConstraint (v, FunctionExpr vb)) = NONE;

fun dc_to_ub (DurationConstraint (EQ, ConstantExpr x)) = SOME (LE x)
  | dc_to_ub (DurationConstraint (LEQ, ConstantExpr x)) = SOME (LE x)
  | dc_to_ub (DurationConstraint (LEQ, DurationExpr)) = NONE
  | dc_to_ub (DurationConstraint (LEQ, AddExpr (v, vb))) = NONE
  | dc_to_ub (DurationConstraint (LEQ, SubExpr (v, vb))) = NONE
  | dc_to_ub (DurationConstraint (LEQ, MulExpr (v, vb))) = NONE
  | dc_to_ub (DurationConstraint (LEQ, DivExpr (v, vb))) = NONE
  | dc_to_ub (DurationConstraint (LEQ, SinExpr v)) = NONE
  | dc_to_ub (DurationConstraint (LEQ, CosExpr v)) = NONE
  | dc_to_ub (DurationConstraint (LEQ, ExpExpr v)) = NONE
  | dc_to_ub (DurationConstraint (LEQ, PiExpr)) = NONE
  | dc_to_ub (DurationConstraint (LEQ, FunctionExpr v)) = NONE
  | dc_to_ub (DurationConstraint (GEQ, va)) = NONE
  | dc_to_ub (DurationConstraint (v, DurationExpr)) = NONE
  | dc_to_ub (DurationConstraint (v, AddExpr (vb, vc))) = NONE
  | dc_to_ub (DurationConstraint (v, SubExpr (vb, vc))) = NONE
  | dc_to_ub (DurationConstraint (v, MulExpr (vb, vc))) = NONE
  | dc_to_ub (DurationConstraint (v, DivExpr (vb, vc))) = NONE
  | dc_to_ub (DurationConstraint (v, SinExpr vb)) = NONE
  | dc_to_ub (DurationConstraint (v, CosExpr vb)) = NONE
  | dc_to_ub (DurationConstraint (v, ExpExpr vb)) = NONE
  | dc_to_ub (DurationConstraint (v, PiExpr)) = NONE
  | dc_to_ub (DurationConstraint (v, FunctionExpr vb)) = NONE;

fun int_of_digits [] acc = acc
  | int_of_digits (d :: ds) acc =
    int_of_digits ds
      (plus_inta (times_inta acc (Int_of_integer (10 : Int.int)))
        (int_of_nat d));

fun actions (Domain (x1, x2, x3, x4, x5)) = x5;

fun domain (Problem (x1, x2, x3, x4)) = x1;

fun func (FuncDecl (x1, x2)) = x1;

fun check_all_list B_ p l msg msgf =
  catch_error
    (forallM
      (fn x =>
        check (p x)
          (fn _ =>
            shows_prec B_ zero_nata msg o
              shows_prec_list show_char zero_nata
                [Chara (false, true, false, true, true, true, false, false),
                  Chara (false, false, false, false, false, true, false,
                          false)] o
              msgf x))
      l)
    (fn x => Inl (snd x));

fun check_wf_types d =
  check_all_list (show_list show_char)
    (fn (_, t) =>
      ((t : string) = "object") orelse
        member (ceq_literal, ccompare_literal) t
          (image
            (ceq_prod ceq_literal ceq_literal,
              ccompare_prod ccompare_literal ccompare_literal)
            (ceq_literal, ccompare_literal, set_impl_literal) fst
            (set (ceq_prod ceq_literal ceq_literal,
                   ccompare_prod ccompare_literal ccompare_literal,
                   set_impl_prod set_impl_literal set_impl_literal)
              (types d))))
    (types d)
    [Chara (true, false, true, false, true, false, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (false, false, true, false, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (false, false, true, true, false, true, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, false, true, false, false, true, true, false),
      Chara (false, false, false, false, false, true, false, false),
      Chara (true, true, false, false, true, true, true, false),
      Chara (true, false, true, false, true, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (true, false, false, true, true, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false)]
    (shows_prec_literal zero_nata o snd);

fun bexp_and_all [] = True
  | bexp_and_all (x :: xs) = Anda (x, bexp_and_all xs);

fun objects (Problem (x1, x2, x3, x4)) = x2;

fun pred (PredDecl (x1, x2)) = x1;

fun dc_no_func (DurationConstraint (dop, ConstantExpr x)) = true
  | dc_no_func (DurationConstraint (v, DurationExpr)) = false
  | dc_no_func (DurationConstraint (v, AddExpr (vb, vc))) = false
  | dc_no_func (DurationConstraint (v, SubExpr (vb, vc))) = false
  | dc_no_func (DurationConstraint (v, MulExpr (vb, vc))) = false
  | dc_no_func (DurationConstraint (v, DivExpr (vb, vc))) = false
  | dc_no_func (DurationConstraint (v, SinExpr vb)) = false
  | dc_no_func (DurationConstraint (v, CosExpr vb)) = false
  | dc_no_func (DurationConstraint (v, ExpExpr vb)) = false
  | dc_no_func (DurationConstraint (v, PiExpr)) = false
  | dc_no_func (DurationConstraint (v, FunctionExpr vb)) = false;

fun comp_opt_ge A_ NONE NONE = true
  | comp_opt_ge A_ NONE (SOME x) = false
  | comp_opt_ge A_ (SOME x) NONE = true
  | comp_opt_ge A_ (SOME x) (SOME y) =
    less_eq ((ord_preorder o preorder_order o order_linorder) A_) y x;

fun max_lb_opt A_ [] l = l
  | max_lb_opt A_ (x :: xs) l =
    max_lb_opt A_ xs
      (if comp_opt_ge (linorder_lower_bound A_) x l then x else l);

fun comp_opt_le A_ NONE NONE = true
  | comp_opt_le A_ NONE (SOME x) = false
  | comp_opt_le A_ (SOME x) NONE = true
  | comp_opt_le A_ (SOME x) (SOME y) =
    less_eq ((ord_preorder o preorder_order o order_linorder) A_) x y;

fun min_ub_opt A_ [] u = u
  | min_ub_opt A_ (x :: xs) u =
    min_ub_opt A_ xs
      (if comp_opt_le (linorder_upper_bound A_) x u then x else u);

fun prepend_err_msg A_ msg e =
  (fn _ =>
    shows_prec A_ zero_nata msg o
      shows_prec_list show_char zero_nata
        [Chara (false, true, false, true, true, true, false, false),
          Chara (false, false, false, false, false, true, false, false)] o
      e ());

fun wf_type ty_decl (Either ts) =
  less_eq_set (cenum_literal, ceq_literal, ccompare_literal)
    (set (ceq_literal, ccompare_literal, set_impl_literal) ts)
    (insert (ceq_literal, ccompare_literal) "object"
      (image
        (ceq_prod ceq_literal ceq_literal,
          ccompare_prod ccompare_literal ccompare_literal)
        (ceq_literal, ccompare_literal, set_impl_literal) fst
        (set (ceq_prod ceq_literal ceq_literal,
               ccompare_prod ccompare_literal ccompare_literal,
               set_impl_prod set_impl_literal set_impl_literal)
          ty_decl)));

fun app_snap at_start at_end f (AtStart a) = f (at_start a)
  | app_snap at_start at_end f (AtEnd a) = f (at_end a);

fun nameb (ActionHead (x1, x2)) = x1;

fun functions (Domain (x1, x2, x3, x4, x5)) = x3;

fun to_literals (Atom (PredAtm (x, asa))) = [Atom (PredAtm (x, asa))]
  | to_literals (And (x, y)) = to_literals x @ to_literals y
  | to_literals (Atom (EqAtm (va, vb))) = []
  | to_literals (Atom (NumericEqAtm (va, vb))) = []
  | to_literals (Atom (NumericLessAtm (va, vb))) = []
  | to_literals (Atom (NumericLEAtm (va, vb))) = []
  | to_literals (Atom (NumericGreaterAtm (va, vb))) = []
  | to_literals (Atom (NumericGEAtm (va, vb))) = []
  | to_literals Bot = []
  | to_literals (Not v) = []
  | to_literals (Or (v, va)) = []
  | to_literals (Imp (v, va)) = [];

fun floor_rat p = let
                    val (a, b) = quotient_of p;
                  in
                    divide_int a b
                  end;

fun siga predicates =
  map_of equal_predicate (map (fn PredDecl (a, b) => (a, b)) predicates);

fun predicates (Domain (x1, x2, x3, x4, x5)) = x2;

fun act_pres_pos (SimpleActionSchemaa (h, SimpleActionBody (pre, eff))) =
  is_pos_conj pre
  | act_pres_pos (DurativeActionSchema (h, DurativeActionBody (dc, cond, deff)))
    = list_all is_pos_conj (map snd cond);

fun atom_no_args (PredAtm (p, [])) = true
  | atom_no_args (PredAtm (v, vb :: vc)) = false
  | atom_no_args (EqAtm (v, va)) = false
  | atom_no_args (NumericEqAtm (v, va)) = false
  | atom_no_args (NumericLessAtm (v, va)) = false
  | atom_no_args (NumericLEAtm (v, va)) = false
  | atom_no_args (NumericGreaterAtm (v, va)) = false
  | atom_no_args (NumericGEAtm (v, va)) = false;

fun pred_no_args (PredDecl (p, asa)) = null asa;

fun to_predicate (Atom (PredAtm (x, uu))) = x;

fun dfs_map_impl_0 A_ (B1_, B2_, B3_) succsi lei keyi copyi x =
  let
    val (a1, (a1a, a2a)) = x;
  in
    (fn f_ => fn () => f_ ((keyi a2a) ()) ())
      (fn xa =>
        (fn f_ => fn () => f_
          ((hms_extract (ht_lookup (B1_, B2_, B3_) (heap_list A_))
             (ht_delete (B1_, B2_, B3_) (heap_list A_)) xa a1a)
          ()) ())
          (fn xaa =>
            (fn f_ => fn () => f_
              ((case xaa of (NONE, a2b) => (fn () => (a2b, false))
                 | (SOME x_c, a2b) =>
                   (fn f_ => fn () => f_
                     ((imp_nfoldli x_c (fn sigma => (fn () => (not sigma)))
                        (fn xf => fn sigma =>
                          (fn f_ => fn () => f_ ((lei xf a2a) ()) ())
                            (fn x_f => (fn () => (x_f orelse sigma))))
                        false)
                     ()) ())
                     (fn x_d =>
                       (fn f_ => fn () => f_
                         ((ht_update (B1_, B2_, B3_) (heap_list A_) xa x_c a2b)
                         ()) ())
                         (fn x_e => (fn () => (x_e, x_d)))))
              ()) ())
              (fn a =>
                (case a of (a1b, true) => (fn () => (a1, (a1b, true)))
                  | (a1b, false) =>
                    (fn f_ => fn () => f_ ((keyi a2a) ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_
                          ((hms_extract
                             (ht_lookup (B1_, B2_, B3_) (heap_list A_))
                             (ht_delete (B1_, B2_, B3_) (heap_list A_)) xb a1)
                          ()) ())
                          (fn xab =>
                            (fn f_ => fn () => f_
                              ((case xab
                                 of (NONE, a2c) => (fn () => (a2c, false))
                                 | (SOME x_e, a2c) =>
                                   (fn f_ => fn () => f_
                                     ((lso_bex_impl (lei a2a) x_e) ()) ())
                                     (fn x_f =>
                                       (fn f_ => fn () => f_
 ((ht_update (B1_, B2_, B3_) (heap_list A_) xb x_e a2c) ()) ())
 (fn x_g => (fn () => (x_g, x_f)))))
                              ()) ())
                              (fn aa =>
                                (case aa
                                  of (a1c, true) =>
                                    (fn () => (a1c, (a1b, false)))
                                  | (a1c, false) =>
                                    (fn f_ => fn () => f_ ((copyi a2a) ()) ())
                                      (fn xc =>
(fn f_ => fn () => f_ ((keyi xc) ()) ())
  (fn xd =>
    (fn f_ => fn () => f_
      ((hms_extract (ht_lookup (B1_, B2_, B3_) (heap_list A_))
         (ht_delete (B1_, B2_, B3_) (heap_list A_)) xd a1b)
      ()) ())
      (fn xac =>
        (fn f_ => fn () => f_
          ((case xac
             of (NONE, a2d) =>
               (fn f_ => fn () => f_ ((copyi a2a) ()) ())
                 (fn xad =>
                   (fn f_ => fn () => f_
                     ((ht_update (B1_, B2_, B3_) (heap_list A_) xd
                        (op_list_prepend xad []) a2d)
                     ()) ())
                     (fn x_h => (fn () => ((), x_h))))
             | (SOME x_g, a2d) =>
               (fn f_ => fn () => f_ ((copyi a2a) ()) ())
                 (fn xad =>
                   (fn f_ => fn () => f_
                     ((ht_update (B1_, B2_, B3_) (heap_list A_) xd
                        (op_list_prepend xad x_g) a2d)
                     ()) ())
                     (fn x_i => (fn () => ((), x_i)))))
          ()) ())
          (fn (_, a2d) =>
            (fn f_ => fn () => f_ ((succsi a2a) ()) ())
              (fn xe =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli xe (fn (_, (_, b)) => (fn () => (not b)))
                     (fn xk => fn (a1e, (a1f, _)) =>
                       dfs_map_impl_0 A_ (B1_, B2_, B3_) succsi lei keyi copyi
                         (a1e, (a1f, xk)))
                     (a1c, (a2d, false)))
                  ()) ())
                  (fn (a1e, (a1f, a2f)) =>
                    (fn f_ => fn () => f_ ((copyi a2a) ()) ())
                      (fn xf =>
                        (fn f_ => fn () => f_ ((keyi xf) ()) ())
                          (fn xg =>
                            (fn f_ => fn () => f_
                              ((hms_extract
                                 (ht_lookup (B1_, B2_, B3_) (heap_list A_))
                                 (ht_delete (B1_, B2_, B3_) (heap_list A_)) xg
                                 a1f)
                              ()) ())
                              (fn xad =>
                                (fn f_ => fn () => f_
                                  ((case xad
                                     of (NONE, a2g) =>
                                       (fn f_ => fn () => f_
 ((ht_update (B1_, B2_, B3_) (heap_list A_) xg [] a2g) ()) ())
 (fn x_k => (fn () => ((), x_k)))
                                     | (SOME x_j, a2g) =>
                                       (fn f_ => fn () => f_
 ((ht_update (B1_, B2_, B3_) (heap_list A_) xg
    (if op_list_is_empty x_j then [] else op_list_tl x_j) a2g)
 ()) ())
 (fn x_l => (fn () => ((), x_l))))
                                  ()) ())
                                  (fn (_, a2g) =>
                                    (fn f_ => fn () => f_ ((copyi a2a) ()) ())
                                      (fn xh =>
(fn f_ => fn () => f_ ((keyi xh) ()) ())
  (fn xi =>
    (fn f_ => fn () => f_
      ((hms_extract (ht_lookup (B1_, B2_, B3_) (heap_list A_))
         (ht_delete (B1_, B2_, B3_) (heap_list A_)) xi a1e)
      ()) ())
      (fn xae =>
        (fn f_ => fn () => f_
          ((case xae
             of (NONE, a2h) =>
               (fn f_ => fn () => f_ ((copyi a2a) ()) ())
                 (fn xaf =>
                   (fn f_ => fn () => f_
                     ((ht_update (B1_, B2_, B3_) (heap_list A_) xi [xaf] a2h)
                     ()) ())
                     (fn x_m => (fn () => ((), x_m))))
             | (SOME x_l, a2h) =>
               (fn f_ => fn () => f_ ((copyi a2a) ()) ())
                 (fn xaf =>
                   (fn f_ => fn () => f_
                     ((ht_update (B1_, B2_, B3_) (heap_list A_) xi (xaf :: x_l)
                        a2h)
                     ()) ())
                     (fn x_n => (fn () => ((), x_n)))))
          ()) ())
          (fn (_, a2h) =>
            (fn f_ => fn () => f_ (tRACE_impl ()) ())
              (fn _ => (fn () => (a2h, (a2g, a2f))))))))))))))))))))))))))
  end;

fun heada (SimpleActionSchemaa (x11, x12)) = x11
  | heada (DurativeActionSchema (x21, x22)) = x21;

fun temporal_to_continuous_action_body (DurativeActionBody (d, c, e)) =
  ContChangeActionBody (d, c, e, []);

fun temporal_to_continuous_action_schema (SimpleActionSchemaa (h, b)) =
  SimpleActionSchema (h, b)
  | temporal_to_continuous_action_schema (DurativeActionSchema (h, b)) =
    ContChangeActionSchema (h, temporal_to_continuous_action_body b);

fun map_ast_domain f (Domain (x1, x2, x3, x4, x5)) =
  Domain (x1, x2, x3, x4, map f x5);

fun map_ast_problem f (Problem (x1, x2, x3, x4)) =
  Problem (map_ast_domain f x1, x2, x3, x4);

fun temporal_to_continuous_problem x =
  map_ast_problem temporal_to_continuous_action_schema x;

fun is_of_type ty_ent stg v t =
  (case ty_ent v of NONE => false | SOME vT => of_type_impl stg vT t);

fun func_sig functions =
  map_of equal_func (map (fn FuncDecl (a, b) => (a, b)) functions);

fun wf_func_args d ty_ent stg (f, args) =
  (case func_sig (functions d) f of NONE => false
    | SOME a => list_all2 (is_of_type ty_ent stg) args a);

fun wf_func_assign p ot stg
  (Atom (NumericEqAtm (FunctionExpr (PNE (f, args)), ConstantExpr r))) =
  wf_func_args (domain p) (lookupa (ccompare_object, equal_object) ot) stg
    (f, args)
  | wf_func_assign p ot stg (Atom (PredAtm (va, vb))) = false
  | wf_func_assign p ot stg (Atom (EqAtm (va, vb))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (ConstantExpr vc, vb))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (DurationExpr, vb))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (AddExpr (vc, vd), vb))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (SubExpr (vc, vd), vb))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (MulExpr (vc, vd), vb))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (DivExpr (vc, vd), vb))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (SinExpr vc, vb))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (CosExpr vc, vb))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (ExpExpr vc, vb))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (PiExpr, vb))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (va, DurationExpr))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (va, AddExpr (vc, vd)))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (va, SubExpr (vc, vd)))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (va, MulExpr (vc, vd)))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (va, DivExpr (vc, vd)))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (va, SinExpr vc))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (va, CosExpr vc))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (va, ExpExpr vc))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (va, PiExpr))) = false
  | wf_func_assign p ot stg (Atom (NumericEqAtm (va, FunctionExpr vc))) = false
  | wf_func_assign p ot stg (Atom (NumericLessAtm (va, vb))) = false
  | wf_func_assign p ot stg (Atom (NumericLEAtm (va, vb))) = false
  | wf_func_assign p ot stg (Atom (NumericGreaterAtm (va, vb))) = false
  | wf_func_assign p ot stg (Atom (NumericGEAtm (va, vb))) = false
  | wf_func_assign p ot stg Bot = false
  | wf_func_assign p ot stg (Not v) = false
  | wf_func_assign p ot stg (And (v, va)) = false
  | wf_func_assign p ot stg (Or (v, va)) = false
  | wf_func_assign p ot stg (Imp (v, va)) = false;

fun wf_pred_atom d ty_ent stg (p, vs) =
  (case siga (predicates d) p of NONE => false
    | SOME a => list_all2 (is_of_type ty_ent stg) vs a);

fun wf_fact p ot stg =
  wf_pred_atom (domain p) (lookupa (ccompare_object, equal_object) ot) stg;

fun wf_fmla_atom2 p mp stg f =
  (case f of Atom (PredAtm (pa, vs)) => wf_fact p mp stg (pa, vs)
    | Atom (EqAtm (_, _)) => false | Atom (NumericEqAtm (_, _)) => false
    | Atom (NumericLessAtm (_, _)) => false
    | Atom (NumericLEAtm (_, _)) => false
    | Atom (NumericGreaterAtm (_, _)) => false
    | Atom (NumericGEAtm (_, _)) => false | Bot => false | Not _ => false
    | And (_, _) => false | Or (_, _) => false | Imp (_, _) => false);

fun mp_constT d =
  of_alist (ccompare_object, equal_object, mapping_impl_object) (consts d);

fun mp_objT p =
  of_alist (ccompare_object, equal_object, mapping_impl_object)
    (consts (domain p) @ objects p);

fun wf_primitive_numeric_expression d ty_ent stg (PNE (f, args)) =
  wf_func_args d ty_ent stg (f, args);

fun wf_numeric_expression d ty_ent stg (ConstantExpr uu) = true
  | wf_numeric_expression d ty_ent stg DurationExpr = true
  | wf_numeric_expression d ty_ent stg (AddExpr (x, y)) =
    wf_numeric_expression d ty_ent stg x andalso
      wf_numeric_expression d ty_ent stg y
  | wf_numeric_expression d ty_ent stg (SubExpr (x, y)) =
    wf_numeric_expression d ty_ent stg x andalso
      wf_numeric_expression d ty_ent stg y
  | wf_numeric_expression d ty_ent stg (MulExpr (x, y)) =
    wf_numeric_expression d ty_ent stg x andalso
      wf_numeric_expression d ty_ent stg y
  | wf_numeric_expression d ty_ent stg (DivExpr (x, y)) =
    wf_numeric_expression d ty_ent stg x andalso
      wf_numeric_expression d ty_ent stg y
  | wf_numeric_expression d ty_ent stg (SinExpr x) =
    wf_numeric_expression d ty_ent stg x
  | wf_numeric_expression d ty_ent stg (CosExpr x) =
    wf_numeric_expression d ty_ent stg x
  | wf_numeric_expression d ty_ent stg (ExpExpr x) =
    wf_numeric_expression d ty_ent stg x
  | wf_numeric_expression d ty_ent stg PiExpr = true
  | wf_numeric_expression d ty_ent stg (FunctionExpr p) =
    wf_primitive_numeric_expression d ty_ent stg p;

fun wf_atom d ty_ent stg (PredAtm (p, vs)) = wf_pred_atom d ty_ent stg (p, vs)
  | wf_atom d ty_ent stg (EqAtm (a, b)) =
    not (is_none (ty_ent a)) andalso not (is_none (ty_ent b))
  | wf_atom d ty_ent stg (NumericEqAtm (a, b)) =
    wf_numeric_expression d ty_ent stg a andalso
      wf_numeric_expression d ty_ent stg b
  | wf_atom d ty_ent stg (NumericLessAtm (a, b)) =
    wf_numeric_expression d ty_ent stg a andalso
      wf_numeric_expression d ty_ent stg b
  | wf_atom d ty_ent stg (NumericLEAtm (a, b)) =
    wf_numeric_expression d ty_ent stg a andalso
      wf_numeric_expression d ty_ent stg b
  | wf_atom d ty_ent stg (NumericGreaterAtm (a, b)) =
    wf_numeric_expression d ty_ent stg a andalso
      wf_numeric_expression d ty_ent stg b
  | wf_atom d ty_ent stg (NumericGEAtm (a, b)) =
    wf_numeric_expression d ty_ent stg a andalso
      wf_numeric_expression d ty_ent stg b;

fun wf_fmla d ty_ent stg (Atom a) = wf_atom d ty_ent stg a
  | wf_fmla d ty_ent stg Bot = true
  | wf_fmla d ty_ent stg (And (phi_1, phi_2)) =
    wf_fmla d ty_ent stg phi_1 andalso wf_fmla d ty_ent stg phi_2
  | wf_fmla d ty_ent stg (Or (phi_1, phi_2)) =
    wf_fmla d ty_ent stg phi_1 andalso wf_fmla d ty_ent stg phi_2
  | wf_fmla d ty_ent stg (Imp (phi_1, phi_2)) =
    wf_fmla d ty_ent stg phi_1 andalso wf_fmla d ty_ent stg phi_2
  | wf_fmla d ty_ent stg (Not phi) = wf_fmla d ty_ent stg phi;

fun wf_continuous_effect d ty_ent stg (ContinuousEffect (cop, l, r)) =
  wf_primitive_numeric_expression d ty_ent stg l andalso
    wf_numeric_expression d ty_ent stg r;

fun wf_duration_const d ty_ent stg (DurationConstraint (operator, r)) =
  wf_numeric_expression d ty_ent stg r;

fun wf_numeric_effect d ty_ent stg (NumericEffect (uu, l, r)) =
  wf_primitive_numeric_expression d ty_ent stg l andalso
    wf_numeric_expression d ty_ent stg r;

fun wf_fmla_atom1 d ty_ent stg (Atom (PredAtm (p, vs))) =
  wf_pred_atom d ty_ent stg (p, vs)
  | wf_fmla_atom1 d ty_ent stg (Atom (EqAtm (va, vb))) = false
  | wf_fmla_atom1 d ty_ent stg (Atom (NumericEqAtm (va, vb))) = false
  | wf_fmla_atom1 d ty_ent stg (Atom (NumericLessAtm (va, vb))) = false
  | wf_fmla_atom1 d ty_ent stg (Atom (NumericLEAtm (va, vb))) = false
  | wf_fmla_atom1 d ty_ent stg (Atom (NumericGreaterAtm (va, vb))) = false
  | wf_fmla_atom1 d ty_ent stg (Atom (NumericGEAtm (va, vb))) = false
  | wf_fmla_atom1 d ty_ent stg Bot = false
  | wf_fmla_atom1 d ty_ent stg (Not v) = false
  | wf_fmla_atom1 d ty_ent stg (And (v, va)) = false
  | wf_fmla_atom1 d ty_ent stg (Or (v, va)) = false
  | wf_fmla_atom1 d ty_ent stg (Imp (v, va)) = false;

fun wf_effect da ty_ent stg (Effect (a, d, nes)) =
  list_all (wf_fmla_atom1 da ty_ent stg) a andalso
    (list_all (wf_fmla_atom1 da ty_ent stg) d andalso
      list_all (wf_numeric_effect da ty_ent stg) nes);

fun wf_cont_action_schema d stg conT
  (SimpleActionSchema (ActionHead (n, params), SimpleActionBody (pre, eff))) =
  let
    val tyv = ty_term (map_of equal_variable params) conT;
  in
    distinct_ds (equal_variable, linorder_variable) (map fst params) andalso
      (wf_fmla d tyv stg pre andalso wf_effect d tyv stg eff)
  end
  | wf_cont_action_schema da stg conT
    (ContChangeActionSchema
      (ActionHead (n, params), ContChangeActionBody (d, cond, eff, cont_eff)))
    = let
        val tyv = ty_term (map_of equal_variable params) conT;
      in
        distinct_ds (equal_variable, linorder_variable) (map fst params) andalso
          (list_all (fn (_, a) => wf_fmla da tyv stg a) cond andalso
            (list_all
               (fn (t, e) =>
                 wf_effect da tyv stg e andalso
                   not (equal_temporal_annotationa t Over_All))
               eff andalso
              (list_all (wf_continuous_effect da tyv stg) cont_eff andalso
                list_all
                  (fn (t, c) =>
                    (equal_temporal_annotationa t At_Start orelse
                      equal_temporal_annotationa t At_End) andalso
                      wf_duration_const da tyv stg c)
                  d)))
      end;

fun wf_predicate_decl ty_decl (PredDecl (p, ts)) =
  list_all (wf_type ty_decl) ts;

fun wf_function_decl ty_decl (FuncDecl (f, ts)) = list_all (wf_type ty_decl) ts;

fun head (SimpleActionSchema (x11, x12)) = x11
  | head (ContChangeActionSchema (x21, x22)) = x21;

fun check_wf_cont_domain d stg conT =
  bind (check_wf_types d)
    (fn _ =>
      bind (check
             (distinct_ds (equal_predicate, linorder_predicate)
               (map pred (predicates d)))
             (fn _ =>
               shows_prec_list show_char zero_nata
                 [Chara (false, false, true, false, false, false, true, false),
                   Chara (true, false, true, false, true, true, true, false),
                   Chara (false, false, false, false, true, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (true, false, false, true, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, true, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, false, false, true, true, true, false),
                   Chara (false, true, false, false, true, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, false, true, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, true, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, true, false, false, true, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, true, true, true, false),
                   Chara (true, false, false, true, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, true, true, true, false, true, true, false)]))
        (fn _ =>
          bind (check_all_list (show_list show_char)
                 (wf_predicate_decl (types d)) (predicates d)
                 [Chara (true, false, true, true, false, false, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (false, true, true, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, true, false, false, true, true, true, false),
                   Chara (true, false, true, true, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, false, false, true, true, true, false),
                   Chara (false, true, false, false, true, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, false, true, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, true, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, true, false, false, true, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, true, true, true, false),
                   Chara (true, false, false, true, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, true, true, true, false, true, true, false)]
                 (shows_prec_literal zero_nata o namea o pred))
            (fn _ =>
              bind (check
                     (distinct_ds (equal_func, linorder_func)
                       (map func (functions d)))
                     (fn _ =>
                       shows_prec_list show_char zero_nata
                         [Chara (false, false, true, false, false, false, true,
                                  false),
                           Chara (true, false, true, false, true, true, true,
                                   false),
                           Chara (false, false, false, false, true, true, true,
                                   false),
                           Chara (false, false, true, true, false, true, true,
                                   false),
                           Chara (true, false, false, true, false, true, true,
                                   false),
                           Chara (true, true, false, false, false, true, true,
                                   false),
                           Chara (true, false, false, false, false, true, true,
                                   false),
                           Chara (false, false, true, false, true, true, true,
                                   false),
                           Chara (true, false, true, false, false, true, true,
                                   false),
                           Chara (false, false, false, false, false, true,
                                   false, false),
                           Chara (false, true, true, false, false, true, true,
                                   false),
                           Chara (true, false, true, false, true, true, true,
                                   false),
                           Chara (false, true, true, true, false, true, true,
                                   false),
                           Chara (true, true, false, false, false, true, true,
                                   false),
                           Chara (false, false, true, false, true, true, true,
                                   false),
                           Chara (true, false, false, true, false, true, true,
                                   false),
                           Chara (true, true, true, true, false, true, true,
                                   false),
                           Chara (false, true, true, true, false, true, true,
                                   false),
                           Chara (false, false, false, false, false, true,
                                   false, false),
                           Chara (false, false, true, false, false, true, true,
                                   false),
                           Chara (true, false, true, false, false, true, true,
                                   false),
                           Chara (true, true, false, false, false, true, true,
                                   false),
                           Chara (false, false, true, true, false, true, true,
                                   false),
                           Chara (true, false, false, false, false, true, true,
                                   false),
                           Chara (false, true, false, false, true, true, true,
                                   false),
                           Chara (true, false, false, false, false, true, true,
                                   false),
                           Chara (false, false, true, false, true, true, true,
                                   false),
                           Chara (true, false, false, true, false, true, true,
                                   false),
                           Chara (true, true, true, true, false, true, true,
                                   false),
                           Chara (false, true, true, true, false, true, true,
                                   false)]))
                (fn _ =>
                  bind (check_all_list (show_list show_char)
                         (wf_function_decl (types d)) (functions d)
                         [Chara (true, false, true, true, false, false, true,
                                  false),
                           Chara (true, false, false, false, false, true, true,
                                   false),
                           Chara (false, false, true, true, false, true, true,
                                   false),
                           Chara (false, true, true, false, false, true, true,
                                   false),
                           Chara (true, true, true, true, false, true, true,
                                   false),
                           Chara (false, true, false, false, true, true, true,
                                   false),
                           Chara (true, false, true, true, false, true, true,
                                   false),
                           Chara (true, false, true, false, false, true, true,
                                   false),
                           Chara (false, false, true, false, false, true, true,
                                   false),
                           Chara (false, false, false, false, false, true,
                                   false, false),
                           Chara (false, true, true, false, false, true, true,
                                   false),
                           Chara (true, false, true, false, true, true, true,
                                   false),
                           Chara (false, true, true, true, false, true, true,
                                   false),
                           Chara (true, true, false, false, false, true, true,
                                   false),
                           Chara (false, false, true, false, true, true, true,
                                   false),
                           Chara (true, false, false, true, false, true, true,
                                   false),
                           Chara (true, true, true, true, false, true, true,
                                   false),
                           Chara (false, true, true, true, false, true, true,
                                   false),
                           Chara (false, false, false, false, false, true,
                                   false, false),
                           Chara (false, false, true, false, false, true, true,
                                   false),
                           Chara (true, false, true, false, false, true, true,
                                   false),
                           Chara (true, true, false, false, false, true, true,
                                   false),
                           Chara (false, false, true, true, false, true, true,
                                   false),
                           Chara (true, false, false, false, false, true, true,
                                   false),
                           Chara (false, true, false, false, true, true, true,
                                   false),
                           Chara (true, false, false, false, false, true, true,
                                   false),
                           Chara (false, false, true, false, true, true, true,
                                   false),
                           Chara (true, false, false, true, false, true, true,
                                   false),
                           Chara (true, true, true, true, false, true, true,
                                   false),
                           Chara (false, true, true, true, false, true, true,
                                   false)]
                         (shows_prec_literal zero_nata o name o func))
                    (fn _ =>
                      bind (check
                             (distinct_ds (equal_object, linorder_object)
                               (map fst (consts d)))
                             (fn _ =>
                               shows_prec_list show_char zero_nata
                                 [Chara (false, false, true, false, false,
  false, true, false),
                                   Chara (true, false, true, false, true, true,
   true, false),
                                   Chara (false, false, false, false, true,
   true, true, false),
                                   Chara (false, false, true, true, false, true,
   true, false),
                                   Chara (true, false, false, true, false, true,
   true, false),
                                   Chara (true, true, false, false, false, true,
   true, false),
                                   Chara (true, false, false, false, false,
   true, true, false),
                                   Chara (false, false, true, false, true, true,
   true, false),
                                   Chara (true, false, true, false, false, true,
   true, false),
                                   Chara (false, false, false, false, false,
   true, false, false),
                                   Chara (true, true, false, false, false, true,
   true, false),
                                   Chara (true, true, true, true, false, true,
   true, false),
                                   Chara (false, true, true, true, false, true,
   true, false),
                                   Chara (true, true, false, false, true, true,
   true, false),
                                   Chara (false, false, true, false, true, true,
   true, false),
                                   Chara (true, false, false, false, false,
   true, true, false),
                                   Chara (false, true, true, true, false, true,
   true, false),
                                   Chara (false, false, true, false, true, true,
   true, false),
                                   Chara (false, false, false, false, false,
   true, false, false),
                                   Chara (false, false, true, false, false,
   true, true, false),
                                   Chara (true, false, true, false, false, true,
   true, false),
                                   Chara (true, true, false, false, false, true,
   true, false),
                                   Chara (false, false, true, true, false, true,
   true, false),
                                   Chara (true, false, false, false, false,
   true, true, false),
                                   Chara (false, true, false, false, true, true,
   true, false),
                                   Chara (true, false, false, false, false,
   true, true, false),
                                   Chara (false, false, true, false, true, true,
   true, false),
                                   Chara (true, false, false, true, false, true,
   true, false),
                                   Chara (true, true, true, true, false, true,
   true, false),
                                   Chara (false, true, true, true, false, true,
   true, false)]))
                        (fn _ =>
                          bind (check
                                 (list_all (fn (_, a) => wf_type (types d) a)
                                   (consts d))
                                 (fn _ =>
                                   shows_prec_list show_char zero_nata
                                     [Chara
(true, false, true, true, false, false, true, false),
                                       Chara
 (true, false, false, false, false, true, true, false),
                                       Chara
 (false, false, true, true, false, true, true, false),
                                       Chara
 (false, true, true, false, false, true, true, false),
                                       Chara
 (true, true, true, true, false, true, true, false),
                                       Chara
 (false, true, false, false, true, true, true, false),
                                       Chara
 (true, false, true, true, false, true, true, false),
                                       Chara
 (true, false, true, false, false, true, true, false),
                                       Chara
 (false, false, true, false, false, true, true, false),
                                       Chara
 (false, false, false, false, false, true, false, false),
                                       Chara
 (false, false, true, false, true, true, true, false),
                                       Chara
 (true, false, false, true, true, true, true, false),
                                       Chara
 (false, false, false, false, true, true, true, false),
                                       Chara
 (true, false, true, false, false, true, true, false)]))
                            (fn _ =>
                              bind (check
                                     (distinct_ds
                                       (equal_literal, linorder_literal)
                                       (map (fn a => nameb (head a))
 (actions d)))
                                     (fn _ =>
                                       shows_prec_list show_char zero_nata
 [Chara (false, false, true, false, false, false, true, false),
   Chara (true, false, true, false, true, true, true, false),
   Chara (false, false, false, false, true, true, true, false),
   Chara (false, false, true, true, false, true, true, false),
   Chara (true, false, false, true, false, true, true, false),
   Chara (true, true, false, false, false, true, true, false),
   Chara (true, false, false, false, false, true, true, false),
   Chara (false, false, true, false, true, true, true, false),
   Chara (true, false, true, false, false, true, true, false),
   Chara (false, false, false, false, false, true, false, false),
   Chara (true, false, false, false, false, true, true, false),
   Chara (true, true, false, false, false, true, true, false),
   Chara (false, false, true, false, true, true, true, false),
   Chara (true, false, false, true, false, true, true, false),
   Chara (true, true, true, true, false, true, true, false),
   Chara (false, true, true, true, false, true, true, false),
   Chara (false, false, false, false, false, true, false, false),
   Chara (false, true, true, true, false, true, true, false),
   Chara (true, false, false, false, false, true, true, false),
   Chara (true, false, true, true, false, true, true, false),
   Chara (true, false, true, false, false, true, true, false)]))
                                (fn _ =>
                                  check_all_list (show_list show_char)
                                    (wf_cont_action_schema d stg conT)
                                    (actions d)
                                    [Chara (true, false, true, true, false,
     false, true, false),
                                      Chara
(true, false, false, false, false, true, true, false),
                                      Chara
(false, false, true, true, false, true, true, false),
                                      Chara
(false, true, true, false, false, true, true, false),
                                      Chara
(true, true, true, true, false, true, true, false),
                                      Chara
(false, true, false, false, true, true, true, false),
                                      Chara
(true, false, true, true, false, true, true, false),
                                      Chara
(true, false, true, false, false, true, true, false),
                                      Chara
(false, false, true, false, false, true, true, false),
                                      Chara
(false, false, false, false, false, true, false, false),
                                      Chara
(true, false, false, false, false, true, true, false),
                                      Chara
(true, true, false, false, false, true, true, false),
                                      Chara
(false, false, true, false, true, true, true, false),
                                      Chara
(true, false, false, true, false, true, true, false),
                                      Chara
(true, true, true, true, false, true, true, false),
                                      Chara
(false, true, true, true, false, true, true, false)]
                                    (shows_prec_literal zero_nata o
                                      (fn a => nameb (head a)))))))))));

fun subtype_edge (ty, superty) = (superty, ty);

fun stg d =
  tab_succ (ccompare_literal, equal_literal, mapping_impl_literal)
    (map subtype_edge (types d));

fun check_wf_cont_problem p =
  let
    val d = domain p;
    val stga = stg (domain p);
    val conT = mp_constT (domain p);
    val mp = mp_objT p;
  in
    bind (catch_error (check_wf_cont_domain d stga conT)
           (fn x =>
             Inl (prepend_err_msg (show_list show_char)
                   [Chara (false, false, true, false, false, false, true,
                            false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (true, false, true, true, false, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, true, true, false, true, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, true, true, false, true, true, false),
                     Chara (false, false, true, true, false, true, true, false),
                     Chara (true, false, true, true, false, true, false, false),
                     Chara (false, true, true, false, false, true, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, false, true, true, false, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, true, false, false, true, true,
                             false)]
                   x)))
      (fn _ =>
        bind (check
               (distinct_ds (equal_object, linorder_object)
                 (map fst (objects p) @ map fst (consts d)))
               (fn _ =>
                 shows_prec_list show_char zero_nata
                   [Chara (false, false, true, false, false, false, true,
                            false),
                     Chara (true, false, true, false, true, true, true, false),
                     Chara (false, false, false, false, true, true, true,
                             false),
                     Chara (false, false, true, true, false, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (true, true, false, false, false, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, true, false, false, false, true, true,
                             false),
                     Chara (false, true, false, true, false, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (true, true, false, false, false, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (false, false, true, false, false, true, true,
                             false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (true, true, false, false, false, true, true, false),
                     Chara (false, false, true, true, false, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, true,
                             false)]))
          (fn _ =>
            bind (check
                   (list_all (fn (_, a) => wf_type (types d) a) (objects p))
                   (fn _ =>
                     shows_prec_list show_char zero_nata
                       [Chara (true, false, true, true, false, false, true,
                                false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (false, false, true, true, false, true, true,
                                 false),
                         Chara (false, true, true, false, false, true, true,
                                 false),
                         Chara (true, true, true, true, false, true, true,
                                 false),
                         Chara (false, true, false, false, true, true, true,
                                 false),
                         Chara (true, false, true, true, false, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (false, false, true, false, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (false, false, true, false, true, true, true,
                                 false),
                         Chara (true, false, false, true, true, true, true,
                                 false),
                         Chara (false, false, false, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false)]))
              (fn _ =>
                bind (check
                       (distinct_ds
                         (equal_formula (equal_atom equal_object),
                           linorder_formula
                             (equal_atom equal_object,
                               linorder_atom (equal_object, linorder_object)))
                         (inita p))
                       (fn _ =>
                         shows_prec_list show_char zero_nata
                           [Chara (false, false, true, false, false, false,
                                    true, false),
                             Chara (true, false, true, false, true, true, true,
                                     false),
                             Chara (false, false, false, false, true, true,
                                     true, false),
                             Chara (false, false, true, true, false, true, true,
                                     false),
                             Chara (true, false, false, true, false, true, true,
                                     false),
                             Chara (true, true, false, false, false, true, true,
                                     false),
                             Chara (true, false, false, false, false, true,
                                     true, false),
                             Chara (false, false, true, false, true, true, true,
                                     false),
                             Chara (true, false, true, false, false, true, true,
                                     false),
                             Chara (false, false, false, false, false, true,
                                     false, false),
                             Chara (false, true, true, false, false, true, true,
                                     false),
                             Chara (true, false, false, false, false, true,
                                     true, false),
                             Chara (true, true, false, false, false, true, true,
                                     false),
                             Chara (false, false, true, false, true, true, true,
                                     false),
                             Chara (false, false, false, false, false, true,
                                     false, false),
                             Chara (true, false, false, true, false, true, true,
                                     false),
                             Chara (false, true, true, true, false, true, true,
                                     false),
                             Chara (false, false, false, false, false, true,
                                     false, false),
                             Chara (true, false, false, true, false, true, true,
                                     false),
                             Chara (false, true, true, true, false, true, true,
                                     false),
                             Chara (true, false, false, true, false, true, true,
                                     false),
                             Chara (false, false, true, false, true, true, true,
                                     false),
                             Chara (true, false, false, true, false, true, true,
                                     false),
                             Chara (true, false, false, false, false, true,
                                     true, false),
                             Chara (false, false, true, true, false, true, true,
                                     false),
                             Chara (false, false, false, false, false, true,
                                     false, false),
                             Chara (true, true, false, false, true, true, true,
                                     false),
                             Chara (false, false, true, false, true, true, true,
                                     false),
                             Chara (true, false, false, false, false, true,
                                     true, false),
                             Chara (false, false, true, false, true, true, true,
                                     false),
                             Chara (true, false, true, false, false, true, true,
                                     false)]))
                  (fn _ =>
                    bind (check
                           (list_all
                             (fn f =>
                               wf_fmla_atom2 p mp stga f orelse
                                 wf_func_assign p mp stga f)
                             (inita p))
                           (fn _ =>
                             shows_prec_list show_char zero_nata
                               [Chara (true, false, true, true, false, false,
true, false),
                                 Chara (true, false, false, false, false, true,
 true, false),
                                 Chara (false, false, true, true, false, true,
 true, false),
                                 Chara (false, true, true, false, false, true,
 true, false),
                                 Chara (true, true, true, true, false, true,
 true, false),
                                 Chara (false, true, false, false, true, true,
 true, false),
                                 Chara (true, false, true, true, false, true,
 true, false),
                                 Chara (true, false, true, false, false, true,
 true, false),
                                 Chara (false, false, true, false, false, true,
 true, false),
                                 Chara (false, false, false, false, false, true,
 false, false),
                                 Chara (false, true, true, false, false, true,
 true, false),
                                 Chara (true, true, true, true, false, true,
 true, false),
                                 Chara (false, true, false, false, true, true,
 true, false),
                                 Chara (true, false, true, true, false, true,
 true, false),
                                 Chara (true, false, true, false, true, true,
 true, false),
                                 Chara (false, false, true, true, false, true,
 true, false),
                                 Chara (true, false, false, false, false, true,
 true, false),
                                 Chara (false, false, false, false, false, true,
 false, false),
                                 Chara (true, false, false, true, false, true,
 true, false),
                                 Chara (false, true, true, true, false, true,
 true, false),
                                 Chara (false, false, false, false, false, true,
 false, false),
                                 Chara (true, false, false, true, false, true,
 true, false),
                                 Chara (false, true, true, true, false, true,
 true, false),
                                 Chara (true, false, false, true, false, true,
 true, false),
                                 Chara (false, false, true, false, true, true,
 true, false),
                                 Chara (true, false, false, true, false, true,
 true, false),
                                 Chara (true, false, false, false, false, true,
 true, false),
                                 Chara (false, false, true, true, false, true,
 true, false),
                                 Chara (false, false, false, false, false, true,
 false, false),
                                 Chara (true, true, false, false, true, true,
 true, false),
                                 Chara (false, false, true, false, true, true,
 true, false),
                                 Chara (true, false, false, false, false, true,
 true, false),
                                 Chara (false, false, true, false, true, true,
 true, false),
                                 Chara (true, false, true, false, false, true,
 true, false)]))
                      (fn _ =>
                        check (wf_fmla d
                                (lookupa (ccompare_object, equal_object) mp)
                                stga (goal p))
                          (fn _ =>
                            shows_prec_list show_char zero_nata
                              [Chara (true, false, true, true, false, false,
                                       true, false),
                                Chara (true, false, false, false, false, true,
true, false),
                                Chara (false, false, true, true, false, true,
true, false),
                                Chara (false, true, true, false, false, true,
true, false),
                                Chara (true, true, true, true, false, true,
true, false),
                                Chara (false, true, false, false, true, true,
true, false),
                                Chara (true, false, true, true, false, true,
true, false),
                                Chara (true, false, true, false, false, true,
true, false),
                                Chara (false, false, true, false, false, true,
true, false),
                                Chara (false, false, false, false, false, true,
false, false),
                                Chara (true, true, true, false, false, true,
true, false),
                                Chara (true, true, true, true, false, true,
true, false),
                                Chara (true, false, false, false, false, true,
true, false),
                                Chara (false, false, true, true, false, true,
true, false),
                                Chara (false, false, false, false, false, true,
false, false),
                                Chara (false, true, true, false, false, true,
true, false),
                                Chara (true, true, true, true, false, true,
true, false),
                                Chara (false, true, false, false, true, true,
true, false),
                                Chara (true, false, true, true, false, true,
true, false),
                                Chara (true, false, true, false, true, true,
true, false),
                                Chara (false, false, true, true, false, true,
true, false),
                                Chara (true, false, false, false, false, true,
true, false)]))))))
  end;

fun check_wf_temporal_problem p =
  check_wf_cont_problem (temporal_to_continuous_problem p);

fun form_preds_no_args (A1_, A2_) form =
  ball (ceq_atom A2_, ccompare_atom A1_)
    (atoms (ceq_atom A2_, ccompare_atom A1_, set_impl_atom) form) atom_no_args;

fun act_conds_no_args (SimpleActionSchemaa (h, SimpleActionBody (pre, eff))) =
  form_preds_no_args (ccompare_term, equal_term) pre
  | act_conds_no_args
    (DurativeActionSchema (h, DurativeActionBody (dc, cond, deff))) =
    list_all (form_preds_no_args (ccompare_term, equal_term)) (map snd cond);

fun duration_constraint_integer (DurationConstraint (dop, ConstantExpr x)) =
  is_integer x
  | duration_constraint_integer (DurationConstraint (v, DurationExpr)) = false
  | duration_constraint_integer (DurationConstraint (v, AddExpr (vb, vc))) =
    false
  | duration_constraint_integer (DurationConstraint (v, SubExpr (vb, vc))) =
    false
  | duration_constraint_integer (DurationConstraint (v, MulExpr (vb, vc))) =
    false
  | duration_constraint_integer (DurationConstraint (v, DivExpr (vb, vc))) =
    false
  | duration_constraint_integer (DurationConstraint (v, SinExpr vb)) = false
  | duration_constraint_integer (DurationConstraint (v, CosExpr vb)) = false
  | duration_constraint_integer (DurationConstraint (v, ExpExpr vb)) = false
  | duration_constraint_integer (DurationConstraint (v, PiExpr)) = false
  | duration_constraint_integer (DurationConstraint (v, FunctionExpr vb)) =
    false;

fun act_dcs_integers (SimpleActionSchemaa (h, b)) = true
  | act_dcs_integers
    (DurativeActionSchema (h, DurativeActionBody (dc, cond, deff))) =
    list_all duration_constraint_integer (map snd dc);

fun act_no_func_dcs (SimpleActionSchemaa (h, b)) = true
  | act_no_func_dcs
    (DurativeActionSchema (h, DurativeActionBody (dc, cond, deff))) =
    list_all dc_no_func (map snd dc);

fun act_no_params (SimpleActionSchemaa (h, b)) = null (parameters h)
  | act_no_params (DurativeActionSchema (h, b)) = null (parameters h);

fun check_ground_problem_core p =
  let
    val d = domain p;
  in
    bind (check_wf_temporal_problem p)
      (fn _ =>
        bind (check (is_pos_conj (goal p))
               (fn _ =>
                 shows_prec_list show_char zero_nata
                   [Chara (true, true, true, false, false, false, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, false, true, true, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, true, false, false, false, true, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, true, false, true, false, true, true, false),
                     Chara (true, false, true, false, true, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (true, true, false, false, false, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, true, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (false, false, false, false, true, true, true,
                             false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (true, true, false, false, true, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, true, true, false, true, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (false, false, true, true, false, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, false, true, true, false, true, true, false),
                     Chara (true, true, false, false, true, true, true,
                             false)]))
          (fn _ =>
            bind (check_all_list (show_list show_char) pred_no_args
                   (predicates d)
                   [Chara (false, false, false, false, true, false, true,
                            false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, true, false, false, true, true,
                             false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (true, true, false, false, false, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, true, true, false, false, true, true, false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (true, false, true, false, true, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, false, true, false, false, true, true,
                             false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, true, false, false, true, true,
                             false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (false, false, false, true, false, true, false,
                             false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, false, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, true, true, true, false, true, false, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (false, false, false, true, false, true, true,
                             false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (true, true, false, false, true, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, true, false, false, true, true, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (true, false, true, true, false, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, true, true, false, false, true, true, false),
                     Chara (true, false, true, false, true, true, true, false),
                     Chara (true, false, true, true, false, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (true, false, false, true, false, true, false,
                             false)]
                   (shows_prec_literal zero_nata o namea o pred))
              (fn _ =>
                bind (check_all_list (show_list show_char) act_no_params
                       (actions d)
                       [Chara (true, false, false, false, false, false, true,
                                false),
                         Chara (true, true, false, false, false, true, true,
                                 false),
                         Chara (false, false, true, false, true, true, true,
                                 false),
                         Chara (true, false, false, true, false, true, true,
                                 false),
                         Chara (true, true, true, true, false, true, true,
                                 false),
                         Chara (false, true, true, true, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (false, true, true, true, false, true, true,
                                 false),
                         Chara (true, true, true, true, false, true, true,
                                 false),
                         Chara (false, false, true, false, true, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (true, true, true, false, false, true, true,
                                 false),
                         Chara (false, true, false, false, true, true, true,
                                 false),
                         Chara (true, true, true, true, false, true, true,
                                 false),
                         Chara (true, false, true, false, true, true, true,
                                 false),
                         Chara (false, true, true, true, false, true, true,
                                 false),
                         Chara (false, false, true, false, false, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (false, false, true, false, false, true, true,
                                 false),
                         Chara (false, false, true, true, false, true, false,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (true, false, false, true, false, true, true,
                                 false),
                         Chara (false, false, true, false, true, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (false, false, false, true, false, true, true,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (true, true, false, false, true, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (true, true, true, true, false, true, false,
                                 false),
                         Chara (true, true, false, false, true, true, true,
                                 false),
                         Chara (true, true, true, true, false, true, true,
                                 false),
                         Chara (true, false, true, true, false, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (false, false, false, false, true, true, true,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (false, true, false, false, true, true, true,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (true, false, true, true, false, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (false, false, true, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (false, true, false, false, true, true, true,
                                 false),
                         Chara (false, false, false, true, false, true, false,
                                 false),
                         Chara (true, true, false, false, true, true, true,
                                 false),
                         Chara (true, false, false, true, false, true, false,
                                 false)]
                       (shows_prec_literal zero_nata o
                         (fn x => nameb (heada x))))
                  (fn _ =>
                    bind (check_all_list (show_list show_char) act_no_func_dcs
                           (actions d)
                           [Chara (true, false, false, false, false, false,
                                    true, false),
                             Chara (true, true, false, false, false, true, true,
                                     false),
                             Chara (false, false, true, false, true, true, true,
                                     false),
                             Chara (true, false, false, true, false, true, true,
                                     false),
                             Chara (true, true, true, true, false, true, true,
                                     false),
                             Chara (false, true, true, true, false, true, true,
                                     false),
                             Chara (false, false, false, false, false, true,
                                     false, false),
                             Chara (false, true, true, true, false, true, true,
                                     false),
                             Chara (true, true, true, true, false, true, true,
                                     false),
                             Chara (false, false, true, false, true, true, true,
                                     false),
                             Chara (false, false, false, false, false, true,
                                     false, false),
                             Chara (true, true, true, false, false, true, true,
                                     false),
                             Chara (false, true, false, false, true, true, true,
                                     false),
                             Chara (true, true, true, true, false, true, true,
                                     false),
                             Chara (true, false, true, false, true, true, true,
                                     false),
                             Chara (false, true, true, true, false, true, true,
                                     false),
                             Chara (false, false, true, false, false, true,
                                     true, false),
                             Chara (true, false, true, false, false, true, true,
                                     false),
                             Chara (false, false, true, false, false, true,
                                     true, false),
                             Chara (false, false, true, true, false, true,
                                     false, false),
                             Chara (false, false, false, false, false, true,
                                     false, false),
                             Chara (true, false, false, true, false, true, true,
                                     false),
                             Chara (false, false, true, false, true, true, true,
                                     false),
                             Chara (false, false, false, false, false, true,
                                     false, false),
                             Chara (false, false, false, true, false, true,
                                     true, false),
                             Chara (true, false, false, false, false, true,
                                     true, false),
                             Chara (true, true, false, false, true, true, true,
                                     false),
                             Chara (false, false, false, false, false, true,
                                     false, false),
                             Chara (true, false, false, false, false, true,
                                     true, false),
                             Chara (false, false, false, false, false, true,
                                     false, false),
                             Chara (false, true, true, false, false, true, true,
                                     false),
                             Chara (true, false, true, false, true, true, true,
                                     false),
                             Chara (false, true, true, true, false, true, true,
                                     false),
                             Chara (true, true, false, false, false, true, true,
                                     false),
                             Chara (false, false, true, false, true, true, true,
                                     false),
                             Chara (true, false, false, true, false, true, true,
                                     false),
                             Chara (true, true, true, true, false, true, true,
                                     false),
                             Chara (false, true, true, true, false, true, true,
                                     false),
                             Chara (true, false, false, false, false, true,
                                     true, false),
                             Chara (false, false, true, true, false, true, true,
                                     false),
                             Chara (false, false, false, false, false, true,
                                     false, false),
                             Chara (false, false, true, false, false, true,
                                     true, false),
                             Chara (true, false, true, false, true, true, true,
                                     false),
                             Chara (false, true, false, false, true, true, true,
                                     false),
                             Chara (true, false, false, false, false, true,
                                     true, false),
                             Chara (false, false, true, false, true, true, true,
                                     false),
                             Chara (true, false, false, true, false, true, true,
                                     false),
                             Chara (true, true, true, true, false, true, true,
                                     false),
                             Chara (false, true, true, true, false, true, true,
                                     false),
                             Chara (false, false, false, false, false, true,
                                     false, false),
                             Chara (true, true, false, false, false, true, true,
                                     false),
                             Chara (true, true, true, true, false, true, true,
                                     false),
                             Chara (false, true, true, true, false, true, true,
                                     false),
                             Chara (true, true, false, false, true, true, true,
                                     false),
                             Chara (false, false, true, false, true, true, true,
                                     false),
                             Chara (false, true, false, false, true, true, true,
                                     false),
                             Chara (true, false, false, false, false, true,
                                     true, false),
                             Chara (true, false, false, true, false, true, true,
                                     false),
                             Chara (false, true, true, true, false, true, true,
                                     false),
                             Chara (false, false, true, false, true, true, true,
                                     false)]
                           (shows_prec_literal zero_nata o
                             (fn x => nameb (heada x))))
                      (fn _ =>
                        bind (check_all_list (show_list show_char)
                               act_dcs_integers (actions d)
                               [Chara (true, false, false, false, false, false,
true, false),
                                 Chara (true, true, false, false, false, true,
 true, false),
                                 Chara (false, false, true, false, true, true,
 true, false),
                                 Chara (true, false, false, true, false, true,
 true, false),
                                 Chara (true, true, true, true, false, true,
 true, false),
                                 Chara (false, true, true, true, false, true,
 true, false),
                                 Chara (true, true, true, false, false, true,
 false, false),
                                 Chara (true, true, false, false, true, true,
 true, false),
                                 Chara (false, false, false, false, false, true,
 false, false),
                                 Chara (false, false, true, false, false, true,
 true, false),
                                 Chara (true, false, true, false, true, true,
 true, false),
                                 Chara (false, true, false, false, true, true,
 true, false),
                                 Chara (true, false, false, false, false, true,
 true, false),
                                 Chara (false, false, true, false, true, true,
 true, false),
                                 Chara (true, false, false, true, false, true,
 true, false),
                                 Chara (true, true, true, true, false, true,
 true, false),
                                 Chara (false, true, true, true, false, true,
 true, false),
                                 Chara (false, false, false, false, false, true,
 false, false),
                                 Chara (true, true, false, false, false, true,
 true, false),
                                 Chara (true, true, true, true, false, true,
 true, false),
                                 Chara (false, true, true, true, false, true,
 true, false),
                                 Chara (true, true, false, false, true, true,
 true, false),
                                 Chara (false, false, true, false, true, true,
 true, false),
                                 Chara (false, true, false, false, true, true,
 true, false),
                                 Chara (true, false, false, false, false, true,
 true, false),
                                 Chara (true, false, false, true, false, true,
 true, false),
                                 Chara (false, true, true, true, false, true,
 true, false),
                                 Chara (false, false, true, false, true, true,
 true, false),
                                 Chara (false, false, false, false, false, true,
 false, false),
                                 Chara (true, false, false, true, false, true,
 true, false),
                                 Chara (true, true, false, false, true, true,
 true, false),
                                 Chara (false, false, false, false, false, true,
 false, false),
                                 Chara (false, true, true, true, false, true,
 true, false),
                                 Chara (true, true, true, true, false, true,
 true, false),
                                 Chara (false, false, true, false, true, true,
 true, false),
                                 Chara (false, false, false, false, false, true,
 false, false),
                                 Chara (true, false, false, false, false, true,
 true, false),
                                 Chara (false, true, true, true, false, true,
 true, false),
                                 Chara (false, false, false, false, false, true,
 false, false),
                                 Chara (true, false, false, true, false, true,
 true, false),
                                 Chara (false, true, true, true, false, true,
 true, false),
                                 Chara (false, false, true, false, true, true,
 true, false),
                                 Chara (true, false, true, false, false, true,
 true, false),
                                 Chara (true, true, true, false, false, true,
 true, false),
                                 Chara (true, false, true, false, false, true,
 true, false),
                                 Chara (false, true, false, false, true, true,
 true, false)]
                               (shows_prec_literal zero_nata o
                                 (fn x => nameb (heada x))))
                          (fn _ =>
                            bind (check_all_list (show_list show_char)
                                   act_pres_pos (actions d)
                                   [Chara (true, false, false, false, false,
    false, true, false),
                                     Chara (true, true, false, false, false,
     true, true, false),
                                     Chara (false, false, true, false, true,
     true, true, false),
                                     Chara (true, false, false, true, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (false, true, true, true, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, false, false, false, false,
     true, true, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, false, false, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (false, true, true, true, false,
     true, true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (true, false, false, true, false,
     true, true, false),
                                     Chara (false, false, true, false, true,
     true, true, false),
                                     Chara (true, false, false, true, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (false, true, true, true, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, false, true, false, true,
     true, true, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, false, false, false, false,
     true, true, false),
                                     Chara (false, false, true, false, true,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, false, false, true, false,
     true, true, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, true, true, true, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (false, false, true, false, true,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, false, false, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (false, true, true, true, false,
     true, true, false),
                                     Chara (false, true, false, true, false,
     true, true, false),
                                     Chara (true, false, true, false, true,
     true, true, false),
                                     Chara (false, true, true, true, false,
     true, true, false),
                                     Chara (true, true, false, false, false,
     true, true, false),
                                     Chara (false, false, true, false, true,
     true, true, false),
                                     Chara (true, false, false, true, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (false, true, true, true, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (false, true, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, false, false, false, true,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (true, false, false, true, false,
     true, true, false),
                                     Chara (false, false, true, false, true,
     true, true, false),
                                     Chara (true, false, false, true, false,
     true, true, false),
                                     Chara (false, true, true, false, true,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, false, true, true, false,
     true, true, false),
                                     Chara (true, false, false, true, false,
     true, true, false),
                                     Chara (false, false, true, false, true,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (false, true, false, false, true,
     true, true, false),
                                     Chara (true, false, false, false, false,
     true, true, false),
                                     Chara (false, false, true, true, false,
     true, true, false),
                                     Chara (true, true, false, false, true,
     true, true, false)]
                                   (shows_prec_literal zero_nata o
                                     (fn x => nameb (heada x))))
                              (fn _ =>
                                bind (check_all_list (show_list show_char)
                                       act_conds_no_args (actions d)
                                       [Chara
  (true, false, false, false, false, false, true, false),
 Chara (true, true, false, false, false, true, true, false),
 Chara (false, false, true, false, true, true, true, false),
 Chara (true, false, false, true, false, true, true, false),
 Chara (true, true, true, true, false, true, true, false),
 Chara (false, true, true, true, false, true, true, false),
 Chara (false, false, false, false, false, true, false, false),
 Chara (true, true, false, false, false, true, true, false),
 Chara (true, true, true, true, false, true, true, false),
 Chara (false, true, true, true, false, true, true, false),
 Chara (false, false, true, false, false, true, true, false),
 Chara (true, false, false, true, false, true, true, false),
 Chara (false, false, true, false, true, true, true, false),
 Chara (true, false, false, true, false, true, true, false),
 Chara (true, true, true, true, false, true, true, false),
 Chara (false, true, true, true, false, true, true, false),
 Chara (false, false, false, false, false, true, false, false),
 Chara (true, false, false, true, false, true, true, false),
 Chara (true, true, false, false, true, true, true, false),
 Chara (false, false, false, false, false, true, false, false),
 Chara (false, true, true, true, false, true, true, false),
 Chara (true, true, true, true, false, true, true, false),
 Chara (false, false, true, false, true, true, true, false),
 Chara (false, false, false, false, false, true, false, false),
 Chara (true, false, false, false, false, true, true, false),
 Chara (false, true, false, false, true, true, true, false),
 Chara (true, true, true, false, false, true, true, false),
 Chara (true, false, true, false, true, true, true, false),
 Chara (true, false, true, true, false, true, true, false),
 Chara (true, false, true, false, false, true, true, false),
 Chara (false, true, true, true, false, true, true, false),
 Chara (false, false, true, false, true, true, true, false),
 Chara (true, false, true, true, false, true, false, false),
 Chara (false, true, true, false, false, true, true, false),
 Chara (false, true, false, false, true, true, true, false),
 Chara (true, false, true, false, false, true, true, false),
 Chara (true, false, true, false, false, true, true, false),
 Chara (false, false, false, false, false, true, false, false),
 Chara (false, false, false, true, false, true, false, false),
 Chara (false, true, true, true, false, true, true, false),
 Chara (true, false, true, false, true, true, true, false),
 Chara (true, false, true, true, false, true, true, false),
 Chara (true, false, true, false, false, true, true, false),
 Chara (false, true, false, false, true, true, true, false),
 Chara (true, false, false, true, false, true, true, false),
 Chara (true, true, false, false, false, true, true, false),
 Chara (true, true, true, true, false, true, false, false),
 Chara (true, false, true, false, false, true, true, false),
 Chara (true, false, false, false, true, true, true, false),
 Chara (true, false, false, false, false, false, true, false),
 Chara (false, false, true, false, true, true, true, false),
 Chara (true, false, true, true, false, true, true, false),
 Chara (false, false, false, false, false, true, false, false),
 Chara (true, false, false, false, false, true, true, false),
 Chara (false, false, true, false, true, true, true, false),
 Chara (true, true, true, true, false, true, true, false),
 Chara (true, false, true, true, false, true, true, false),
 Chara (true, true, false, false, true, true, true, false),
 Chara (false, false, false, false, false, true, false, false),
 Chara (true, true, true, false, true, true, true, false),
 Chara (true, false, false, true, false, true, true, false),
 Chara (false, false, true, false, true, true, true, false),
 Chara (false, false, false, true, false, true, true, false),
 Chara (false, false, false, false, false, true, false, false),
 Chara (true, false, false, false, false, true, true, false),
 Chara (false, true, false, false, true, true, true, false),
 Chara (true, true, true, false, false, true, true, false),
 Chara (true, false, true, false, true, true, true, false),
 Chara (true, false, true, true, false, true, true, false),
 Chara (true, false, true, false, false, true, true, false),
 Chara (false, true, true, true, false, true, true, false),
 Chara (false, false, true, false, true, true, true, false),
 Chara (true, true, false, false, true, true, true, false),
 Chara (true, false, false, true, false, true, false, false)]
                                       (shows_prec_literal zero_nata o
 (fn x => nameb (heada x))))
                                  (fn _ =>
                                    bind (check (null (consts d))
   (fn _ =>
     shows_prec_list show_char zero_nata
       [Chara (false, false, true, false, false, false, true, false),
         Chara (true, true, true, true, false, true, true, false),
         Chara (true, false, true, true, false, true, true, false),
         Chara (true, false, false, false, false, true, true, false),
         Chara (true, false, false, true, false, true, true, false),
         Chara (false, true, true, true, false, true, true, false),
         Chara (false, false, false, false, false, true, false, false),
         Chara (false, false, false, true, false, true, true, false),
         Chara (true, false, false, false, false, true, true, false),
         Chara (true, true, false, false, true, true, true, false),
         Chara (false, false, false, false, false, true, false, false),
         Chara (true, true, false, false, false, true, true, false),
         Chara (true, true, true, true, false, true, true, false),
         Chara (false, true, true, true, false, true, true, false),
         Chara (true, true, false, false, true, true, true, false),
         Chara (false, false, true, false, true, true, true, false),
         Chara (true, false, false, false, false, true, true, false),
         Chara (false, true, true, true, false, true, true, false),
         Chara (false, false, true, false, true, true, true, false),
         Chara (true, true, false, false, true, true, true, false)]))
                                      (fn _ =>
check_all_list (show_list show_char)
  (form_preds_no_args (ccompare_object, equal_object)) (inita p)
  [Chara (true, false, false, true, false, false, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, true, false, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, false, true, false, true, false, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, true, true, false, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (true, false, false, true, false, true, false, false)]
  (fn _ => fn y => shows_prec_list show_char zero_nata y []))))))))))
  end;

fun check_ground_problem p =
  bind (check_ground_problem_core p)
    (fn _ =>
      check (null (functions (domain p)))
        (fn _ =>
          shows_prec_list show_char zero_nata
            [Chara (false, false, true, false, false, false, true, false),
              Chara (true, true, true, true, false, true, true, false),
              Chara (true, false, true, true, false, true, true, false),
              Chara (true, false, false, false, false, true, true, false),
              Chara (true, false, false, true, false, true, true, false),
              Chara (false, true, true, true, false, true, true, false),
              Chara (false, false, false, false, false, true, false, false),
              Chara (false, false, false, true, false, true, true, false),
              Chara (true, false, false, false, false, true, true, false),
              Chara (true, true, false, false, true, true, true, false),
              Chara (false, false, false, false, false, true, false, false),
              Chara (false, true, true, false, false, true, true, false),
              Chara (true, false, true, false, true, true, true, false),
              Chara (false, true, true, true, false, true, true, false),
              Chara (true, true, false, false, false, true, true, false),
              Chara (false, false, true, false, true, true, true, false),
              Chara (true, false, false, true, false, true, true, false),
              Chara (true, true, true, true, false, true, true, false),
              Chara (false, true, true, true, false, true, true, false),
              Chara (true, true, false, false, true, true, true, false)]));

fun auto_loc_ids_to_names n m =
  (if equal_nata n zero_nata
    then (if equal_nata m zero_nata then "init"
           else (if equal_nata (minus_nata m one_nata) zero_nata then "planning"
                  else (if equal_nata
                             (minus_nata (minus_nata m one_nata) one_nata)
                             zero_nata
                         then "goal" else (raise Fail "undefined"))))
    else (if equal_nata m zero_nata then "off"
           else (if equal_nata (minus_nata m one_nata) zero_nata then "starting"
                  else (if equal_nata
                             (minus_nata (minus_nata m one_nata) one_nata)
                             zero_nata
                         then "running"
                         else (if equal_nata
                                    (minus_nata
                                      (minus_nata (minus_nata m one_nata)
one_nata)
                                      one_nata)
                                    zero_nata
                                then "ending"
                                else (raise Fail "undefined"))))));

fun actions_spec p = actions (domain p);

fun auto_names p =
  "main" :: map (fn x => "act_" ^ nameb (heada x)) (actions_spec p);

fun auto_names_to_index p = index equal_literal (auto_names p);

val goal_loc_impl : nat = nat_of_integer (2 : Int.int);

val reach_formula : (nat, nat, string, inta) formulaa =
  EX (Loc (zero_nata, goal_loc_impl));

val net_broadcast : string list = [];

fun pre_imp_list x = app_snap x;

fun del_imp_list x = app_snap x;

fun add_imp_list x = app_snap x;

fun map_numeric_effect f (NumericEffect (x1, x2, x3)) =
  NumericEffect
    (x1, map_primitive_numeric_expression f x2, map_numeric_expression f x3);

fun map_ast_effect f (Effect (x1, x2, x3)) =
  Effect
    (map (map_formula (map_atom f)) x1, map (map_formula (map_atom f)) x2,
      map (map_numeric_effect f) x3);

fun instantiate_simple_body (SimpleActionBody (pre, eff)) f =
  let
    val pre_inst = (map_formula o map_atom) f pre;
    val a = map_ast_effect f eff;
  in
    GroundAction (pre_inst, a)
  end;

fun instantiate_temporal_action_schema (SimpleActionSchemaa (h, b)) args =
  instantiate_simple_body b (tsubst h args);

fun duration_constraint_as_formula (DurationConstraint (EQ, r)) =
  Atom (NumericEqAtm (DurationExpr, r))
  | duration_constraint_as_formula (DurationConstraint (LEQ, r)) =
    Atom (NumericLEAtm (DurationExpr, r))
  | duration_constraint_as_formula (DurationConstraint (GEQ, r)) =
    Atom (NumericGEAtm (DurationExpr, r));

fun inst_duration_in_numeric_effect (NumericEffect (p, l, r)) d =
  NumericEffect (p, l, inst_duration_in_numeric_expression r d);

fun inst_duration_in_ast_effect (Effect (a, de, nums)) d =
  Effect (a, de, map (fn x => inst_duration_in_numeric_effect x d) nums);

fun inst_snap_action_body_elements d cond eff f dur ta =
  let
    val pre_i =
      inst_formula f dur
        (bigAnd
          (filter_time_spec ta
            (cond @
              map (fn (x, y) => (x, duration_constraint_as_formula y)) d)));
    val a =
      inst_duration_in_ast_effect
        (map_ast_effect f (conjunct_effects (filter_time_spec ta eff))) dur;
  in
    GroundAction (pre_i, a)
  end;

fun at_start_spec (SimpleActionSchemaa (h, b)) =
  instantiate_temporal_action_schema (SimpleActionSchemaa (h, b)) []
  | at_start_spec
    (DurativeActionSchema (h, DurativeActionBody (dc, cond, deff))) =
    inst_snap_action_body_elements [] cond deff (tsubst h []) zero_rat At_Start;

val ground_non_action : ground_action =
  GroundAction (Not Bot, Effect ([], [], []));

fun at_end_spec (SimpleActionSchemaa (h, b)) = ground_non_action
  | at_end_spec (DurativeActionSchema (h, DurativeActionBody (dc, cond, deff)))
    = inst_snap_action_body_elements [] cond deff (tsubst h []) zero_rat At_End;

fun dels_spec (GroundAction (form, eff)) =
  remdups equal_predicate (map to_predicate (dels eff));

fun adds_spec (GroundAction (form, eff)) =
  remdups equal_predicate (map to_predicate (adds eff));

fun pre_spec (GroundAction (form, eff)) =
  remdups equal_predicate (map to_predicate (to_literals form));

fun mutex_snap_action (B1_, B2_, B3_) =
  (fn pre => fn adds => fn dels => fn a => fn b =>
    not (is_empty (B1_, B2_, B3_)
          (inf_seta (B2_, ccompare_cproper_interval B3_) (pre a)
            (sup_seta (B2_, ccompare_cproper_interval B3_) (adds b)
              (dels b)))) orelse
      (not (is_empty (B1_, B2_, B3_)
             (inf_seta (B2_, ccompare_cproper_interval B3_) (adds a)
               (dels b))) orelse
        (not (is_empty (B1_, B2_, B3_)
               (inf_seta (B2_, ccompare_cproper_interval B3_) (pre b)
                 (sup_seta (B2_, ccompare_cproper_interval B3_) (adds a)
                   (dels a)))) orelse
          not (is_empty (B1_, B2_, B3_)
                (inf_seta (B2_, ccompare_cproper_interval B3_) (adds b)
                  (dels a))))));

fun mutex_snap_actiona a b =
  mutex_snap_action
    (card_UNIV_predicate, ceq_predicate, cproper_interval_predicate)
    (fn aa =>
      set (ceq_predicate, ccompare_predicate, set_impl_predicate)
        (pre_imp_list at_start_spec at_end_spec pre_spec aa))
    (fn aa =>
      set (ceq_predicate, ccompare_predicate, set_impl_predicate)
        (add_imp_list at_start_spec at_end_spec adds_spec aa))
    (fn aa =>
      set (ceq_predicate, ccompare_predicate, set_impl_predicate)
        (del_imp_list at_start_spec at_end_spec dels_spec aa))
    a b;

fun act_to_start_clock_impl act_to_name a = "start_" ^ act_to_name a;

fun act_to_end_clock_impl act_to_name a = "end_" ^ act_to_name a;

fun net_int_clocks p a =
  map_filter
    (fn x =>
      (if mutex_snap_actiona a (AtStart x)
        then SOME (act_to_start_clock_impl (fn xa => nameb (heada xa)) x)
        else NONE))
    (actions_spec p) @
    map_filter
      (fn x =>
        (if mutex_snap_actiona a (AtEnd x)
          then SOME (act_to_end_clock_impl (fn xa => nameb (heada xa)) x)
          else NONE))
      (actions_spec p);

val planning_lock_impl : string = "planning_lock";

val starting_loc_impl : nat = one_nata;

val ending_loc_impl : nat = nat_of_integer (3 : Int.int);

fun map_upper_bound f (LT x1) = LT (f x1)
  | map_upper_bound f (LE x2) = LE (f x2);

fun dc_list_upper xs = min_ub_opt linorder_rat (map dc_to_ub xs) NONE;

fun upper_spec_impl (SimpleActionSchemaa (h, b)) = SOME (LE zero_inta)
  | upper_spec_impl
    (DurativeActionSchema (h, DurativeActionBody (dc, cond, deff))) =
    map_option (map_upper_bound floor_rat) (dc_list_upper (map snd dc));

fun u_dur_impl a =
  (case upper_spec_impl a of NONE => []
    | SOME (LT n) =>
      [LTa (act_to_start_clock_impl (fn x => nameb (heada x)) a, n)]
    | SOME (LE n) =>
      [LEa (act_to_start_clock_impl (fn x => nameb (heada x)) a, n)]);

fun map_lower_bound f (GT x1) = GT (f x1)
  | map_lower_bound f (GE x2) = GE (f x2);

fun dc_list_lower xs = max_lb_opt linorder_rat (map dc_to_lb xs) NONE;

fun lower_spec_impl (SimpleActionSchemaa (h, b)) = SOME (GE zero_inta)
  | lower_spec_impl
    (DurativeActionSchema (h, DurativeActionBody (dc, cond, deff))) =
    map_option (map_lower_bound floor_rat) (dc_list_lower (map snd dc));

fun l_dur_impl a =
  (case lower_spec_impl a of NONE => []
    | SOME (GT n) =>
      [GTa (act_to_start_clock_impl (fn x => nameb (heada x)) a, n)]
    | SOME (GE n) =>
      [GEa (act_to_start_clock_impl (fn x => nameb (heada x)) a, n)]);

fun instant_trans_edge A_ p a =
  let
    val end_snap = AtEnd a;
    val _ = AtStart a;
    val int_clocks =
      map (fn x => GTa (x, zero_inta)) (net_int_clocks p end_snap) @
        map (fn x => GEa (x, zero_inta)) (net_int_clocks p end_snap);
    val guard = l_dur_impl a @ u_dur_impl a @ int_clocks;
    val resets = [act_to_end_clock_impl (fn x => nameb (heada x)) a];
  in
    (starting_loc_impl,
      (Eqa (Var planning_lock_impl, Const (one A_)),
        (guard, (Sil "", ([], (resets, ending_loc_impl))))))
  end;

fun prop_to_lock_impl prop_to_name p = "lock_" ^ prop_to_name p;

fun prop_to_var_impl prop_to_name p = "var_" ^ prop_to_name p;

val acts_active_impl : string = "acts_active";

val off_loc_impl : nat = zero_nata;

fun start_edge (A1_, A2_) B_ (C1_, C2_, C3_) p a =
  let
    val start_snap = AtStart a;
    val guard =
      map (fn x => GTa (x, zero B_)) (net_int_clocks p start_snap) @
        map (fn x => GEa (x, zero B_)) (net_int_clocks p start_snap);
    val not_locked_check =
      map_filter
        (fn x =>
          (if not (membera equal_predicate
                    (add_imp_list at_start_spec at_end_spec adds_spec
                      start_snap)
                    x)
            then SOME (((fn v => Eqa (Var v, Const (zero A2_))) o
                         prop_to_lock_impl namea)
                        x)
            else NONE))
        (del_imp_list at_start_spec at_end_spec dels_spec start_snap);
    val pre_check =
      map ((fn v => Eqa (Var v, Const (one A1_))) o prop_to_var_impl namea)
        (pre_imp_list at_start_spec at_end_spec pre_spec start_snap);
    val var_check =
      bexp_and_all
        (Eqa (Var planning_lock_impl, Const (one A1_)) ::
          not_locked_check @ pre_check);
    val add_upds =
      map ((fn v => (v, Const (one C1_))) o prop_to_var_impl namea)
        (add_imp_list at_start_spec at_end_spec adds_spec start_snap);
    val del_upds =
      map ((fn v => (v, Const (zero C3_))) o prop_to_var_impl namea)
        (del_imp_list at_start_spec at_end_spec dels_spec start_snap);
    val upds =
      (acts_active_impl,
        Binop (plus C2_, Var acts_active_impl, Const (one C1_))) ::
        del_upds @ add_upds;
    val resets = [act_to_start_clock_impl (fn x => nameb (heada x)) a];
  in
    (off_loc_impl,
      (var_check, (guard, (Sil "", (upds, (resets, starting_loc_impl))))))
  end;

fun end_edge (A1_, A2_) (C1_, C2_, C3_, C4_) a =
  let
    val end_instant = ending_loc_impl;
    val off = off_loc_impl;
    val end_snap = AtEnd a;
    val not_locked_check =
      map_filter
        (fn x =>
          (if not (membera equal_predicate
                    (add_imp_list at_start_spec at_end_spec adds_spec end_snap)
                    x)
            then SOME (((fn v => Eqa (Var v, Const (zero A2_))) o
                         prop_to_lock_impl namea)
                        x)
            else NONE))
        (del_imp_list at_start_spec at_end_spec dels_spec end_snap);
    val pre_check =
      map ((fn v => Eqa (Var v, Const (one A1_))) o prop_to_var_impl namea)
        (pre_imp_list at_start_spec at_end_spec pre_spec end_snap);
    val check =
      bexp_and_all
        (Eqa (Var planning_lock_impl, Const (one A1_)) ::
          not_locked_check @ pre_check);
    val add_upds =
      map ((fn v => (v, Const (one C1_))) o prop_to_var_impl namea)
        (add_imp_list at_start_spec at_end_spec adds_spec end_snap);
    val del_upds =
      map ((fn v => (v, Const (zero C4_))) o prop_to_var_impl namea)
        (del_imp_list at_start_spec at_end_spec dels_spec end_snap);
    val upds =
      (acts_active_impl,
        Binop (plus C2_, Var acts_active_impl, Const (uminus C3_ (one C1_)))) ::
        del_upds @ add_upds;
  in
    (end_instant, (check, ([], (Sil "", (upds, ([], off))))))
  end;

fun over_all_snap (SimpleActionSchemaa (h, b)) = ground_non_action
  | over_all_snap
    (DurativeActionSchema (h, DurativeActionBody (dc, cond, deff))) =
    inst_snap_action_body_elements [] cond deff (tsubst h []) zero_rat Over_All;

fun over_all_spec x = pre_spec (over_all_snap x);

val running_loc_impl : nat = nat_of_integer (2 : Int.int);

fun edge_3 A_ (B1_, B2_, B3_) p a =
  let
    val end_snap = AtEnd a;
    val int_clocks =
      map (fn x => GTa (x, zero_inta)) (net_int_clocks p end_snap) @
        map (fn x => GEa (x, zero_inta)) (net_int_clocks p end_snap);
    val guard = l_dur_impl a @ u_dur_impl a @ int_clocks;
    val upds =
      map ((fn v =>
             (v, Binop (plus B2_, Var v, Const (uminus B3_ (one B1_))))) o
            prop_to_lock_impl namea)
        (over_all_spec a);
    val resets = [act_to_end_clock_impl (fn x => nameb (heada x)) a];
  in
    (running_loc_impl,
      (Eqa (Var planning_lock_impl, Const (one A_)),
        (guard, (Sil "", (upds, (resets, ending_loc_impl))))))
  end;

fun edge_2 A_ (C1_, C2_) a =
  let
    val check_invs =
      bexp_and_all
        (Eqa (Var planning_lock_impl, Const (one A_)) ::
          map ((fn v => Eqa (Var v, Const (one A_))) o prop_to_var_impl namea)
            (over_all_spec a));
    val upds =
      map ((fn v => (v, Binop (plus C2_, Var v, Const (one C1_)))) o
            prop_to_lock_impl namea)
        (over_all_spec a);
  in
    (starting_loc_impl,
      (check_invs, ([], (Sil "", (upds, ([], running_loc_impl))))))
  end;

fun action_to_automaton (B1_, B2_) (C1_, C2_, C3_, C4_) p a =
  let
    val committed_locs = [];
    val urgent_locs = [starting_loc_impl, ending_loc_impl];
    val edges =
      [start_edge (B1_, B2_) zero_int (C1_, C2_, C4_) p a,
        edge_2 B1_ (C1_, C2_) a, edge_3 B1_ (C1_, C2_, C3_) p a,
        end_edge (B1_, B2_) (C1_, C2_, C3_, C4_) a, instant_trans_edge B1_ p a];
    val invs = [];
  in
    (committed_locs, (urgent_locs, (edges, invs)))
  end;

fun init_spec p =
  map_filter (fn x => (if is_predAtom x then SOME (to_predicate x) else NONE))
    (inita p);

val planning_loc_impl : nat = one_nata;

val init_loc_impl : nat = zero_nata;

fun main_auto_init_edge A_ (D1_, D2_) p =
  let
    val can_start = Eqa (Var planning_lock_impl, Const (zero A_));
    val permit_planning = (planning_lock_impl, Const (one D1_));
    val set_active = (acts_active_impl, Const (zero D2_));
    val set_props =
      map ((fn v => (v, Const (one D1_))) o prop_to_var_impl namea)
        (init_spec p);
    val upds = permit_planning :: set_active :: set_props;
  in
    (init_loc_impl,
      (can_start, ([], (Sil "", (upds, ([], planning_loc_impl))))))
  end;

fun goal_spec p =
  remdups equal_predicate (map to_predicate (to_literals (goal p)));

fun main_auto_goal_edge p =
  let
    val can_end =
      [Eqa (Var planning_lock_impl, Const one_inta),
        Eqa (Var acts_active_impl, Const zero_inta)];
    val goal_sat =
      map ((fn v => Eqa (Var v, Const one_inta)) o prop_to_var_impl namea)
        (goal_spec p);
    val cond = bexp_and_all (can_end @ goal_sat);
    val lock_plan =
      (planning_lock_impl, Const (Int_of_integer (2 : Int.int)));
  in
    (planning_loc_impl,
      (cond, ([], (Sil "", ([lock_plan], ([], goal_loc_impl))))))
  end;

val main_auto_loop_impl :
  nat * ((string, inta) bexp *
          ((string, inta) acconstraint list *
            (string act *
              ((string * (string, inta) exp) list * (string list * nat)))))
  = (goal_loc_impl, (True, ([], (Sil "", ([], ([], goal_loc_impl))))));

fun main_auto p =
  let
    val committed_locs = [];
    val urgent_locs = [init_loc_impl, goal_loc_impl];
    val edges =
      [main_auto_init_edge zero_int (one_int, zero_int) p,
        main_auto_goal_edge p, main_auto_loop_impl];
    val invs = [];
  in
    (committed_locs, (urgent_locs, (edges, invs)))
  end;

fun net_automata p =
  main_auto p ::
    map (action_to_automaton (one_int, zero_int)
          (one_int, plus_int, uminus_int, zero_int) p)
      (actions_spec p);

fun snap_vars snap =
  let
    val pre_vars =
      map (prop_to_var_impl namea)
        (pre_imp_list at_start_spec at_end_spec pre_spec snap);
    val add_vars =
      map (prop_to_var_impl namea)
        (add_imp_list at_start_spec at_end_spec adds_spec snap);
    val del_vars =
      map_filter
        (fn x =>
          (if not (membera equal_predicate
                    (add_imp_list at_start_spec at_end_spec adds_spec snap) x)
            then SOME (prop_to_lock_impl namea x) else NONE))
        (del_imp_list at_start_spec at_end_spec dels_spec snap) @
        map (prop_to_var_impl namea)
          (del_imp_list at_start_spec at_end_spec dels_spec snap);
  in
    set (ceq_literal, ccompare_literal, set_impl_literal)
      (pre_vars @ add_vars @ del_vars)
  end;

fun inv_vars invs =
  let
    val i = set (ceq_predicate, ccompare_predicate, set_impl_predicate) invs;
  in
    sup_seta (ceq_literal, ccompare_literal)
      (image (ceq_predicate, ccompare_predicate)
        (ceq_literal, ccompare_literal, set_impl_literal)
        (prop_to_lock_impl namea) i)
      (image (ceq_predicate, ccompare_predicate)
        (ceq_literal, ccompare_literal, set_impl_literal)
        (prop_to_var_impl namea) i)
  end;

fun action_vars a =
  let
    val inv_varsa = inv_vars (over_all_spec a);
    val start_vars = snap_vars (AtStart a);
    val aa = snap_vars (AtEnd a);
  in
    sup_seta (ceq_literal, ccompare_literal)
      (sup_seta (ceq_literal, ccompare_literal) inv_varsa start_vars) aa
  end;

fun props_spec p = map pred (predicates (domain p));

fun net_bounds p =
  let
    val action_varsa =
      sup_setb
        (finite_UNIV_literal, cenum_literal, ceq_literal,
          cproper_interval_literal, set_impl_literal)
        (image
          (ceq_ast_temporal_action_schema, ccompare_ast_temporal_action_schema)
          (ceq_set
             (cenum_literal, ceq_literal,
               ccompare_cproper_interval cproper_interval_literal),
            ccompare_set
              (finite_UNIV_literal, ceq_literal, cproper_interval_literal,
                set_impl_literal),
            set_impl_set)
          action_vars
          (set (ceq_ast_temporal_action_schema,
                 ccompare_ast_temporal_action_schema,
                 set_impl_ast_temporal_action_schema)
            (actions_spec p)));
    val init_vars =
      image (ceq_predicate, ccompare_predicate)
        (ceq_literal, ccompare_literal, set_impl_literal)
        (prop_to_var_impl namea)
        (set (ceq_predicate, ccompare_predicate, set_impl_predicate)
          (init_spec p));
    val goal_vars =
      image (ceq_predicate, ccompare_predicate)
        (ceq_literal, ccompare_literal, set_impl_literal)
        (prop_to_var_impl namea)
        (set (ceq_predicate, ccompare_predicate, set_impl_predicate)
          (goal_spec p));
    val vars_occ =
      sup_seta (ceq_literal, ccompare_literal)
        (sup_seta (ceq_literal, ccompare_literal) action_varsa init_vars)
        goal_vars;
    val prop_lock_var_defs =
      map (fn pa =>
            (prop_to_lock_impl namea pa,
              (zero_inta, int_of_nat (size_list (actions_spec p)))))
        (props_spec p);
    val prop_var_var_defs =
      map (fn pa => (prop_to_var_impl namea pa, (zero_inta, one_inta)))
        (props_spec p);
    val prop_var_defs =
      filter (fn x => member (ceq_literal, ccompare_literal) (fst x) vars_occ)
        (prop_lock_var_defs @ prop_var_var_defs);
    val acts_active_var =
      (acts_active_impl, (zero_inta, int_of_nat (size_list (actions_spec p))));
    val planning_lock_var =
      (planning_lock_impl, (zero_inta, Int_of_integer (2 : Int.int)));
  in
    [acts_active_var, planning_lock_var] @ prop_var_defs
  end;

fun clock_names p =
  map (act_to_start_clock_impl (fn x => nameb (heada x))) (actions_spec p) @
    map (act_to_end_clock_impl (fn x => nameb (heada x))) (actions_spec p);

fun init_vars p = map (map_prod id fst) (net_bounds p);

fun init_locs p = init_loc_impl :: map (fn _ => off_loc_impl) (actions_spec p);

fun make_network_impl p =
  let
    val automata = net_automata p;
    val broadcast = net_broadcast;
    val bounds = net_bounds p;
    val init_locsa = init_locs p;
    val init_varsa = init_vars p;
    val formula = reach_formula;
    val clock_namesa = clock_names p;
    val auto_namesa = auto_names p;
    val ids_to_names = auto_loc_ids_to_names;
    val process_names_to_index = auto_names_to_index p;
  in
    Inr (clock_namesa,
          (auto_namesa,
            (ids_to_names,
              (process_names_to_index,
                (broadcast,
                  (automata, (bounds, (formula, (init_locsa, init_varsa)))))))))
  end;

fun check_and_make_network p =
  bind (check_ground_problem p) (fn _ => make_network_impl p);

fun make_certified_net problem certifier =
  (case check_and_make_network problem
    of Inl e => Error ["Could not make network", implode (e () [])]
    | Inr (clocks, (names, network)) =>
      binda (case certifier (clocks, (names, network))
              of NONE => Error ["Certificate could not be generated"]
              | SOME a => Result a)
        (fn (renaming, cert) => Result (network, (renaming, cert))));

fun rat_of_digits_pair (ds_1, ds_2) =
  let
    val ds_1a = trim_ld_zs ds_1;
    val ds_2a = trim_tr_zs ds_2;
  in
    fract (int_of_digits (ds_1a @ ds_2a) zero_inta)
      (power power_int (Int_of_integer (10 : Int.int)) (size_list ds_2a))
  end;

fun dfs_map_impl A_ (B1_, B2_, B3_) succsi a_0i lei keyi copyi =
  (fn f_ => fn () => f_ ((ht_new (B2_, B3_) (heap_list A_)) ()) ())
    (fn x =>
      (fn f_ => fn () => f_ ((ht_new (B2_, B3_) (heap_list A_)) ()) ())
        (fn xa =>
          (fn f_ => fn () => f_ (a_0i ()) ())
            (fn xb =>
              (fn f_ => fn () => f_
                ((dfs_map_impl_0 A_ (B1_, B2_, B3_) succsi lei keyi copyi
                   (x, (xa, xb)))
                ()) ())
                (fn xc =>
                  (fn f_ => fn () => f_ (let
   val (a1, (_, a2a)) = xc;
 in
   (fn () => (a2a, a1))
 end
                    ()) ())
                    (fn (a1, _) => (fn () => a1))))));

fun err s = Error [s];

fun geta A_ m x =
  (case m x
    of NONE =>
      Error ["(Get) key not found: " ^ implode (shows_prec A_ zero_nata x [])]
    | SOME a => Result a);

fun pad m s =
  replicate m (Chara (false, false, false, false, false, true, false, false)) @
    s;

fun norm_upd_impl (A1_, A2_, A3_) n =
  (fn ai => fn bia => fn bi =>
    (fn f_ => fn () => f_
      ((mtx_get (heap_DBMEntry A3_) (suc n) ai (zero_nata, zero_nata)) ()) ())
      (fn x =>
        (fn f_ => fn () => f_
          ((mtx_set (heap_DBMEntry A3_) (suc n) ai (zero_nata, zero_nata)
             (norm_diag
               ((zero_monoid_add o monoid_add_group_add o
                  group_add_ab_group_add o ab_group_add_ordered_ab_group_add o
                  ordered_ab_group_add_linordered_ab_group_add)
                  A1_,
                 A2_,
                 (linorder_linordered_ab_semigroup_add o
                   linordered_ab_semigroup_add_linordered_ab_monoid_add o
                   linordered_ab_monoid_add_linordered_cancel_ab_monoid_add o
                   linordered_cancel_ab_monoid_add_linordered_ab_group_add)
                   A1_)
               x))
          ()) ())
          (fn xa =>
            (fn f_ => fn () => f_
              ((imp_for_inta one_nata (suc bi)
                 (fn xc => fn sigma =>
                   (fn f_ => fn () => f_
                     ((mtx_get (heap_DBMEntry A3_) (suc n) sigma
                        (zero_nata, xc))
                     ()) ())
                     (fn xb =>
                       mtx_set (heap_DBMEntry A3_) (suc n) sigma (zero_nata, xc)
                         (norm_lower
                           ((linorder_linordered_ab_semigroup_add o
                              linordered_ab_semigroup_add_linordered_ab_monoid_add o
                              linordered_ab_monoid_add_linordered_cancel_ab_monoid_add o
                              linordered_cancel_ab_monoid_add_linordered_ab_group_add)
                             A1_)
                           (norm_upper
                             ((linorder_linordered_ab_semigroup_add o
                                linordered_ab_semigroup_add_linordered_ab_monoid_add o
                                linordered_ab_monoid_add_linordered_cancel_ab_monoid_add o
                                linordered_cancel_ab_monoid_add_linordered_ab_group_add)
                               A1_)
                             xb (zero ((zero_monoid_add o monoid_add_group_add o
 group_add_ab_group_add o ab_group_add_ordered_ab_group_add o
 ordered_ab_group_add_linordered_ab_group_add)
A1_)))
                           (uminus
                             ((uminus_group_add o group_add_ab_group_add o
                                ab_group_add_ordered_ab_group_add o
                                ordered_ab_group_add_linordered_ab_group_add)
                               A1_)
                             (sub bia xc)))))
                 xa)
              ()) ())
              (imp_for_inta one_nata (suc bi)
                (fn xb => fn sigma =>
                  (fn f_ => fn () => f_
                    ((mtx_get (heap_DBMEntry A3_) (suc n) sigma (xb, zero_nata))
                    ()) ())
                    (fn xc =>
                      (fn f_ => fn () => f_
                        ((mtx_set (heap_DBMEntry A3_) (suc n) sigma
                           (xb, zero_nata)
                           (norm_lower
                             ((linorder_linordered_ab_semigroup_add o
                                linordered_ab_semigroup_add_linordered_ab_monoid_add o
                                linordered_ab_monoid_add_linordered_cancel_ab_monoid_add o
                                linordered_cancel_ab_monoid_add_linordered_ab_group_add)
                               A1_)
                             (norm_upper
                               ((linorder_linordered_ab_semigroup_add o
                                  linordered_ab_semigroup_add_linordered_ab_monoid_add o
                                  linordered_ab_monoid_add_linordered_cancel_ab_monoid_add o
                                  linordered_cancel_ab_monoid_add_linordered_ab_group_add)
                                 A1_)
                               xc (sub bia xb))
                             (uminus
                               ((uminus_group_add o group_add_ab_group_add o
                                  ab_group_add_ordered_ab_group_add o
                                  ordered_ab_group_add_linordered_ab_group_add)
                                 A1_)
                               (zero ((zero_monoid_add o monoid_add_group_add o
group_add_ab_group_add o ab_group_add_ordered_ab_group_add o
ordered_ab_group_add_linordered_ab_group_add)
                                       A1_)))))
                        ()) ())
                        (imp_for_inta one_nata (suc bi)
                          (fn xe => fn sigmaa =>
                            (if not (equal_nata xb xe)
                              then (fn f_ => fn () => f_
                                     ((mtx_get (heap_DBMEntry A3_) (suc n)
sigmaa (xb, xe))
                                     ()) ())
                                     (fn xd =>
                                       mtx_set (heap_DBMEntry A3_) (suc n)
 sigmaa (xb, xe)
 (norm_lower
   ((linorder_linordered_ab_semigroup_add o
      linordered_ab_semigroup_add_linordered_ab_monoid_add o
      linordered_ab_monoid_add_linordered_cancel_ab_monoid_add o
      linordered_cancel_ab_monoid_add_linordered_ab_group_add)
     A1_)
   (norm_upper
     ((linorder_linordered_ab_semigroup_add o
        linordered_ab_semigroup_add_linordered_ab_monoid_add o
        linordered_ab_monoid_add_linordered_cancel_ab_monoid_add o
        linordered_cancel_ab_monoid_add_linordered_ab_group_add)
       A1_)
     xd (sub bia xb))
   (uminus
     ((uminus_group_add o group_add_ab_group_add o
        ab_group_add_ordered_ab_group_add o
        ordered_ab_group_add_linordered_ab_group_add)
       A1_)
     (sub bia xe))))
                              else (fn f_ => fn () => f_
                                     ((mtx_get (heap_DBMEntry A3_) (suc n)
sigmaa (xb, xe))
                                     ()) ())
                                     (fn xd =>
                                       mtx_set (heap_DBMEntry A3_) (suc n)
 sigmaa (xb, xe)
 (norm_diag
   ((zero_monoid_add o monoid_add_group_add o group_add_ab_group_add o
      ab_group_add_ordered_ab_group_add o
      ordered_ab_group_add_linordered_ab_group_add)
      A1_,
     A2_,
     (linorder_linordered_ab_semigroup_add o
       linordered_ab_semigroup_add_linordered_ab_monoid_add o
       linordered_ab_monoid_add_linordered_cancel_ab_monoid_add o
       linordered_cancel_ab_monoid_add_linordered_ab_group_add)
       A1_)
   xd)))))))))));

fun scan_parens lparen rparen inner =
  bindb (gen_token lx_ws (exactly (equal_char, show_char) lparen))
    (fn _ =>
      bindb (gen_token lx_ws inner)
        (fn a =>
          bindb (gen_token lx_ws (exactly (equal_char, show_char) rparen))
            (fn _ => return a)));

fun lx_underscore x =
  bindb (exactly (equal_char, show_char)
          [Chara (true, true, true, true, true, false, true, false)])
    (fn _ => return (Chara (true, true, true, true, true, false, true, false)))
    x;

fun lx_hyphen x =
  bindb (exactly (equal_char, show_char)
          [Chara (true, false, true, true, false, true, false, false)])
    (fn _ =>
      return (Chara (true, false, true, true, false, true, false, false)))
    x;

fun ta_var_ident x =
  bindb (alt (bindb (alt lx_alpha lx_digit) (fn xa => return (sum_join xa)))
          lx_underscore)
    (fn xa =>
      bindb (repeat
              (bindb
                (alt (bindb (alt lx_alpha lx_digit)
                       (fn xb => return (sum_join xb)))
                  (bindb (alt lx_underscore lx_hyphen)
                    (fn xb => return (sum_join xb))))
                (fn xb => return (sum_join xb))))
        (fn xaa =>
          return (uncurry (fn a => fn b => a :: b) (sum_join xa, xaa))))
    x;

fun scan_var x = ta_var_ident x;

fun scan_infix_pair a b s =
  bindb (gen_token lx_ws a)
    (fn aa =>
      bindb (gen_token lx_ws (exactly (equal_char, show_char) s))
        (fn _ => bindb (gen_token lx_ws b) (fn ba => return (aa, ba))));

fun aexp l =
  bindb (alt (bindb (gen_token lx_ws lx_int) (fn x => return (Const x)))
          (bindb
            (alt (bindb (gen_token lx_ws scan_var)
                   (fn x => return ((Var o implode) x)))
              (bindb
                (alt (bindb
                       (scan_parens
                         [Chara (false, false, false, true, false, true, false,
                                  false)]
                         [Chara (true, false, false, true, false, true, false,
                                  false)]
                         (bindb (gen_token lx_ws scan_exp)
                           (fn a =>
                             bindb (gen_token lx_ws
                                     (exactly (equal_char, show_char)
                                       [Chara
  (true, true, true, true, true, true, false, false)]))
                               (fn _ =>
                                 bindb (gen_token lx_ws scan_7)
                                   (fn x =>
                                     bindb (gen_token lx_ws
     (exactly (equal_char, show_char)
       [Chara (false, true, false, true, true, true, false, false)]))
                                       (fn _ =>
 bindb scan_exp (fn xa => return (a, (x, xa)))))))))
                       (fn x => return let
 val (e1, (b, a)) = x;
                                       in
 If_then_else (b, e1, a)
                                       end))
                  (bindb (gen_token lx_ws tk_lparen)
                    (fn _ =>
                      bindb (gen_token lx_ws scan_exp)
                        (fn a => bindb tk_rparen (fn _ => return a)))))
                (fn x => return (sum_join x))))
            (fn x => return (sum_join x))))
    (fn x => return (sum_join x)) l
and mexp l =
  chainL1 aexp
    (bindb
      (alt (bindb tk_times (fn _ => return times_inta))
        (bindb tk_div (fn _ => return divide_int)))
      (fn x => return (fn a => fn b => Binop (sum_join x, a, b))))
    l
and scan_exp l =
  chainL1 mexp
    (bindb
      (alt (bindb tk_plus (fn _ => return plus_inta))
        (bindb tk_minus (fn _ => return minus_inta)))
      (fn x => return (fn a => fn b => Binop (sum_join x, a, b))))
    l
and scan_0 l =
  bindb (alt (bindb
               (gen_token lx_ws
                 (bindb
                   (alt (exactly (equal_char, show_char)
                          [Chara (false, true, true, true, true, true, true,
                                   false)])
                     (exactly (equal_char, show_char)
                       [Chara (true, false, false, false, false, true, false,
                                false)]))
                   (fn x => return (sum_join x))))
               (fn _ =>
                 bindb (scan_parens
                         [Chara (false, false, false, true, false, true, false,
                                  false)]
                         [Chara (true, false, false, true, false, true, false,
                                  false)]
                         scan_7)
                   (fn x => return (Nota x))))
          (bindb
            (alt (bindb
                   (gen_token lx_ws
                     (exactly (equal_char, show_char)
                       [Chara (false, false, true, false, true, true, true,
                                false),
                         Chara (false, true, false, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false)]))
                   (fn _ => return True))
              (bindb
                (alt (bindb
                       (scan_infix_pair aexp aexp
                         [Chara (false, false, true, true, true, true, false,
                                  false),
                           Chara (true, false, true, true, true, true, false,
                                   false)])
                       (fn x =>
                         return (uncurry (fn a => fn b => Lea (a, b)) x)))
                  (bindb
                    (alt (bindb
                           (scan_infix_pair aexp aexp
                             [Chara (false, false, true, true, true, true,
                                      false, false)])
                           (fn x =>
                             return (uncurry (fn a => fn b => Ltb (a, b)) x)))
                      (bindb
                        (alt (bindb
                               (scan_infix_pair aexp aexp
                                 [Chara (true, false, true, true, true, true,
  false, false),
                                   Chara (true, false, true, true, true, true,
   false, false)])
                               (fn x =>
                                 return
                                   (uncurry (fn a => fn b => Eqa (a, b)) x)))
                          (bindb
                            (alt (bindb
                                   (scan_infix_pair aexp aexp
                                     [Chara
(true, false, true, true, true, true, false, false)])
                                   (fn x =>
                                     return
                                       (uncurry (fn a => fn b => Eqa (a, b))
 x)))
                              (bindb
                                (alt (bindb
                                       (scan_infix_pair aexp aexp
 [Chara (false, true, true, true, true, true, false, false)])
                                       (fn x =>
 return (uncurry (fn a => fn b => Gta (a, b)) x)))
                                  (bindb
                                    (alt (bindb
   (scan_infix_pair aexp aexp
     [Chara (false, true, true, true, true, true, false, false),
       Chara (true, false, true, true, true, true, false, false)])
   (fn x => return (uncurry (fn a => fn b => Ge (a, b)) x)))
                                      (scan_parens
[Chara (false, false, false, true, false, true, false, false)]
[Chara (true, false, false, true, false, true, false, false)] scan_7))
                                    (fn x => return (sum_join x))))
                                (fn x => return (sum_join x))))
                            (fn x => return (sum_join x))))
                        (fn x => return (sum_join x))))
                    (fn x => return (sum_join x))))
                (fn x => return (sum_join x))))
            (fn x => return (sum_join x))))
    (fn x => return (sum_join x)) l
and scan_6 l =
  bindb (alt (bindb
               (scan_infix_pair scan_0 scan_6
                 [Chara (false, true, true, false, false, true, false, false),
                   Chara (false, true, true, false, false, true, false, false)])
               (fn x => return (uncurry (fn a => fn b => Anda (a, b)) x)))
          scan_0)
    (fn x => return (sum_join x)) l
and scan_7 l =
  bindb (alt (bindb
               (scan_infix_pair scan_6 scan_7
                 [Chara (true, false, true, true, false, true, false, false),
                   Chara (false, true, true, true, true, true, false, false)])
               (fn x => return (uncurry (fn a => fn b => Imply (a, b)) x)))
          (bindb
            (alt (bindb
                   (scan_infix_pair scan_6 scan_7
                     [Chara (false, false, true, true, true, true, true, false),
                       Chara (false, false, true, true, true, true, true,
                               false)])
                   (fn x => return (uncurry (fn a => fn b => Ora (a, b)) x)))
              scan_6)
            (fn x => return (sum_join x))))
    (fn x => return (sum_join x)) l;

fun parse parser s =
  (case parse_all lx_ws parser s
    of Inl e =>
      Error [implode
               (e () [Chara (false, false, false, false, true, false, true,
                              false),
                       Chara (true, false, false, false, false, true, true,
                               false),
                       Chara (false, true, false, false, true, true, true,
                               false),
                       Chara (true, true, false, false, true, true, true,
                               false),
                       Chara (true, false, true, false, false, true, true,
                               false),
                       Chara (false, true, false, false, true, true, true,
                               false),
                       Chara (false, true, false, true, true, true, false,
                               false),
                       Chara (false, false, false, false, false, true, false,
                               false)])]
    | Inr a => Result a);

fun of_nat json =
  (case json of Object _ => Error ["of_nat: expected natural number"]
    | Arraya _ => Error ["of_nat: expected natural number"]
    | Stringa _ => Error ["of_nat: expected natural number"]
    | Int _ => Error ["of_nat: expected natural number"] | Nata a => Result a
    | Rat _ => Error ["of_nat: expected natural number"]
    | Boolean _ => Error ["of_nat: expected natural number"]
    | Null => Error ["of_nat: expected natural number"]);

fun dbm_subset_impl (A1_, A2_, A3_) n =
  (fn ai => fn bi =>
    imp_for_int zero_nata (suc n) (fn a => (fn () => a))
      (fn xb => fn _ =>
        imp_for_int zero_nata (suc n) (fn a => (fn () => a))
          (fn xe => fn _ =>
            (fn f_ => fn () => f_
              ((mtx_get (heap_DBMEntry A3_) (suc n) ai (xb, xe)) ()) ())
              (fn x_f =>
                (fn f_ => fn () => f_
                  ((mtx_get (heap_DBMEntry A3_) (suc n) bi (xb, xe)) ()) ())
                  (fn x_g =>
                    (fn () =>
                      (less_eq_DBMEntry
                        (A2_, (linorder_linordered_ab_semigroup_add o
                                linordered_ab_semigroup_add_linordered_ab_monoid_add o
                                linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
                                A1_)
                        x_f x_g)))))
          true)
      true);

fun map_sexpa f1 f2 f3 f4 Truea = Truea
  | map_sexpa f1 f2 f3 f4 (Notb x2) = Notb (map_sexpa f1 f2 f3 f4 x2)
  | map_sexpa f1 f2 f3 f4 (Andb (x31, x32)) =
    Andb (map_sexpa f1 f2 f3 f4 x31, map_sexpa f1 f2 f3 f4 x32)
  | map_sexpa f1 f2 f3 f4 (Orb (x41, x42)) =
    Orb (map_sexpa f1 f2 f3 f4 x41, map_sexpa f1 f2 f3 f4 x42)
  | map_sexpa f1 f2 f3 f4 (Implya (x51, x52)) =
    Implya (map_sexpa f1 f2 f3 f4 x51, map_sexpa f1 f2 f3 f4 x52)
  | map_sexpa f1 f2 f3 f4 (Eqb (x61, x62)) = Eqb (f3 x61, f4 x62)
  | map_sexpa f1 f2 f3 f4 (Leb (x71, x72)) = Leb (f3 x71, f4 x72)
  | map_sexpa f1 f2 f3 f4 (Ltc (x81, x82)) = Ltc (f3 x81, f4 x82)
  | map_sexpa f1 f2 f3 f4 (Gea (x91, x92)) = Gea (f3 x91, f4 x92)
  | map_sexpa f1 f2 f3 f4 (Gtb (x101, x102)) = Gtb (f3 x101, f4 x102)
  | map_sexpa f1 f2 f3 f4 (Loc (x111, x112)) = Loc (f1 x111, f2 x112);

fun map_formulab f1 f2 f3 f4 (EX x1) = EX (map_sexpa f1 f2 f3 f4 x1)
  | map_formulab f1 f2 f3 f4 (EG x2) = EG (map_sexpa f1 f2 f3 f4 x2)
  | map_formulab f1 f2 f3 f4 (AX x3) = AX (map_sexpa f1 f2 f3 f4 x3)
  | map_formulab f1 f2 f3 f4 (AG x4) = AG (map_sexpa f1 f2 f3 f4 x4)
  | map_formulab f1 f2 f3 f4 (Leadsto (x51, x52)) =
    Leadsto (map_sexpa f1 f2 f3 f4 x51, map_sexpa f1 f2 f3 f4 x52);

fun rename_locs_sexp f (Notb a) =
  binda (rename_locs_sexp f a) (fn aa => Result (Notb aa))
  | rename_locs_sexp f (Implya (a, b)) =
    binda (rename_locs_sexp f a)
      (fn aa =>
        binda (rename_locs_sexp f b) (fn ba => Result (Implya (aa, ba))))
  | rename_locs_sexp f (Orb (a, b)) =
    binda (rename_locs_sexp f a)
      (fn aa => binda (rename_locs_sexp f b) (fn ba => Result (Orb (aa, ba))))
  | rename_locs_sexp f (Andb (a, b)) =
    binda (rename_locs_sexp f a)
      (fn aa => binda (rename_locs_sexp f b) (fn ba => Result (Andb (aa, ba))))
  | rename_locs_sexp f (Loc (n, x)) =
    binda (f n x) (fn xa => Result (Loc (n, xa)))
  | rename_locs_sexp f (Eqb (a, b)) = Result (Eqb (a, b))
  | rename_locs_sexp f (Ltc (a, b)) = Result (Ltc (a, b))
  | rename_locs_sexp f (Leb (a, b)) = Result (Leb (a, b))
  | rename_locs_sexp f (Gea (a, b)) = Result (Gea (a, b))
  | rename_locs_sexp f (Gtb (a, b)) = Result (Gtb (a, b));

fun rename_locs_formula f (EX phi) =
  binda (rename_locs_sexp f phi) (Result o EX)
  | rename_locs_formula f (EG phi) =
    binda (rename_locs_sexp f phi) (Result o EG)
  | rename_locs_formula f (AX phi) =
    binda (rename_locs_sexp f phi) (Result o AX)
  | rename_locs_formula f (AG phi) =
    binda (rename_locs_sexp f phi) (Result o AG)
  | rename_locs_formula f (Leadsto (phi, psi)) =
    binda (rename_locs_sexp f phi)
      (fn phia =>
        binda (rename_locs_sexp f psi)
          (fn psia => Result (Leadsto (phia, psia))));

fun chop_bexp A_ clocks (Anda (a, b)) (cs, es) =
  chop_bexp A_ clocks b (chop_bexp A_ clocks a (cs, es))
  | chop_bexp A_ clocks (Ltb (Var a, Const b)) (cs, es) =
    (if membera A_ clocks a then (LTa (a, b) :: cs, es)
      else (cs, Ltb (Var a, Const b) :: es))
  | chop_bexp A_ clocks (Lea (Var a, Const b)) (cs, es) =
    (if membera A_ clocks a then (LEa (a, b) :: cs, es)
      else (cs, Lea (Var a, Const b) :: es))
  | chop_bexp A_ clocks (Eqa (Var a, Const b)) (cs, es) =
    (if membera A_ clocks a then (EQa (a, b) :: cs, es)
      else (cs, Eqa (Var a, Const b) :: es))
  | chop_bexp A_ clocks (Ge (Var a, Const b)) (cs, es) =
    (if membera A_ clocks a then (GEa (a, b) :: cs, es)
      else (cs, Ge (Var a, Const b) :: es))
  | chop_bexp A_ clocks (Gta (Var a, Const b)) (cs, es) =
    (if membera A_ clocks a then (GTa (a, b) :: cs, es)
      else (cs, Gta (Var a, Const b) :: es))
  | chop_bexp A_ clocks True (cs, es) = (cs, True :: es)
  | chop_bexp A_ clocks (Nota v) (cs, es) = (cs, Nota v :: es)
  | chop_bexp A_ clocks (Ora (v, va)) (cs, es) = (cs, Ora (v, va) :: es)
  | chop_bexp A_ clocks (Imply (v, va)) (cs, es) = (cs, Imply (v, va) :: es)
  | chop_bexp A_ clocks (Eqa (Const vb, va)) (cs, es) =
    (cs, Eqa (Const vb, va) :: es)
  | chop_bexp A_ clocks (Eqa (If_then_else (vb, vc, vd), va)) (cs, es) =
    (cs, Eqa (If_then_else (vb, vc, vd), va) :: es)
  | chop_bexp A_ clocks (Eqa (Binop (vb, vc, vd), va)) (cs, es) =
    (cs, Eqa (Binop (vb, vc, vd), va) :: es)
  | chop_bexp A_ clocks (Eqa (Unop (vb, vc), va)) (cs, es) =
    (cs, Eqa (Unop (vb, vc), va) :: es)
  | chop_bexp A_ clocks (Eqa (v, Var vb)) (cs, es) = (cs, Eqa (v, Var vb) :: es)
  | chop_bexp A_ clocks (Eqa (v, If_then_else (vb, vc, vd))) (cs, es) =
    (cs, Eqa (v, If_then_else (vb, vc, vd)) :: es)
  | chop_bexp A_ clocks (Eqa (v, Binop (vb, vc, vd))) (cs, es) =
    (cs, Eqa (v, Binop (vb, vc, vd)) :: es)
  | chop_bexp A_ clocks (Eqa (v, Unop (vb, vc))) (cs, es) =
    (cs, Eqa (v, Unop (vb, vc)) :: es)
  | chop_bexp A_ clocks (Lea (Const vb, va)) (cs, es) =
    (cs, Lea (Const vb, va) :: es)
  | chop_bexp A_ clocks (Lea (If_then_else (vb, vc, vd), va)) (cs, es) =
    (cs, Lea (If_then_else (vb, vc, vd), va) :: es)
  | chop_bexp A_ clocks (Lea (Binop (vb, vc, vd), va)) (cs, es) =
    (cs, Lea (Binop (vb, vc, vd), va) :: es)
  | chop_bexp A_ clocks (Lea (Unop (vb, vc), va)) (cs, es) =
    (cs, Lea (Unop (vb, vc), va) :: es)
  | chop_bexp A_ clocks (Lea (v, Var vb)) (cs, es) = (cs, Lea (v, Var vb) :: es)
  | chop_bexp A_ clocks (Lea (v, If_then_else (vb, vc, vd))) (cs, es) =
    (cs, Lea (v, If_then_else (vb, vc, vd)) :: es)
  | chop_bexp A_ clocks (Lea (v, Binop (vb, vc, vd))) (cs, es) =
    (cs, Lea (v, Binop (vb, vc, vd)) :: es)
  | chop_bexp A_ clocks (Lea (v, Unop (vb, vc))) (cs, es) =
    (cs, Lea (v, Unop (vb, vc)) :: es)
  | chop_bexp A_ clocks (Ltb (Const vb, va)) (cs, es) =
    (cs, Ltb (Const vb, va) :: es)
  | chop_bexp A_ clocks (Ltb (If_then_else (vb, vc, vd), va)) (cs, es) =
    (cs, Ltb (If_then_else (vb, vc, vd), va) :: es)
  | chop_bexp A_ clocks (Ltb (Binop (vb, vc, vd), va)) (cs, es) =
    (cs, Ltb (Binop (vb, vc, vd), va) :: es)
  | chop_bexp A_ clocks (Ltb (Unop (vb, vc), va)) (cs, es) =
    (cs, Ltb (Unop (vb, vc), va) :: es)
  | chop_bexp A_ clocks (Ltb (v, Var vb)) (cs, es) = (cs, Ltb (v, Var vb) :: es)
  | chop_bexp A_ clocks (Ltb (v, If_then_else (vb, vc, vd))) (cs, es) =
    (cs, Ltb (v, If_then_else (vb, vc, vd)) :: es)
  | chop_bexp A_ clocks (Ltb (v, Binop (vb, vc, vd))) (cs, es) =
    (cs, Ltb (v, Binop (vb, vc, vd)) :: es)
  | chop_bexp A_ clocks (Ltb (v, Unop (vb, vc))) (cs, es) =
    (cs, Ltb (v, Unop (vb, vc)) :: es)
  | chop_bexp A_ clocks (Ge (Const vb, va)) (cs, es) =
    (cs, Ge (Const vb, va) :: es)
  | chop_bexp A_ clocks (Ge (If_then_else (vb, vc, vd), va)) (cs, es) =
    (cs, Ge (If_then_else (vb, vc, vd), va) :: es)
  | chop_bexp A_ clocks (Ge (Binop (vb, vc, vd), va)) (cs, es) =
    (cs, Ge (Binop (vb, vc, vd), va) :: es)
  | chop_bexp A_ clocks (Ge (Unop (vb, vc), va)) (cs, es) =
    (cs, Ge (Unop (vb, vc), va) :: es)
  | chop_bexp A_ clocks (Ge (v, Var vb)) (cs, es) = (cs, Ge (v, Var vb) :: es)
  | chop_bexp A_ clocks (Ge (v, If_then_else (vb, vc, vd))) (cs, es) =
    (cs, Ge (v, If_then_else (vb, vc, vd)) :: es)
  | chop_bexp A_ clocks (Ge (v, Binop (vb, vc, vd))) (cs, es) =
    (cs, Ge (v, Binop (vb, vc, vd)) :: es)
  | chop_bexp A_ clocks (Ge (v, Unop (vb, vc))) (cs, es) =
    (cs, Ge (v, Unop (vb, vc)) :: es)
  | chop_bexp A_ clocks (Gta (Const vb, va)) (cs, es) =
    (cs, Gta (Const vb, va) :: es)
  | chop_bexp A_ clocks (Gta (If_then_else (vb, vc, vd), va)) (cs, es) =
    (cs, Gta (If_then_else (vb, vc, vd), va) :: es)
  | chop_bexp A_ clocks (Gta (Binop (vb, vc, vd), va)) (cs, es) =
    (cs, Gta (Binop (vb, vc, vd), va) :: es)
  | chop_bexp A_ clocks (Gta (Unop (vb, vc), va)) (cs, es) =
    (cs, Gta (Unop (vb, vc), va) :: es)
  | chop_bexp A_ clocks (Gta (v, Var vb)) (cs, es) = (cs, Gta (v, Var vb) :: es)
  | chop_bexp A_ clocks (Gta (v, If_then_else (vb, vc, vd))) (cs, es) =
    (cs, Gta (v, If_then_else (vb, vc, vd)) :: es)
  | chop_bexp A_ clocks (Gta (v, Binop (vb, vc, vd))) (cs, es) =
    (cs, Gta (v, Binop (vb, vc, vd)) :: es)
  | chop_bexp A_ clocks (Gta (v, Unop (vb, vc))) (cs, es) =
    (cs, Gta (v, Unop (vb, vc)) :: es);

fun compile_invariant (A1_, A2_, A3_, A4_, A5_, A6_) B_ clocks vars inv =
  let
    val (cs, es) = chop_bexp A4_ clocks inv ([], []);
  in
    (if null es then Result (cs, True)
      else let
             val b = fold (fn a => fn b => Anda (a, b)) (tla es) (hda es);
           in
             binda (assert
                     (less_eq_set (A1_, A2_, A3_) (set_bexp (A2_, A3_, A5_) b)
                       (set (A2_, A3_, A5_) vars))
                     (implode
                       ([Chara (true, false, true, false, true, false, true,
                                 false),
                          Chara (false, true, true, true, false, true, true,
                                  false),
                          Chara (true, true, false, true, false, true, true,
                                  false),
                          Chara (false, true, true, true, false, true, true,
                                  false),
                          Chara (true, true, true, true, false, true, true,
                                  false),
                          Chara (true, true, true, false, true, true, true,
                                  false),
                          Chara (false, true, true, true, false, true, true,
                                  false),
                          Chara (false, false, false, false, false, true, false,
                                  false),
                          Chara (false, true, true, false, true, true, true,
                                  false),
                          Chara (true, false, false, false, false, true, true,
                                  false),
                          Chara (false, true, false, false, true, true, true,
                                  false),
                          Chara (true, false, false, true, false, true, true,
                                  false),
                          Chara (true, false, false, false, false, true, true,
                                  false),
                          Chara (false, true, false, false, false, true, true,
                                  false),
                          Chara (false, false, true, true, false, true, true,
                                  false),
                          Chara (true, false, true, false, false, true, true,
                                  false),
                          Chara (false, false, false, false, false, true, false,
                                  false),
                          Chara (true, false, false, true, false, true, true,
                                  false),
                          Chara (false, true, true, true, false, true, true,
                                  false),
                          Chara (false, false, false, false, false, true, false,
                                  false),
                          Chara (false, true, false, false, false, true, true,
                                  false),
                          Chara (true, false, true, false, false, true, true,
                                  false),
                          Chara (false, false, false, true, true, true, true,
                                  false),
                          Chara (false, false, false, false, true, true, true,
                                  false),
                          Chara (false, true, false, true, true, true, false,
                                  false),
                          Chara (false, false, false, false, false, true, false,
                                  false)] @
                         shows_prec_bexp A6_ B_ zero_nata b [])))
               (fn _ => Result (cs, b))
           end)
  end;

fun compile_invarianta clocks vars inv =
  (if ((inv : string) = "") then Result ([], True)
    else binda (err_msg ("Failed to parse guard in " ^ inv) (parse scan_7 inv))
           (compile_invariant
             (cenum_literal, ceq_literal, ccompare_literal, equal_literal,
               set_impl_literal, show_literal)
             show_int clocks vars));

fun of_string json =
  (case json of Object _ => Error ["of_array: expected sequence"]
    | Arraya _ => Error ["of_array: expected sequence"]
    | Stringa s => Result (implode s)
    | Int _ => Error ["of_array: expected sequence"]
    | Nata _ => Error ["of_array: expected sequence"]
    | Rat _ => Error ["of_array: expected sequence"]
    | Boolean _ => Error ["of_array: expected sequence"]
    | Null => Error ["of_array: expected sequence"]);

fun of_object json =
  (case json of Object asa => Result (map_of (equal_list equal_char) asa)
    | Arraya _ => Error ["json_to_map: expected object"]
    | Stringa _ => Error ["json_to_map: expected object"]
    | Int _ => Error ["json_to_map: expected object"]
    | Nata _ => Error ["json_to_map: expected object"]
    | Rat _ => Error ["json_to_map: expected object"]
    | Boolean _ => Error ["json_to_map: expected object"]
    | Null => Error ["json_to_map: expected object"]);

fun convert_node clocks vars n =
  binda (of_object n)
    (fn na =>
      binda (binda
              (geta (show_list show_char) na
                [Chara (true, false, false, true, false, true, true, false),
                  Chara (false, false, true, false, false, true, true, false)])
              of_nat)
        (fn id =>
          binda (binda
                  (geta (show_list show_char) na
                    [Chara (false, true, true, true, false, true, true, false),
                      Chara (true, false, false, false, false, true, true,
                              false),
                      Chara (true, false, true, true, false, true, true, false),
                      Chara (true, false, true, false, false, true, true,
                              false)])
                  of_string)
            (fn name =>
              binda (binda
                      (geta (show_list show_char) na
                        [Chara (true, false, false, true, false, true, true,
                                 false),
                          Chara (false, true, true, true, false, true, true,
                                  false),
                          Chara (false, true, true, false, true, true, true,
                                  false),
                          Chara (true, false, false, false, false, true, true,
                                  false),
                          Chara (false, true, false, false, true, true, true,
                                  false),
                          Chara (true, false, false, true, false, true, true,
                                  false),
                          Chara (true, false, false, false, false, true, true,
                                  false),
                          Chara (false, true, true, true, false, true, true,
                                  false),
                          Chara (false, false, true, false, true, true, true,
                                  false)])
                      of_string)
                (fn inv =>
                  binda (err_msg "Failed to parse invariant!"
                          (compile_invarianta clocks vars inv))
                    (fn (inva, inv_vars) =>
                      binda (assert
                              (case inv_vars of True => true | Nota _ => false
                                | Anda (_, _) => false | Ora (_, _) => false
                                | Imply (_, _) => false | Eqa (_, _) => false
                                | Lea (_, _) => false | Ltb (_, _) => false
                                | Ge (_, _) => false | Gta (_, _) => false)
                              "State invariants on nodes are not supported")
                        (fn _ => Result ((name, id), inva)))))));

fun scan_update x =
  bindb (gen_token lx_ws scan_var)
    (fn xa =>
      bindb (gen_token lx_ws
              (bindb
                (alt (exactly (equal_char, show_char)
                       [Chara (true, false, true, true, true, true, false,
                                false)])
                  (exactly (equal_char, show_char)
                    [Chara (false, true, false, true, true, true, false, false),
                      Chara (true, false, true, true, true, true, false,
                              false)]))
                (fn xb => return (sum_join xb))))
        (fn _ => bindb scan_exp (fn xaa => return (implode xa, xaa))))
    x;

fun scan_action x =
  bindb (alt (bindb scan_var
               (fn xa =>
                 bindb (gen_token lx_ws
                         (exactly (equal_char, show_char)
                           [Chara (true, true, true, true, true, true, false,
                                    false)]))
                   (fn _ => return ((In o implode) xa))))
          (bindb
            (alt (bindb scan_var
                   (fn xa =>
                     bindb (gen_token lx_ws
                             (exactly (equal_char, show_char)
                               [Chara (true, false, false, false, false, true,
false, false)]))
                       (fn _ => return ((Out o implode) xa))))
              (bindb scan_var (fn xa => return ((Sil o implode) xa))))
            (fn xa => return (sum_join xa))))
    (fn xa => return (sum_join xa)) x;

fun convert_edge clocks vars e =
  binda (of_object e)
    (fn ea =>
      binda (binda
              (geta (show_list show_char) ea
                [Chara (true, true, false, false, true, true, true, false),
                  Chara (true, true, true, true, false, true, true, false),
                  Chara (true, false, true, false, true, true, true, false),
                  Chara (false, true, false, false, true, true, true, false),
                  Chara (true, true, false, false, false, true, true, false),
                  Chara (true, false, true, false, false, true, true, false)])
              of_nat)
        (fn source =>
          binda (binda
                  (geta (show_list show_char) ea
                    [Chara (false, false, true, false, true, true, true, false),
                      Chara (true, false, false, false, false, true, true,
                              false),
                      Chara (false, true, false, false, true, true, true,
                              false),
                      Chara (true, true, true, false, false, true, true, false),
                      Chara (true, false, true, false, false, true, true,
                              false),
                      Chara (false, false, true, false, true, true, true,
                              false)])
                  of_nat)
            (fn target =>
              binda (binda
                      (geta (show_list show_char) ea
                        [Chara (true, true, true, false, false, true, true,
                                 false),
                          Chara (true, false, true, false, true, true, true,
                                  false),
                          Chara (true, false, false, false, false, true, true,
                                  false),
                          Chara (false, true, false, false, true, true, true,
                                  false),
                          Chara (false, false, true, false, false, true, true,
                                  false)])
                      of_string)
                (fn guard =>
                  binda (binda
                          (geta (show_list show_char) ea
                            [Chara (false, false, true, true, false, true, true,
                                     false),
                              Chara (true, false, false, false, false, true,
                                      true, false),
                              Chara (false, true, false, false, false, true,
                                      true, false),
                              Chara (true, false, true, false, false, true,
                                      true, false),
                              Chara (false, false, true, true, false, true,
                                      true, false)])
                          of_string)
                    (fn label =>
                      binda (binda
                              (geta (show_list show_char) ea
                                [Chara (true, false, true, false, true, true,
 true, false),
                                  Chara (false, false, false, false, true, true,
  true, false),
                                  Chara (false, false, true, false, false, true,
  true, false),
                                  Chara (true, false, false, false, false, true,
  true, false),
                                  Chara (false, false, true, false, true, true,
  true, false),
                                  Chara (true, false, true, false, false, true,
  true, false)])
                              of_string)
                        (fn update =>
                          binda (if ((label : string) = "") then Result (Sil "")
                                  else err_msg
 ("Failed to parse label in " ^ label) (parse scan_action label))
                            (fn labela =>
                              binda (err_msg "Failed to parse guard!"
                                      (compile_invarianta clocks vars guard))
                                (fn (g, check) =>
                                  binda (if ((update : string) = "")
  then Result []
  else err_msg ("Failed to parse update in " ^ update)
         (parse (parse_list scan_update) update))
                                    (fn upd =>
                                      let
val resets = filter (fn x => membera equal_literal clocks (fst x)) upd;
                                      in
binda (assert (list_all (fn (_, Const x) => equal_inta x zero_inta) resets)
        "Clock resets to values different from zero are not supported")
  (fn _ =>
    let
      val resetsa = map fst resets;
      val upds =
        filter (fn x => not (membera equal_literal clocks (fst x))) upd;
    in
      binda (assert (list_all (fn (x, _) => membera equal_literal vars x) upds)
              ("Unknown variable in update: " ^ update))
        (fn _ =>
          Result (source, (check, (g, (labela, (upds, (resetsa, target)))))))
    end)
                                      end)))))))));

fun of_array json =
  (case json of Object _ => Error ["of_array: expected sequence"]
    | Arraya a => Result a | Stringa _ => Error ["of_array: expected sequence"]
    | Int _ => Error ["of_array: expected sequence"]
    | Nata _ => Error ["of_array: expected sequence"]
    | Rat _ => Error ["of_array: expected sequence"]
    | Boolean _ => Error ["of_array: expected sequence"]
    | Null => Error ["of_array: expected sequence"]);

fun defaulta def x = (case x of Result s => s | Error _ => def);

fun convert_automaton clocks vars a =
  binda (binda
          (geta (show_list show_char) a
            [Chara (false, true, true, true, false, true, true, false),
              Chara (true, true, true, true, false, true, true, false),
              Chara (false, false, true, false, false, true, true, false),
              Chara (true, false, true, false, false, true, true, false),
              Chara (true, true, false, false, true, true, true, false)])
          of_array)
    (fn nodes =>
      binda (binda
              (geta (show_list show_char) a
                [Chara (true, false, true, false, false, true, true, false),
                  Chara (false, false, true, false, false, true, true, false),
                  Chara (true, true, true, false, false, true, true, false),
                  Chara (true, false, true, false, false, true, true, false),
                  Chara (true, true, false, false, true, true, true, false)])
              of_array)
        (fn edges =>
          binda (combine_map (convert_node clocks vars) nodes)
            (fn nodesa =>
              let
                val invs = map (fn (aa, b) => let
        val (_, ab) = aa;
      in
        (fn ba => (ab, ba))
      end
        b)
                             nodesa;
                val names_to_ids = map fst nodesa;
              in
                binda (assert
                        (distinct_ds (equal_literal, linorder_literal)
                          (filter (fn s => not ((s : string) = ""))
                            (map fst names_to_ids)))
                        ("Node names are ambiguous" ^
                          implode
                            (shows_prec_list show_literal zero_nata
                              (map fst names_to_ids) [])))
                  (fn _ =>
                    binda (assert
                            (distinct_ds (equal_nat, linorder_nat)
                              (map snd names_to_ids))
                            "Duplicate node id")
                      (fn _ =>
                        let
                          val ids_to_names =
                            map_of equal_nat (map swap names_to_ids);
                          val names_to_idsa = map_of equal_literal names_to_ids;
                          val committed =
                            defaulta []
                              (binda
                                (geta (show_list show_char) a
                                  [Chara (true, true, false, false, false, true,
   true, false),
                                    Chara (true, true, true, true, false, true,
    true, false),
                                    Chara (true, false, true, true, false, true,
    true, false),
                                    Chara (true, false, true, true, false, true,
    true, false),
                                    Chara (true, false, false, true, false,
    true, true, false),
                                    Chara (false, false, true, false, true,
    true, true, false),
                                    Chara (false, false, true, false, true,
    true, true, false),
                                    Chara (true, false, true, false, false,
    true, true, false),
                                    Chara (false, false, true, false, false,
    true, true, false)])
                                of_array);
                        in
                          binda (combine_map of_nat committed)
                            (fn committeda =>
                              let
                                val urgent =
                                  defaulta []
                                    (binda
                                      (geta (show_list show_char) a
[Chara (true, false, true, false, true, true, true, false),
  Chara (false, true, false, false, true, true, true, false),
  Chara (true, true, true, false, false, true, true, false),
  Chara (true, false, true, false, false, true, true, false),
  Chara (false, true, true, true, false, true, true, false),
  Chara (false, false, true, false, true, true, true, false)])
                                      of_array);
                              in
                                binda (combine_map of_nat urgent)
                                  (fn urgenta =>
                                    binda (combine_map
    (convert_edge clocks vars) edges)
                                      (fn edgesa =>
Result
  (names_to_idsa, (ids_to_names, (committeda, (urgenta, (edgesa, invs)))))))
                              end)
                        end))
              end)));

fun scan_acconstraint x =
  let
    val scan =
      (fn s => fn c =>
        bindb (gen_token lx_ws scan_var)
          (fn xa =>
            bindb (gen_token lx_ws (exactly (equal_char, show_char) s))
              (fn _ =>
                bindb (gen_token lx_ws lx_int)
                  (fn xaa => return (c (implode xa) xaa)))));
  in
    bindb (alt (scan [Chara (false, false, true, true, true, true, false,
                              false)]
                 (fn a => fn b => Ltc (a, b)))
            (bindb
              (alt (scan [Chara (false, false, true, true, true, true, false,
                                  false),
                           Chara (true, false, true, true, true, true, false,
                                   false)]
                     (fn a => fn b => Leb (a, b)))
                (bindb
                  (alt (scan [Chara (true, false, true, true, true, true, false,
                                      false),
                               Chara (true, false, true, true, true, true,
                                       false, false)]
                         (fn a => fn b => Eqb (a, b)))
                    (bindb
                      (alt (scan [Chara (true, false, true, true, true, true,
  false, false)]
                             (fn a => fn b => Eqb (a, b)))
                        (bindb
                          (alt (scan [Chara
(false, true, true, true, true, true, false, false),
                                       Chara
 (true, false, true, true, true, true, false, false)]
                                 (fn a => fn b => Gea (a, b)))
                            (scan [Chara (false, true, true, true, true, true,
   false, false)]
                              (fn a => fn b => Gtb (a, b))))
                          (fn xa => return (sum_join xa))))
                      (fn xa => return (sum_join xa))))
                  (fn xa => return (sum_join xa))))
              (fn xa => return (sum_join xa))))
      (fn xa => return (sum_join xa))
  end
    x;

fun scan_loc x =
  bindb (gen_token lx_ws scan_var)
    (fn xa =>
      bindb (exactly (equal_char, show_char)
              [Chara (false, true, true, true, false, true, false, false)])
        (fn _ =>
          bindb scan_var (fn xaa => return (Loc (implode xa, implode xaa)))))
    x;

fun scan_bexp_elem x =
  bindb (alt scan_acconstraint scan_loc) (fn xa => return (sum_join xa)) x;

fun scan_prefix p head =
  bindb (gen_token lx_ws (exactly (equal_char, show_char) head)) (fn _ => p);

fun scan_7a elem imply or anda nota l =
  bindb (alt (bindb
               (scan_infix_pair (scan_6a elem imply or anda nota)
                 (scan_7a elem imply or anda nota)
                 [Chara (true, false, true, true, false, true, false, false),
                   Chara (false, true, true, true, true, true, false, false)])
               (fn x => return (uncurry imply x)))
          (bindb
            (alt (bindb
                   (scan_infix_pair (scan_6a elem imply or anda nota)
                     (scan_7a elem imply or anda nota)
                     [Chara (false, false, true, true, true, true, true, false),
                       Chara (false, false, true, true, true, true, true,
                               false)])
                   (fn x => return (uncurry or x)))
              (scan_6a elem imply or anda nota))
            (fn x => return (sum_join x))))
    (fn x => return (sum_join x)) l
and scan_0a elem imply or anda nota l =
  bindb (alt (bindb
               (gen_token lx_ws
                 (bindb
                   (alt (exactly (equal_char, show_char)
                          [Chara (false, true, true, true, true, true, true,
                                   false)])
                     (exactly (equal_char, show_char)
                       [Chara (true, false, false, false, false, true, false,
                                false)]))
                   (fn x => return (sum_join x))))
               (fn _ =>
                 bindb (scan_parens
                         [Chara (false, false, false, true, false, true, false,
                                  false)]
                         [Chara (true, false, false, true, false, true, false,
                                  false)]
                         (scan_7a elem imply or anda nota))
                   (fn x => return (nota x))))
          (bindb
            (alt elem
              (scan_parens
                [Chara (false, false, false, true, false, true, false, false)]
                [Chara (true, false, false, true, false, true, false, false)]
                (scan_7a elem imply or anda nota)))
            (fn x => return (sum_join x))))
    (fn x => return (sum_join x)) l
and scan_6a elem imply or anda nota l =
  bindb (alt (bindb
               (scan_infix_pair (scan_0a elem imply or anda nota)
                 (scan_6a elem imply or anda nota)
                 [Chara (false, true, true, false, false, true, false, false),
                   Chara (false, true, true, false, false, true, false, false)])
               (fn x => return (uncurry anda x)))
          (scan_0a elem imply or anda nota))
    (fn x => return (sum_join x)) l;

fun scan_formula x =
  bindb (alt (bindb
               (scan_prefix
                 (scan_7a scan_bexp_elem (fn a => fn b => Implya (a, b))
                   (fn a => fn b => Orb (a, b)) (fn a => fn b => Andb (a, b))
                   Notb)
                 [Chara (true, false, true, false, false, false, true, false),
                   Chara (false, false, true, true, true, true, false, false),
                   Chara (false, true, true, true, true, true, false, false)])
               (fn xa => return (EX xa)))
          (bindb
            (alt (bindb
                   (scan_prefix
                     (scan_7a scan_bexp_elem (fn a => fn b => Implya (a, b))
                       (fn a => fn b => Orb (a, b))
                       (fn a => fn b => Andb (a, b)) Notb)
                     [Chara (true, false, true, false, false, false, true,
                              false),
                       Chara (true, true, false, true, true, false, true,
                               false),
                       Chara (true, false, true, true, true, false, true,
                               false)])
                   (fn xa => return (EG xa)))
              (bindb
                (alt (bindb
                       (scan_prefix
                         (scan_7a scan_bexp_elem (fn a => fn b => Implya (a, b))
                           (fn a => fn b => Orb (a, b))
                           (fn a => fn b => Andb (a, b)) Notb)
                         [Chara (true, false, false, false, false, false, true,
                                  false),
                           Chara (false, false, true, true, true, true, false,
                                   false),
                           Chara (false, true, true, true, true, true, false,
                                   false)])
                       (fn xa => return (AX xa)))
                  (bindb
                    (alt (bindb
                           (scan_prefix
                             (scan_7a scan_bexp_elem
                               (fn a => fn b => Implya (a, b))
                               (fn a => fn b => Orb (a, b))
                               (fn a => fn b => Andb (a, b)) Notb)
                             [Chara (true, false, false, false, false, false,
                                      true, false),
                               Chara (true, true, false, true, true, false,
                                       true, false),
                               Chara (true, false, true, true, true, false,
                                       true, false)])
                           (fn xa => return (AG xa)))
                      (bindb
                        (scan_infix_pair
                          (scan_7a scan_bexp_elem
                            (fn a => fn b => Implya (a, b))
                            (fn a => fn b => Orb (a, b))
                            (fn a => fn b => Andb (a, b)) Notb)
                          (scan_7a scan_bexp_elem
                            (fn a => fn b => Implya (a, b))
                            (fn a => fn b => Orb (a, b))
                            (fn a => fn b => Andb (a, b)) Notb)
                          [Chara (true, false, true, true, false, true, false,
                                   false),
                            Chara (true, false, true, true, false, true, false,
                                    false),
                            Chara (false, true, true, true, true, true, false,
                                    false)])
                        (fn xa =>
                          return
                            (uncurry (fn a => fn b => Leadsto (a, b)) xa))))
                    (fn xa => return (sum_join xa))))
                (fn xa => return (sum_join xa))))
            (fn xa => return (sum_join xa))))
    (fn xa => return (sum_join xa)) x;

fun parse_bound x =
  bindb ta_var_ident
    (fn a =>
      bindb (exactly (equal_char, show_char)
              [Chara (true, true, false, true, true, false, true, false)])
        (fn _ =>
          bindb lx_int
            (fn xa =>
              bindb (exactly (equal_char, show_char)
                      [Chara (false, true, false, true, true, true, false,
                               false)])
                (fn _ =>
                  bindb lx_int
                    (fn xaa =>
                      bindb (exactly (equal_char, show_char)
                              [Chara (true, false, true, true, true, false,
                                       true, false)])
                        (fn _ => return (a, (xa, xaa))))))))
    x;

fun parse_bounds x =
  bindb (alt (parse_list
               (bindb lx_ws
                 (fn _ =>
                   bindb parse_bound (fn xa => return let
                val (s, a) = xa;
              in
                (implode s, a)
              end))))
          (bindb lx_ws (fn _ => return [])))
    (fn xa => return (sum_join xa)) x;

fun convert json =
  binda (of_object json)
    (fn all =>
      binda (geta (show_list show_char) all
              [Chara (true, false, false, false, false, true, true, false),
                Chara (true, false, true, false, true, true, true, false),
                Chara (false, false, true, false, true, true, true, false),
                Chara (true, true, true, true, false, true, true, false),
                Chara (true, false, true, true, false, true, true, false),
                Chara (true, false, false, false, false, true, true, false),
                Chara (false, false, true, false, true, true, true, false),
                Chara (true, false, false, false, false, true, true, false)])
        (fn automata =>
          binda (of_array automata)
            (fn automataa =>
              let
                val broadcast =
                  defaulta []
                    (binda
                      (geta (show_list show_char) all
                        [Chara (false, true, false, false, false, true, true,
                                 false),
                          Chara (false, true, false, false, true, true, true,
                                  false),
                          Chara (true, true, true, true, false, true, true,
                                  false),
                          Chara (true, false, false, false, false, true, true,
                                  false),
                          Chara (false, false, true, false, false, true, true,
                                  false),
                          Chara (true, true, false, false, false, true, true,
                                  false),
                          Chara (true, false, false, false, false, true, true,
                                  false),
                          Chara (true, true, false, false, true, true, true,
                                  false),
                          Chara (false, false, true, false, true, true, true,
                                  false)])
                      of_array);
              in
                binda (combine_map of_string broadcast)
                  (fn broadcasta =>
                    let
                      val _ =
                        (fn _ => fn s => writeln (s ())) (Int_of_integer
                   (3 : Int.int)) ((fn _ =>
(fn () =>
  ("Broadcast channels " ^
    implode (shows_prec_list show_literal zero_nata broadcasta [])))) ());
                      val bounds =
                        defaulta ""
                          (binda
                            (geta (show_list show_char) all
                              [Chara (false, true, true, false, true, true,
                                       true, false),
                                Chara (true, false, false, false, false, true,
true, false),
                                Chara (false, true, false, false, true, true,
true, false),
                                Chara (true, true, false, false, true, true,
true, false)])
                            of_string);
                    in
                      binda (err_msg "Failed to parse bounds"
                              (parse parse_bounds bounds))
                        (fn boundsa =>
                          binda (geta (show_list show_char) all
                                  [Chara (true, true, false, false, false, true,
   true, false),
                                    Chara (false, false, true, true, false,
    true, true, false),
                                    Chara (true, true, true, true, false, true,
    true, false),
                                    Chara (true, true, false, false, false,
    true, true, false),
                                    Chara (true, true, false, true, false, true,
    true, false),
                                    Chara (true, true, false, false, true, true,
    true, false)])
                            (fn clocks =>
                              binda (of_string clocks)
                                (fn clocksa =>
                                  binda (err_msg "Failed to parse clocks"
  (parse
    (parse_list
      (bindb lx_ws (fn _ => bindb ta_var_ident (fn x => return (implode x)))))
    clocksa))
                                    (fn clocksb =>
                                      binda
(geta (show_list show_char) all
  [Chara (false, true, true, false, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, true, true, false, true, true, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false)])
(fn formula =>
  binda (of_string formula)
    (fn formulaa =>
      binda (err_msg "Failed to parse formula" (parse scan_formula formulaa))
        (fn formulab =>
          binda (combine_map of_object automataa)
            (fn automatab =>
              binda (combine_map
                      (fn a =>
                        binda (geta (show_list show_char) a
                                [Chara (false, true, true, true, false, true,
 true, false),
                                  Chara (true, false, false, false, false, true,
  true, false),
                                  Chara (true, false, true, true, false, true,
  true, false),
                                  Chara (true, false, true, false, false, true,
  true, false)])
                          of_string)
                      automatab)
                (fn process_names =>
                  binda (assert
                          (distinct_ds (equal_literal, linorder_literal)
                            process_names)
                          "Process names are ambiguous")
                    (fn _ =>
                      binda (assert
                              (less_eq_set
                                (cenum_literal, ceq_literal, ccompare_literal)
                                (locs_of_formula
                                  (ceq_literal, ccompare_literal,
                                    set_impl_literal)
                                  formulab)
                                (set (ceq_literal, ccompare_literal,
                                       set_impl_literal)
                                  process_names))
                              "Unknown process name in formula")
                        (fn _ =>
                          let
                            val process_names_to_index =
                              index equal_literal process_names;
                          in
                            binda (combine_map
                                    (fn a =>
                                      binda
(geta (show_list show_char) a
  [Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false)])
(fn x => binda (of_nat x) Result))
                                    automatab)
                              (fn init_locs =>
                                let
                                  val formulac =
                                    map_formulab process_names_to_index id id id
                                      formulab;
                                  val vars = map fst boundsa;
                                  val init_vars =
                                    map (fn x => (x, zero_inta)) vars;
                                in
                                  binda (combine_map
  (convert_automaton clocksb vars) automatab)
                                    (fn names_automata =>
                                      let
val automatac = map (snd o snd) names_automata;
val names = map fst names_automata;
val ids_to_names = map (fst o snd) names_automata;
val ids_to_namesa =
  (fn p => fn i =>
    (case nth ids_to_names p i
      of NONE => implode (shows_prec_nat zero_nata i []) | SOME n => n));
                                      in
binda (rename_locs_formula (fn i => geta show_literal (nth names i)) formulac)
  (fn formulad =>
    Result
      (ids_to_namesa,
        (process_names_to_index,
          (broadcasta,
            (automatac, (boundsa, (formulad, (init_locs, init_vars))))))))
                                      end)
                                end)
                          end)))))))))))
                    end)
              end)));

fun fw_upd_impl_int n =
  (fn ai => fn bib => fn bia => fn bi =>
    (fn f_ => fn () => f_
      ((mtx_get (heap_DBMEntry heap_int) (suc n) ai (bia, bib)) ()) ())
      (fn xa =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) ai (bib, bi)) ()) ())
          (fn xb =>
            (fn f_ => fn () => f_
              ((mtx_get (heap_DBMEntry heap_int) (suc n) ai (bia, bi)) ()) ())
              (fn x =>
                let
                  val e = dbm_add_int xa xb;
                in
                  (if less_DBMEntry linorder_int e x
                    then mtx_set (heap_DBMEntry heap_int) (suc n) ai (bia, bi) e
                    else (fn () => ai))
                end))));

fun fw_impl_int n =
  imp_for_inta zero_nata (plus_nata n one_nata)
    (fn xb =>
      imp_for_inta zero_nata (plus_nata n one_nata)
        (fn xd =>
          imp_for_inta zero_nata (plus_nata n one_nata)
            (fn xf => fn sigma => fw_upd_impl_int n sigma xb xd xf)));

fun deadlock_checker broadcast bounds automata m num_states num_actions k l_0
  s_0 show_clock show_state =
  let
    val n_ps = size_list automata;
    val k_i =
      Vector.fromList
        (map (Vector.fromList o map (Vector.fromList o map int_of_nat)) k);
    val invs =
      Vector.fromList
        (map (fn i =>
               let
                 val ma =
                   default_map_of equal_nat []
                     (snd (snd (snd (nth automata i))));
                 val mb =
                   Vector.fromList (map ma (upt zero_nata (num_states i)));
               in
                 mb
               end)
          (upt zero_nata n_ps));
    val inv_fun =
      (fn (l, _) =>
        maps (fn i => sub (sub invs i) (nth l i)) (upt zero_nata n_ps));
    val trans_mapa = trans_map automata;
    val trans_i_map =
      (fn i => fn j =>
        map_filter
          (fn a =>
            (case a of (_, (_, (In _, (_, _)))) => NONE
              | (_, (_, (Out _, (_, _)))) => NONE
              | (b, (g, (Sil aa, (ma, l)))) => SOME (b, (g, (aa, (ma, l))))))
          (trans_mapa i j));
    val int_trans_from_loc_impl =
      (fn p => fn l => fn la => fn s =>
        let
          val a = trans_i_map p l;
        in
          map_filter
            (fn (b, (g, (aa, (f, (r, lb))))) =>
              let
                val sa = mk_updsi s f;
              in
                (if bvali (equal_int, linorder_int) s b andalso
                      check_boundedi bounds sa
                  then SOME (g, (Internal aa, (r, (list_update la p lb, sa))))
                  else NONE)
              end)
            a
        end);
    val int_trans_from_vec_impl =
      (fn pairs => fn l => fn s =>
        maps (fn (p, la) => int_trans_from_loc_impl p la l s) pairs);
    val int_trans_from_all_impl =
      (fn l => fn s =>
        maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
          (upt zero_nata n_ps));
    val trans_out_map =
      (fn i => fn j =>
        map_filter
          (fn a =>
            (case a of (_, (_, (In _, (_, _)))) => NONE
              | (b, (g, (Out aa, (ma, l)))) => SOME (b, (g, (aa, (ma, l))))
              | (_, (_, (Sil _, (_, _)))) => NONE))
          (trans_mapa i j));
    val trans_in_map =
      (fn i => fn j =>
        map_filter
          (fn a =>
            (case a
              of (b, (g, (In aa, (ma, l)))) => SOME (b, (g, (aa, (ma, l))))
              | (_, (_, (Out _, (_, _)))) => NONE
              | (_, (_, (Sil _, (_, _)))) => NONE))
          (trans_mapa i j));
    val trans_out_broad_grouped =
      (fn i => fn j =>
        actions_by_statea num_actions
          (map_filter
            (fn a =>
              (case a of (_, (_, (In _, (_, _)))) => NONE
                | (b, (g, (Out aa, (ma, l)))) =>
                  (if membera equal_nat broadcast aa
                    then SOME (b, (g, (aa, (ma, l)))) else NONE)
                | (_, (_, (Sil _, (_, _)))) => NONE))
            (trans_mapa i j)));
    val trans_in_broad_grouped =
      (fn i => fn j =>
        actions_by_statea num_actions
          (map_filter
            (fn a =>
              (case a
                of (b, (g, (In aa, (ma, l)))) =>
                  (if membera equal_nat broadcast aa
                    then SOME (b, (g, (aa, (ma, l)))) else NONE)
                | (_, (_, (Out _, (_, _)))) => NONE
                | (_, (_, (Sil _, (_, _)))) => NONE))
            (trans_mapa i j)));
    val broad_trans_impl =
      (fn (l, s) =>
        let
          val pairs = get_committed broadcast bounds automata l;
          val ina =
            map (fn p => trans_in_broad_grouped p (nth l p))
              (upt zero_nata n_ps);
          val out =
            map (fn p => trans_out_broad_grouped p (nth l p))
              (upt zero_nata n_ps);
          val inb =
            map (map (filter
                       (fn (b, _) => bvali (equal_int, linorder_int) s b)))
              ina;
          val outa =
            map (map (filter
                       (fn (b, _) => bvali (equal_int, linorder_int) s b)))
              out;
        in
          (if null pairs
            then maps (fn a =>
                        maps (fn p =>
                               let
                                 val outs = nth (nth outa p) a;
                               in
                                 (if null outs then []
                                   else let
  val combs = make_combs broadcast bounds automata p a inb;
  val outsa = map (fn aa => (p, aa)) outs;
  val combsa =
    (if null combs then map (fn x => [x]) outsa
      else maps (fn x => map (fn aa => x :: aa) combs) outsa);
  val init = ([], (Broad a, ([], (l, s))));
in
  compute_upds_impl bounds init combsa
end)
                               end)
                          (upt zero_nata n_ps))
                   (upt zero_nata num_actions)
            else maps (fn a =>
                        let
                          val ins_committed =
                            map_filter
                              (fn (p, _) =>
                                (if not (null (nth (nth inb p) a)) then SOME p
                                  else NONE))
                              pairs;
                          val always_committed =
                            less_nat one_nata (size_list ins_committed);
                        in
                          maps (fn p =>
                                 let
                                   val outs = nth (nth outa p) a;
                                 in
                                   (if null outs then []
                                     else (if not always_committed andalso
        ((equal_lista equal_nat ins_committed [p] orelse
           null ins_committed) andalso
          not (list_ex (fn (q, _) => equal_nata q p) pairs))
    then []
    else let
           val combs = make_combs broadcast bounds automata p a inb;
           val outsa = map (fn aa => (p, aa)) outs;
           val combsa =
             (if null combs then map (fn x => [x]) outsa
               else maps (fn x => map (fn aa => x :: aa) combs) outsa);
           val init = ([], (Broad a, ([], (l, s))));
         in
           compute_upds_impl bounds init combsa
         end))
                                 end)
                            (upt zero_nata n_ps)
                        end)
                   (upt zero_nata num_actions))
        end);
    val bin_trans_impl =
      (fn (l, s) =>
        let
          val pairs = get_committed broadcast bounds automata l;
          val ina =
            all_actions_by_state broadcast bounds automata num_actions
              trans_in_map l;
          val out =
            all_actions_by_state broadcast bounds automata num_actions
              trans_out_map l;
        in
          (if null pairs
            then maps (fn a =>
                        pairs_by_action_impl bounds l s (nth out a) (nth ina a))
                   (bin_actions broadcast num_actions)
            else let
                   val in2 =
                     all_actions_from_vec num_actions trans_in_map pairs;
                   val out2 =
                     all_actions_from_vec num_actions trans_out_map pairs;
                 in
                   maps (fn a =>
                          pairs_by_action_impl bounds l s (nth out a)
                            (nth in2 a))
                     (bin_actions broadcast num_actions) @
                     maps (fn a =>
                            pairs_by_action_impl bounds l s (nth out2 a)
                              (nth ina a))
                       (bin_actions broadcast num_actions)
                 end)
        end);
    val int_trans_impl =
      (fn (l, s) =>
        let
          val pairs = get_committed broadcast bounds automata l;
        in
          (if null pairs then int_trans_from_all_impl l s
            else int_trans_from_vec_impl pairs l s)
        end);
    val trans_impl =
      (fn st => int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st);
    val e_op_impl =
      (fn ai => fn bic => fn bib => fn bia => fn bi =>
        (fn f_ => fn () => f_ ((up_canonical_upd_impl_int m bi m) ()) ())
          (fn x =>
            (fn f_ => fn () => f_
              ((imp_nfoldli (inv_fun ai) (fn _ => (fn () => true))
                 (fn aia => fn bid =>
                   (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ())
                     ())
                     (fn xa =>
                       repair_pair_impl_int m xa zero_nata
                         (constraint_clk aia)))
                 x)
              ()) ())
              (fn xa =>
                (fn f_ => fn () => f_ ((check_diag_impl_inta m m xa) ()) ())
                  (fn xaa =>
                    (fn f_ => fn () => f_
                      ((if xaa
                         then mtx_set (heap_DBMEntry heap_int) (suc m) xa
                                (zero_nata, zero_nata) (Lt zero_inta)
                         else imp_nfoldli bib (fn _ => (fn () => true))
                                (fn aia => fn bid =>
                                  (fn f_ => fn () => f_
                                    ((abstra_upd_impl_int m aia bid) ()) ())
                                    (fn xb =>
                                      repair_pair_impl_int m xb zero_nata
(constraint_clk aia)))
                                xa)
                      ()) ())
                      (fn x_a =>
                        (fn f_ => fn () => f_ ((check_diag_impl_inta m m x_a)
                          ()) ())
                          (fn xb =>
                            (fn f_ => fn () => f_
                              ((if xb
                                 then mtx_set (heap_DBMEntry heap_int) (suc m)
x_a (zero_nata, zero_nata) (Lt zero_inta)
                                 else (fn f_ => fn () => f_
((imp_nfoldli bic (fn _ => (fn () => true))
   (fn xc => fn sigma => reset_canonical_upd_impl_int m sigma m xc zero_inta)
   x_a)
()) ())
(imp_nfoldli (inv_fun bia) (fn _ => (fn () => true))
  (fn aia => fn bid =>
    (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
      (fn xc => repair_pair_impl_int m xc zero_nata (constraint_clk aia)))))
                              ()) ())
                              (fn x_b =>
                                (fn f_ => fn () => f_
                                  ((check_diag_impl_inta m m x_b) ()) ())
                                  (fn x_c =>
                                    (if x_c
                                      then mtx_set (heap_DBMEntry heap_int)
     (suc m) x_b (zero_nata, zero_nata) (Lt zero_inta)
                                      else (fn f_ => fn () => f_
     ((norm_upd_impl (linordered_ab_group_add_int, equal_int, heap_int) m x_b
        let
          val (l, _) = bia;
        in
          Vector.fromList
            (map (fn c =>
                   maxa (ceq_int, ccompare_int, lattice_int, linorder_int)
                     (image (ceq_nat, ccompare_nat)
                       (ceq_int, ccompare_int, set_impl_int)
                       (fn i => sub (sub (sub k_i i) (nth l i)) c)
                       (atLeastLessThan
                         (ceq_nat, ccompare_nat, equal_nat, interval_nat,
                           set_impl_nat)
                         zero_nata n_ps)))
              (upt zero_nata (plus_nata m one_nata)))
        end
        m)
     ()) ())
     (fw_impl_int m))))))))));
    val is_start =
      (fn () =>
        (not (op_list_is_empty
               (trans_impl
                 (l_0, map (the o map_of equal_nat s_0)
                         (upt zero_nata (n_vs bounds)))))));
    val key = (fn a => (fn () => a)) o fst;
    val suba =
      (fn ai => fn bi =>
        let
          val (a1, a2) = ai;
          val (a1a, a2a) = bi;
        in
          (if equal_proda (equal_list equal_nat) (equal_list equal_int) a1 a1a
            then dbm_subset_impl
                   (linordered_cancel_ab_monoid_add_int, equal_int, heap_int) m
                   a2 a2a
            else (fn () => false))
        end);
    val copy =
      (fn (a1, a2) =>
        (fn f_ => fn () => f_ ((amtx_copy (heap_DBMEntry heap_int) a2) ()) ())
          (fn x => (fn () => (a1, x))));
    val start =
      (fn f_ => fn () => f_
        ((amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m) (Le zero_inta)) ())
        ())
        (fn x_a =>
          (fn () =>
            ((l_0, map (the o map_of equal_nat s_0)
                     (upt zero_nata (n_vs bounds))),
              x_a)));
    val final = (fn _ => (fn () => false));
    val succs =
      (fn (a1, a2) =>
        imp_nfoldli (trans_impl a1) (fn _ => (fn () => true))
          (fn xc => fn sigma =>
            let
              val (a1a, (_, (a1c, a2c))) = xc;
            in
              (fn f_ => fn () => f_ ((amtx_copy (heap_DBMEntry heap_int) a2) ())
                ())
                (fn x =>
                  (fn f_ => fn () => f_ ((e_op_impl a1 a1c a1a a2c x) ()) ())
                    (fn xa => (fn () => (op_list_prepend (a2c, xa) sigma))))
            end)
          []);
    val empty = (fn (_, a) => check_diag_impl_int m a);
    val p =
      (fn (a1, a2) =>
        (fn f_ => fn () => f_
          (((fn f_ => fn () => f_
              ((imp_nfoldli (trans_impl a1) (fn _ => (fn () => true))
                 (fn xb => fn sigma =>
                   (fn f_ => fn () => f_
                     ((v_dbm_impl
                        (linordered_cancel_ab_monoid_add_int, heap_int) m)
                     ()) ())
                     (fn x =>
                       (fn f_ => fn () => f_
                         ((abstr_FW_impl_int m (inv_fun (snd (snd (snd xb)))) x)
                         ()) ())
                         (fn xa =>
                           (fn f_ => fn () => f_
                             ((pre_reset_list_impl m xa (fst (snd (snd xb))))
                             ()) ())
                             (fn xc =>
                               (fn f_ => fn () => f_
                                 ((abstr_FW_impl_int m (fst xb) xc) ()) ())
                                 (fn xd =>
                                   (fn f_ => fn () => f_
                                     ((abstr_FW_impl_int m (inv_fun a1) xd) ())
                                     ())
                                     (fn xe =>
                                       (fn f_ => fn () => f_
 ((down_impl_int m xe) ()) ())
 (fn x_c => (fn () => (x_c :: sigma)))))))))
                 [])
              ()) ())
             (fn x => dbm_subset_fed_impl m a2 (op_list_rev x)))
          ()) ())
          (fn x => (fn () => (not x))));
    val trace =
      (fn a => fn b =>
        (fn n => fn showmstate => fn showshow_stateclock => fn typ => fn x => ()) show_clock a b);
  in
    (fn f_ => fn () => f_ (is_start ()) ())
      (fn r1 =>
        (if r1
          then (fn f_ => fn () => f_
                 ((check_passed_impl
                    (heap_prod
                      (heap_prod (heap_list heap_nat) (heap_list heap_int))
                      (heap_array (typerep_DBMEntry typerep_int)))
                    (equal_prod (equal_list equal_nat) (equal_list equal_int),
                      hashable_prod (hashable_list hashable_nat)
                        (hashable_list hashable_int),
                      heap_prod (heap_list heap_nat) (heap_list heap_int))
                    succs start final suba empty key copy trace p)
                 ()) ())
                 (fn a => (fn () => a))
          else (fn () => true)))
  end;

fun precond_dc show_clock show_state broadcast bounds automata m num_states
  num_actions k l_0 s_0 formula =
  (if simple_Network_Impl_nat_ceiling_start_state broadcast bounds automata m
        num_states num_actions k l_0 s_0 formula
    then (fn f_ => fn () => f_
           ((deadlock_checker broadcast bounds automata m num_states num_actions
              k l_0 s_0 show_clock show_state)
           ()) ())
           (fn x => (fn () => (SOME x)))
    else (fn () => NONE));

fun reachability_checker broadcast bounds automata m num_states num_actions k
  l_0 s_0 formula show_clock show_state =
  (fn f_ => fn () => f_
    (let
       val key = (fn a => (fn () => a)) o fst;
       val suba =
         (fn ai => fn bi =>
           let
             val (a1, a2) = ai;
             val (a1a, a2a) = bi;
           in
             (if equal_proda (equal_list equal_nat) (equal_list equal_int) a1
                   a1a
               then dbm_subset_impl
                      (linordered_cancel_ab_monoid_add_int, equal_int, heap_int)
                      m a2 a2a
               else (fn () => false))
           end);
       val copy =
         (fn (a1, a2) =>
           (fn f_ => fn () => f_ ((amtx_copy (heap_DBMEntry heap_int) a2) ())
             ())
             (fn x => (fn () => (a1, x))));
       val start =
         (fn f_ => fn () => f_
           ((amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m) (Le zero_inta))
           ()) ())
           (fn x_a =>
             (fn () =>
               ((l_0, map (the o map_of equal_nat s_0)
                        (upt zero_nata (n_vs bounds))),
                 x_a)));
       val final = (fn xi => (fn () => let
 val ((a, b), _) = xi;
                                       in
 hd_of_formulai equal_nat formula a b
                                       end));
       val succs =
         let
           val n_ps = size_list automata;
           val k_i =
             Vector.fromList
               (map (Vector.fromList o map (Vector.fromList o map int_of_nat))
                 k);
           val invs =
             Vector.fromList
               (map (fn i =>
                      let
                        val ma =
                          default_map_of equal_nat []
                            (snd (snd (snd (nth automata i))));
                        val mb =
                          Vector.fromList
                            (map ma (upt zero_nata (num_states i)));
                      in
                        mb
                      end)
                 (upt zero_nata n_ps));
           val inv_fun =
             (fn (l, _) =>
               maps (fn i => sub (sub invs i) (nth l i)) (upt zero_nata n_ps));
           val trans_mapa = trans_map automata;
           val trans_i_map =
             (fn i => fn j =>
               map_filter
                 (fn a =>
                   (case a of (_, (_, (In _, (_, _)))) => NONE
                     | (_, (_, (Out _, (_, _)))) => NONE
                     | (b, (g, (Sil aa, (ma, l)))) =>
                       SOME (b, (g, (aa, (ma, l))))))
                 (trans_mapa i j));
           val int_trans_from_loc_impl =
             (fn p => fn l => fn la => fn s =>
               let
                 val a = trans_i_map p l;
               in
                 map_filter
                   (fn (b, (g, (aa, (f, (r, lb))))) =>
                     let
                       val sa = mk_updsi s f;
                     in
                       (if bvali (equal_int, linorder_int) s b andalso
                             check_boundedi bounds sa
                         then SOME (g, (Internal aa,
 (r, (list_update la p lb, sa))))
                         else NONE)
                     end)
                   a
               end);
           val int_trans_from_vec_impl =
             (fn pairs => fn l => fn s =>
               maps (fn (p, la) => int_trans_from_loc_impl p la l s) pairs);
           val int_trans_from_all_impl =
             (fn l => fn s =>
               maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
                 (upt zero_nata n_ps));
           val trans_out_map =
             (fn i => fn j =>
               map_filter
                 (fn a =>
                   (case a of (_, (_, (In _, (_, _)))) => NONE
                     | (b, (g, (Out aa, (ma, l)))) =>
                       SOME (b, (g, (aa, (ma, l))))
                     | (_, (_, (Sil _, (_, _)))) => NONE))
                 (trans_mapa i j));
           val trans_in_map =
             (fn i => fn j =>
               map_filter
                 (fn a =>
                   (case a
                     of (b, (g, (In aa, (ma, l)))) =>
                       SOME (b, (g, (aa, (ma, l))))
                     | (_, (_, (Out _, (_, _)))) => NONE
                     | (_, (_, (Sil _, (_, _)))) => NONE))
                 (trans_mapa i j));
           val trans_out_broad_grouped =
             (fn i => fn j =>
               actions_by_statea num_actions
                 (map_filter
                   (fn a =>
                     (case a of (_, (_, (In _, (_, _)))) => NONE
                       | (b, (g, (Out aa, (ma, l)))) =>
                         (if membera equal_nat broadcast aa
                           then SOME (b, (g, (aa, (ma, l)))) else NONE)
                       | (_, (_, (Sil _, (_, _)))) => NONE))
                   (trans_mapa i j)));
           val trans_in_broad_grouped =
             (fn i => fn j =>
               actions_by_statea num_actions
                 (map_filter
                   (fn a =>
                     (case a
                       of (b, (g, (In aa, (ma, l)))) =>
                         (if membera equal_nat broadcast aa
                           then SOME (b, (g, (aa, (ma, l)))) else NONE)
                       | (_, (_, (Out _, (_, _)))) => NONE
                       | (_, (_, (Sil _, (_, _)))) => NONE))
                   (trans_mapa i j)));
           val broad_trans_impl =
             (fn (l, s) =>
               let
                 val pairs = get_committed broadcast bounds automata l;
                 val ina =
                   map (fn p => trans_in_broad_grouped p (nth l p))
                     (upt zero_nata n_ps);
                 val out =
                   map (fn p => trans_out_broad_grouped p (nth l p))
                     (upt zero_nata n_ps);
                 val inb =
                   map (map (filter
                              (fn (b, _) =>
                                bvali (equal_int, linorder_int) s b)))
                     ina;
                 val outa =
                   map (map (filter
                              (fn (b, _) =>
                                bvali (equal_int, linorder_int) s b)))
                     out;
               in
                 (if null pairs
                   then maps (fn a =>
                               maps (fn p =>
                                      let
val outs = nth (nth outa p) a;
                                      in
(if null outs then []
  else let
         val combs = make_combs broadcast bounds automata p a inb;
         val outsa = map (fn aa => (p, aa)) outs;
         val combsa =
           (if null combs then map (fn x => [x]) outsa
             else maps (fn x => map (fn aa => x :: aa) combs) outsa);
         val init = ([], (Broad a, ([], (l, s))));
       in
         compute_upds_impl bounds init combsa
       end)
                                      end)
                                 (upt zero_nata n_ps))
                          (upt zero_nata num_actions)
                   else maps (fn a =>
                               let
                                 val ins_committed =
                                   map_filter
                                     (fn (p, _) =>
                                       (if not (null (nth (nth inb p) a))
 then SOME p else NONE))
                                     pairs;
                                 val always_committed =
                                   less_nat one_nata (size_list ins_committed);
                               in
                                 maps (fn p =>
let
  val outs = nth (nth outa p) a;
in
  (if null outs then []
    else (if not always_committed andalso
               ((equal_lista equal_nat ins_committed [p] orelse
                  null ins_committed) andalso
                 not (list_ex (fn (q, _) => equal_nata q p) pairs))
           then []
           else let
                  val combs = make_combs broadcast bounds automata p a inb;
                  val outsa = map (fn aa => (p, aa)) outs;
                  val combsa =
                    (if null combs then map (fn x => [x]) outsa
                      else maps (fn x => map (fn aa => x :: aa) combs) outsa);
                  val init = ([], (Broad a, ([], (l, s))));
                in
                  compute_upds_impl bounds init combsa
                end))
end)
                                   (upt zero_nata n_ps)
                               end)
                          (upt zero_nata num_actions))
               end);
           val bin_trans_impl =
             (fn (l, s) =>
               let
                 val pairs = get_committed broadcast bounds automata l;
                 val ina =
                   all_actions_by_state broadcast bounds automata num_actions
                     trans_in_map l;
                 val out =
                   all_actions_by_state broadcast bounds automata num_actions
                     trans_out_map l;
               in
                 (if null pairs
                   then maps (fn a =>
                               pairs_by_action_impl bounds l s (nth out a)
                                 (nth ina a))
                          (bin_actions broadcast num_actions)
                   else let
                          val in2 =
                            all_actions_from_vec num_actions trans_in_map pairs;
                          val out2 =
                            all_actions_from_vec num_actions trans_out_map
                              pairs;
                        in
                          maps (fn a =>
                                 pairs_by_action_impl bounds l s (nth out a)
                                   (nth in2 a))
                            (bin_actions broadcast num_actions) @
                            maps (fn a =>
                                   pairs_by_action_impl bounds l s (nth out2 a)
                                     (nth ina a))
                              (bin_actions broadcast num_actions)
                        end)
               end);
           val int_trans_impl =
             (fn (l, s) =>
               let
                 val pairs = get_committed broadcast bounds automata l;
               in
                 (if null pairs then int_trans_from_all_impl l s
                   else int_trans_from_vec_impl pairs l s)
               end);
           val trans_impl =
             (fn st =>
               int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st);
           val e_op_impl =
             (fn ai => fn bic => fn bib => fn bia => fn bi =>
               (fn f_ => fn () => f_ ((up_canonical_upd_impl_int m bi m) ()) ())
                 (fn x =>
                   (fn f_ => fn () => f_
                     ((imp_nfoldli (inv_fun ai) (fn _ => (fn () => true))
                        (fn aia => fn bid =>
                          (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid)
                            ()) ())
                            (fn xa =>
                              repair_pair_impl_int m xa zero_nata
                                (constraint_clk aia)))
                        x)
                     ()) ())
                     (fn xa =>
                       (fn f_ => fn () => f_ ((check_diag_impl_inta m m xa) ())
                         ())
                         (fn xaa =>
                           (fn f_ => fn () => f_
                             ((if xaa
                                then mtx_set (heap_DBMEntry heap_int) (suc m) xa
                                       (zero_nata, zero_nata) (Lt zero_inta)
                                else imp_nfoldli bib (fn _ => (fn () => true))
                                       (fn aia => fn bid =>
 (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
   (fn xb => repair_pair_impl_int m xb zero_nata (constraint_clk aia)))
                                       xa)
                             ()) ())
                             (fn x_a =>
                               (fn f_ => fn () => f_
                                 ((check_diag_impl_inta m m x_a) ()) ())
                                 (fn xb =>
                                   (fn f_ => fn () => f_
                                     ((if xb
then mtx_set (heap_DBMEntry heap_int) (suc m) x_a (zero_nata, zero_nata)
       (Lt zero_inta)
else (fn f_ => fn () => f_
       ((imp_nfoldli bic (fn _ => (fn () => true))
          (fn xc => fn sigma =>
            reset_canonical_upd_impl_int m sigma m xc zero_inta)
          x_a)
       ()) ())
       (imp_nfoldli (inv_fun bia) (fn _ => (fn () => true))
         (fn aia => fn bid =>
           (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
             (fn xc =>
               repair_pair_impl_int m xc zero_nata (constraint_clk aia)))))
                                     ()) ())
                                     (fn x_b =>
                                       (fn f_ => fn () => f_
 ((check_diag_impl_inta m m x_b) ()) ())
 (fn x_c =>
   (if x_c
     then mtx_set (heap_DBMEntry heap_int) (suc m) x_b (zero_nata, zero_nata)
            (Lt zero_inta)
     else (fn f_ => fn () => f_
            ((norm_upd_impl (linordered_ab_group_add_int, equal_int, heap_int) m
               x_b let
                     val (l, _) = bia;
                   in
                     Vector.fromList
                       (map (fn c =>
                              maxa (ceq_int, ccompare_int, lattice_int,
                                     linorder_int)
                                (image (ceq_nat, ccompare_nat)
                                  (ceq_int, ccompare_int, set_impl_int)
                                  (fn i => sub (sub (sub k_i i) (nth l i)) c)
                                  (atLeastLessThan
                                    (ceq_nat, ccompare_nat, equal_nat,
                                      interval_nat, set_impl_nat)
                                    zero_nata n_ps)))
                         (upt zero_nata (plus_nata m one_nata)))
                   end
               m)
            ()) ())
            (fw_impl_int m))))))))));
         in
           (fn (a1, a2) =>
             imp_nfoldli (trans_impl a1) (fn _ => (fn () => true))
               (fn xc => fn sigma =>
                 let
                   val (a1a, (_, (a1c, a2c))) = xc;
                 in
                   (fn f_ => fn () => f_
                     ((amtx_copy (heap_DBMEntry heap_int) a2) ()) ())
                     (fn x =>
                       (fn f_ => fn () => f_ ((e_op_impl a1 a1c a1a a2c x) ())
                         ())
                         (fn xa =>
                           (fn () => (op_list_prepend (a2c, xa) sigma))))
                 end)
               [])
         end;
       val empty = (fn (_, a) => check_diag_impl_int m a);
       val trace =
         (fn a => fn b =>
           (fn n => fn showmstate => fn showshow_stateclock => fn typ => fn x => ()) show_clock a b);
     in
       pw_impl
         (heap_prod (heap_prod (heap_list heap_nat) (heap_list heap_int))
           (heap_array (typerep_DBMEntry typerep_int)))
         (equal_prod (equal_list equal_nat) (equal_list equal_int),
           hashable_prod (hashable_list hashable_nat)
             (hashable_list hashable_int),
           heap_prod (heap_list heap_nat) (heap_list heap_int))
         key copy trace suba start final succs empty
     end
    ()) ())
    (fn x =>
      (fn f_ => fn () => f_ ((fn () => ()) ()) ()) (fn _ => (fn () => x)));

fun leadsto_checker broadcast bounds automata m num_states num_actions k l_0 s_0
  formula psi show_clock show_state =
  (fn f_ => fn () => f_
    (let
       val key = (fn a => (fn () => a)) o fst;
       val suba =
         (fn ai => fn bi =>
           let
             val (a1, a2) = ai;
             val (a1a, a2a) = bi;
           in
             (if equal_proda (equal_list equal_nat) (equal_list equal_int) a1
                   a1a
               then dbm_subset_impl
                      (linordered_cancel_ab_monoid_add_int, equal_int, heap_int)
                      m a2 a2a
               else (fn () => false))
           end);
       val copy =
         (fn (a1, a2) =>
           (fn f_ => fn () => f_ ((amtx_copy (heap_DBMEntry heap_int) a2) ())
             ())
             (fn x => (fn () => (a1, x))));
       val start =
         (fn f_ => fn () => f_
           ((amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m) (Le zero_inta))
           ()) ())
           (fn x_a =>
             (fn () =>
               ((l_0, map (the o map_of equal_nat s_0)
                        (upt zero_nata (n_vs bounds))),
                 x_a)));
       val final = (fn xi => (fn () => let
 val ((a, b), _) = xi;
                                       in
 hd_of_formulai equal_nat formula a b
                                       end));
       val finala = (fn xi => (fn () => let
  val ((l, s), _) = xi;
in
  not (check_sexpi equal_nat psi l s)
end));
       val succs =
         (fn xi =>
           (fn f_ => fn () => f_
             ((let
                 val n_ps = size_list automata;
                 val k_i =
                   Vector.fromList
                     (map (Vector.fromList o
                            map (Vector.fromList o map int_of_nat))
                       k);
                 val invs =
                   Vector.fromList
                     (map (fn i =>
                            let
                              val ma =
                                default_map_of equal_nat []
                                  (snd (snd (snd (nth automata i))));
                              val mb =
                                Vector.fromList
                                  (map ma (upt zero_nata (num_states i)));
                            in
                              mb
                            end)
                       (upt zero_nata n_ps));
                 val inv_fun =
                   (fn (l, _) =>
                     maps (fn i => sub (sub invs i) (nth l i))
                       (upt zero_nata n_ps));
                 val trans_mapa = trans_map automata;
                 val trans_i_map =
                   (fn i => fn j =>
                     map_filter
                       (fn a =>
                         (case a of (_, (_, (In _, (_, _)))) => NONE
                           | (_, (_, (Out _, (_, _)))) => NONE
                           | (b, (g, (Sil aa, (ma, l)))) =>
                             SOME (b, (g, (aa, (ma, l))))))
                       (trans_mapa i j));
                 val int_trans_from_loc_impl =
                   (fn p => fn l => fn la => fn s =>
                     let
                       val a = trans_i_map p l;
                     in
                       map_filter
                         (fn (b, (g, (aa, (f, (r, lb))))) =>
                           let
                             val sa = mk_updsi s f;
                           in
                             (if bvali (equal_int, linorder_int) s b andalso
                                   check_boundedi bounds sa
                               then SOME (g,
   (Internal aa, (r, (list_update la p lb, sa))))
                               else NONE)
                           end)
                         a
                     end);
                 val int_trans_from_vec_impl =
                   (fn pairs => fn l => fn s =>
                     maps (fn (p, la) => int_trans_from_loc_impl p la l s)
                       pairs);
                 val int_trans_from_all_impl =
                   (fn l => fn s =>
                     maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
                       (upt zero_nata n_ps));
                 val trans_out_map =
                   (fn i => fn j =>
                     map_filter
                       (fn a =>
                         (case a of (_, (_, (In _, (_, _)))) => NONE
                           | (b, (g, (Out aa, (ma, l)))) =>
                             SOME (b, (g, (aa, (ma, l))))
                           | (_, (_, (Sil _, (_, _)))) => NONE))
                       (trans_mapa i j));
                 val trans_in_map =
                   (fn i => fn j =>
                     map_filter
                       (fn a =>
                         (case a
                           of (b, (g, (In aa, (ma, l)))) =>
                             SOME (b, (g, (aa, (ma, l))))
                           | (_, (_, (Out _, (_, _)))) => NONE
                           | (_, (_, (Sil _, (_, _)))) => NONE))
                       (trans_mapa i j));
                 val trans_out_broad_grouped =
                   (fn i => fn j =>
                     actions_by_statea num_actions
                       (map_filter
                         (fn a =>
                           (case a of (_, (_, (In _, (_, _)))) => NONE
                             | (b, (g, (Out aa, (ma, l)))) =>
                               (if membera equal_nat broadcast aa
                                 then SOME (b, (g, (aa, (ma, l)))) else NONE)
                             | (_, (_, (Sil _, (_, _)))) => NONE))
                         (trans_mapa i j)));
                 val trans_in_broad_grouped =
                   (fn i => fn j =>
                     actions_by_statea num_actions
                       (map_filter
                         (fn a =>
                           (case a
                             of (b, (g, (In aa, (ma, l)))) =>
                               (if membera equal_nat broadcast aa
                                 then SOME (b, (g, (aa, (ma, l)))) else NONE)
                             | (_, (_, (Out _, (_, _)))) => NONE
                             | (_, (_, (Sil _, (_, _)))) => NONE))
                         (trans_mapa i j)));
                 val broad_trans_impl =
                   (fn (l, s) =>
                     let
                       val pairs = get_committed broadcast bounds automata l;
                       val ina =
                         map (fn p => trans_in_broad_grouped p (nth l p))
                           (upt zero_nata n_ps);
                       val out =
                         map (fn p => trans_out_broad_grouped p (nth l p))
                           (upt zero_nata n_ps);
                       val inb =
                         map (map (filter
                                    (fn (b, _) =>
                                      bvali (equal_int, linorder_int) s b)))
                           ina;
                       val outa =
                         map (map (filter
                                    (fn (b, _) =>
                                      bvali (equal_int, linorder_int) s b)))
                           out;
                     in
                       (if null pairs
                         then maps (fn a =>
                                     maps (fn p =>
    let
      val outs = nth (nth outa p) a;
    in
      (if null outs then []
        else let
               val combs = make_combs broadcast bounds automata p a inb;
               val outsa = map (fn aa => (p, aa)) outs;
               val combsa =
                 (if null combs then map (fn x => [x]) outsa
                   else maps (fn x => map (fn aa => x :: aa) combs) outsa);
               val init = ([], (Broad a, ([], (l, s))));
             in
               compute_upds_impl bounds init combsa
             end)
    end)
                                       (upt zero_nata n_ps))
                                (upt zero_nata num_actions)
                         else maps (fn a =>
                                     let
                                       val ins_committed =
 map_filter
   (fn (p, _) => (if not (null (nth (nth inb p) a)) then SOME p else NONE))
   pairs;
                                       val always_committed =
 less_nat one_nata (size_list ins_committed);
                                     in
                                       maps
 (fn p =>
   let
     val outs = nth (nth outa p) a;
   in
     (if null outs then []
       else (if not always_committed andalso
                  ((equal_lista equal_nat ins_committed [p] orelse
                     null ins_committed) andalso
                    not (list_ex (fn (q, _) => equal_nata q p) pairs))
              then []
              else let
                     val combs = make_combs broadcast bounds automata p a inb;
                     val outsa = map (fn aa => (p, aa)) outs;
                     val combsa =
                       (if null combs then map (fn x => [x]) outsa
                         else maps (fn x => map (fn aa => x :: aa) combs)
                                outsa);
                     val init = ([], (Broad a, ([], (l, s))));
                   in
                     compute_upds_impl bounds init combsa
                   end))
   end)
 (upt zero_nata n_ps)
                                     end)
                                (upt zero_nata num_actions))
                     end);
                 val bin_trans_impl =
                   (fn (l, s) =>
                     let
                       val pairs = get_committed broadcast bounds automata l;
                       val ina =
                         all_actions_by_state broadcast bounds automata
                           num_actions trans_in_map l;
                       val out =
                         all_actions_by_state broadcast bounds automata
                           num_actions trans_out_map l;
                     in
                       (if null pairs
                         then maps (fn a =>
                                     pairs_by_action_impl bounds l s (nth out a)
                                       (nth ina a))
                                (bin_actions broadcast num_actions)
                         else let
                                val in2 =
                                  all_actions_from_vec num_actions trans_in_map
                                    pairs;
                                val out2 =
                                  all_actions_from_vec num_actions trans_out_map
                                    pairs;
                              in
                                maps (fn a =>
                                       pairs_by_action_impl bounds l s
 (nth out a) (nth in2 a))
                                  (bin_actions broadcast num_actions) @
                                  maps (fn a =>
 pairs_by_action_impl bounds l s (nth out2 a) (nth ina a))
                                    (bin_actions broadcast num_actions)
                              end)
                     end);
                 val int_trans_impl =
                   (fn (l, s) =>
                     let
                       val pairs = get_committed broadcast bounds automata l;
                     in
                       (if null pairs then int_trans_from_all_impl l s
                         else int_trans_from_vec_impl pairs l s)
                     end);
                 val trans_impl =
                   (fn st =>
                     int_trans_impl st @
                       bin_trans_impl st @ broad_trans_impl st);
                 val e_op_impl =
                   (fn ai => fn bic => fn bib => fn bia => fn bi =>
                     (fn f_ => fn () => f_ ((up_canonical_upd_impl_int m bi m)
                       ()) ())
                       (fn x =>
                         (fn f_ => fn () => f_
                           ((imp_nfoldli (inv_fun ai) (fn _ => (fn () => true))
                              (fn aia => fn bid =>
                                (fn f_ => fn () => f_
                                  ((abstra_upd_impl_int m aia bid) ()) ())
                                  (fn xa =>
                                    repair_pair_impl_int m xa zero_nata
                                      (constraint_clk aia)))
                              x)
                           ()) ())
                           (fn xa =>
                             (fn f_ => fn () => f_
                               ((check_diag_impl_inta m m xa) ()) ())
                               (fn xaa =>
                                 (fn f_ => fn () => f_
                                   ((if xaa
                                      then mtx_set (heap_DBMEntry heap_int)
     (suc m) xa (zero_nata, zero_nata) (Lt zero_inta)
                                      else imp_nfoldli bib
     (fn _ => (fn () => true))
     (fn aia => fn bid =>
       (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
         (fn xb => repair_pair_impl_int m xb zero_nata (constraint_clk aia)))
     xa)
                                   ()) ())
                                   (fn x_a =>
                                     (fn f_ => fn () => f_
                                       ((check_diag_impl_inta m m x_a) ()) ())
                                       (fn xb =>
 (fn f_ => fn () => f_
   ((if xb
      then mtx_set (heap_DBMEntry heap_int) (suc m) x_a (zero_nata, zero_nata)
             (Lt zero_inta)
      else (fn f_ => fn () => f_
             ((imp_nfoldli bic (fn _ => (fn () => true))
                (fn xc => fn sigma =>
                  reset_canonical_upd_impl_int m sigma m xc zero_inta)
                x_a)
             ()) ())
             (imp_nfoldli (inv_fun bia) (fn _ => (fn () => true))
               (fn aia => fn bid =>
                 (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
                   (fn xc =>
                     repair_pair_impl_int m xc zero_nata
                       (constraint_clk aia)))))
   ()) ())
   (fn x_b =>
     (fn f_ => fn () => f_ ((check_diag_impl_inta m m x_b) ()) ())
       (fn x_c =>
         (if x_c
           then mtx_set (heap_DBMEntry heap_int) (suc m) x_b
                  (zero_nata, zero_nata) (Lt zero_inta)
           else (fn f_ => fn () => f_
                  ((norm_upd_impl
                     (linordered_ab_group_add_int, equal_int, heap_int) m x_b
                     let
                       val (l, _) = bia;
                     in
                       Vector.fromList
                         (map (fn c =>
                                maxa (ceq_int, ccompare_int, lattice_int,
                                       linorder_int)
                                  (image (ceq_nat, ccompare_nat)
                                    (ceq_int, ccompare_int, set_impl_int)
                                    (fn i => sub (sub (sub k_i i) (nth l i)) c)
                                    (atLeastLessThan
                                      (ceq_nat, ccompare_nat, equal_nat,
interval_nat, set_impl_nat)
                                      zero_nata n_ps)))
                           (upt zero_nata (plus_nata m one_nata)))
                     end
                     m)
                  ()) ())
                  (fw_impl_int m))))))))));
               in
                 (fn (a1, a2) =>
                   imp_nfoldli (trans_impl a1) (fn _ => (fn () => true))
                     (fn xc => fn sigma =>
                       let
                         val (a1a, (_, (a1c, a2c))) = xc;
                       in
                         (if let
                               val (l, s) = a2c;
                             in
                               not (check_sexpi equal_nat psi l s)
                             end
                           then (fn f_ => fn () => f_
                                  ((amtx_copy (heap_DBMEntry heap_int) a2) ())
                                  ())
                                  (fn x =>
                                    (fn f_ => fn () => f_
                                      ((e_op_impl a1 a1c a1a a2c x) ()) ())
                                      (fn xa =>
(fn () => (op_list_prepend (a2c, xa) sigma))))
                           else (fn () => sigma))
                       end)
                     [])
               end
                xi)
             ()) ())
             (fn x =>
               (fn f_ => fn () => f_
                 ((imp_nfoldli x (fn _ => (fn () => true))
                    (fn xc => fn sigma =>
                      (fn f_ => fn () => f_
                        (let
                           val (_, a2) = xc;
                         in
                           (fn f_ => fn () => f_ ((check_diag_impl_int m a2) ())
                             ())
                             (fn x_c => (fn () => (not x_c)))
                         end
                        ()) ())
                        (fn x_c =>
                          (fn () =>
                            (if x_c then op_list_prepend xc sigma else sigma))))
                    [])
                 ()) ())
                 (fn xa => (fn () => (op_list_rev xa)))));
       val succsa =
         (fn xi =>
           (fn f_ => fn () => f_
             ((let
                 val n_ps = size_list automata;
                 val k_i =
                   Vector.fromList
                     (map (Vector.fromList o
                            map (Vector.fromList o map int_of_nat))
                       k);
                 val invs =
                   Vector.fromList
                     (map (fn i =>
                            let
                              val ma =
                                default_map_of equal_nat []
                                  (snd (snd (snd (nth automata i))));
                              val mb =
                                Vector.fromList
                                  (map ma (upt zero_nata (num_states i)));
                            in
                              mb
                            end)
                       (upt zero_nata n_ps));
                 val inv_fun =
                   (fn (l, _) =>
                     maps (fn i => sub (sub invs i) (nth l i))
                       (upt zero_nata n_ps));
                 val trans_mapa = trans_map automata;
                 val trans_i_map =
                   (fn i => fn j =>
                     map_filter
                       (fn a =>
                         (case a of (_, (_, (In _, (_, _)))) => NONE
                           | (_, (_, (Out _, (_, _)))) => NONE
                           | (b, (g, (Sil aa, (ma, l)))) =>
                             SOME (b, (g, (aa, (ma, l))))))
                       (trans_mapa i j));
                 val int_trans_from_loc_impl =
                   (fn p => fn l => fn la => fn s =>
                     let
                       val a = trans_i_map p l;
                     in
                       map_filter
                         (fn (b, (g, (aa, (f, (r, lb))))) =>
                           let
                             val sa = mk_updsi s f;
                           in
                             (if bvali (equal_int, linorder_int) s b andalso
                                   check_boundedi bounds sa
                               then SOME (g,
   (Internal aa, (r, (list_update la p lb, sa))))
                               else NONE)
                           end)
                         a
                     end);
                 val int_trans_from_vec_impl =
                   (fn pairs => fn l => fn s =>
                     maps (fn (p, la) => int_trans_from_loc_impl p la l s)
                       pairs);
                 val int_trans_from_all_impl =
                   (fn l => fn s =>
                     maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
                       (upt zero_nata n_ps));
                 val trans_out_map =
                   (fn i => fn j =>
                     map_filter
                       (fn a =>
                         (case a of (_, (_, (In _, (_, _)))) => NONE
                           | (b, (g, (Out aa, (ma, l)))) =>
                             SOME (b, (g, (aa, (ma, l))))
                           | (_, (_, (Sil _, (_, _)))) => NONE))
                       (trans_mapa i j));
                 val trans_in_map =
                   (fn i => fn j =>
                     map_filter
                       (fn a =>
                         (case a
                           of (b, (g, (In aa, (ma, l)))) =>
                             SOME (b, (g, (aa, (ma, l))))
                           | (_, (_, (Out _, (_, _)))) => NONE
                           | (_, (_, (Sil _, (_, _)))) => NONE))
                       (trans_mapa i j));
                 val trans_out_broad_grouped =
                   (fn i => fn j =>
                     actions_by_statea num_actions
                       (map_filter
                         (fn a =>
                           (case a of (_, (_, (In _, (_, _)))) => NONE
                             | (b, (g, (Out aa, (ma, l)))) =>
                               (if membera equal_nat broadcast aa
                                 then SOME (b, (g, (aa, (ma, l)))) else NONE)
                             | (_, (_, (Sil _, (_, _)))) => NONE))
                         (trans_mapa i j)));
                 val trans_in_broad_grouped =
                   (fn i => fn j =>
                     actions_by_statea num_actions
                       (map_filter
                         (fn a =>
                           (case a
                             of (b, (g, (In aa, (ma, l)))) =>
                               (if membera equal_nat broadcast aa
                                 then SOME (b, (g, (aa, (ma, l)))) else NONE)
                             | (_, (_, (Out _, (_, _)))) => NONE
                             | (_, (_, (Sil _, (_, _)))) => NONE))
                         (trans_mapa i j)));
                 val broad_trans_impl =
                   (fn (l, s) =>
                     let
                       val pairs = get_committed broadcast bounds automata l;
                       val ina =
                         map (fn p => trans_in_broad_grouped p (nth l p))
                           (upt zero_nata n_ps);
                       val out =
                         map (fn p => trans_out_broad_grouped p (nth l p))
                           (upt zero_nata n_ps);
                       val inb =
                         map (map (filter
                                    (fn (b, _) =>
                                      bvali (equal_int, linorder_int) s b)))
                           ina;
                       val outa =
                         map (map (filter
                                    (fn (b, _) =>
                                      bvali (equal_int, linorder_int) s b)))
                           out;
                     in
                       (if null pairs
                         then maps (fn a =>
                                     maps (fn p =>
    let
      val outs = nth (nth outa p) a;
    in
      (if null outs then []
        else let
               val combs = make_combs broadcast bounds automata p a inb;
               val outsa = map (fn aa => (p, aa)) outs;
               val combsa =
                 (if null combs then map (fn x => [x]) outsa
                   else maps (fn x => map (fn aa => x :: aa) combs) outsa);
               val init = ([], (Broad a, ([], (l, s))));
             in
               compute_upds_impl bounds init combsa
             end)
    end)
                                       (upt zero_nata n_ps))
                                (upt zero_nata num_actions)
                         else maps (fn a =>
                                     let
                                       val ins_committed =
 map_filter
   (fn (p, _) => (if not (null (nth (nth inb p) a)) then SOME p else NONE))
   pairs;
                                       val always_committed =
 less_nat one_nata (size_list ins_committed);
                                     in
                                       maps
 (fn p =>
   let
     val outs = nth (nth outa p) a;
   in
     (if null outs then []
       else (if not always_committed andalso
                  ((equal_lista equal_nat ins_committed [p] orelse
                     null ins_committed) andalso
                    not (list_ex (fn (q, _) => equal_nata q p) pairs))
              then []
              else let
                     val combs = make_combs broadcast bounds automata p a inb;
                     val outsa = map (fn aa => (p, aa)) outs;
                     val combsa =
                       (if null combs then map (fn x => [x]) outsa
                         else maps (fn x => map (fn aa => x :: aa) combs)
                                outsa);
                     val init = ([], (Broad a, ([], (l, s))));
                   in
                     compute_upds_impl bounds init combsa
                   end))
   end)
 (upt zero_nata n_ps)
                                     end)
                                (upt zero_nata num_actions))
                     end);
                 val bin_trans_impl =
                   (fn (l, s) =>
                     let
                       val pairs = get_committed broadcast bounds automata l;
                       val ina =
                         all_actions_by_state broadcast bounds automata
                           num_actions trans_in_map l;
                       val out =
                         all_actions_by_state broadcast bounds automata
                           num_actions trans_out_map l;
                     in
                       (if null pairs
                         then maps (fn a =>
                                     pairs_by_action_impl bounds l s (nth out a)
                                       (nth ina a))
                                (bin_actions broadcast num_actions)
                         else let
                                val in2 =
                                  all_actions_from_vec num_actions trans_in_map
                                    pairs;
                                val out2 =
                                  all_actions_from_vec num_actions trans_out_map
                                    pairs;
                              in
                                maps (fn a =>
                                       pairs_by_action_impl bounds l s
 (nth out a) (nth in2 a))
                                  (bin_actions broadcast num_actions) @
                                  maps (fn a =>
 pairs_by_action_impl bounds l s (nth out2 a) (nth ina a))
                                    (bin_actions broadcast num_actions)
                              end)
                     end);
                 val int_trans_impl =
                   (fn (l, s) =>
                     let
                       val pairs = get_committed broadcast bounds automata l;
                     in
                       (if null pairs then int_trans_from_all_impl l s
                         else int_trans_from_vec_impl pairs l s)
                     end);
                 val trans_impl =
                   (fn st =>
                     int_trans_impl st @
                       bin_trans_impl st @ broad_trans_impl st);
                 val e_op_impl =
                   (fn ai => fn bic => fn bib => fn bia => fn bi =>
                     (fn f_ => fn () => f_ ((up_canonical_upd_impl_int m bi m)
                       ()) ())
                       (fn x =>
                         (fn f_ => fn () => f_
                           ((imp_nfoldli (inv_fun ai) (fn _ => (fn () => true))
                              (fn aia => fn bid =>
                                (fn f_ => fn () => f_
                                  ((abstra_upd_impl_int m aia bid) ()) ())
                                  (fn xa =>
                                    repair_pair_impl_int m xa zero_nata
                                      (constraint_clk aia)))
                              x)
                           ()) ())
                           (fn xa =>
                             (fn f_ => fn () => f_
                               ((check_diag_impl_inta m m xa) ()) ())
                               (fn xaa =>
                                 (fn f_ => fn () => f_
                                   ((if xaa
                                      then mtx_set (heap_DBMEntry heap_int)
     (suc m) xa (zero_nata, zero_nata) (Lt zero_inta)
                                      else imp_nfoldli bib
     (fn _ => (fn () => true))
     (fn aia => fn bid =>
       (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
         (fn xb => repair_pair_impl_int m xb zero_nata (constraint_clk aia)))
     xa)
                                   ()) ())
                                   (fn x_a =>
                                     (fn f_ => fn () => f_
                                       ((check_diag_impl_inta m m x_a) ()) ())
                                       (fn xb =>
 (fn f_ => fn () => f_
   ((if xb
      then mtx_set (heap_DBMEntry heap_int) (suc m) x_a (zero_nata, zero_nata)
             (Lt zero_inta)
      else (fn f_ => fn () => f_
             ((imp_nfoldli bic (fn _ => (fn () => true))
                (fn xc => fn sigma =>
                  reset_canonical_upd_impl_int m sigma m xc zero_inta)
                x_a)
             ()) ())
             (imp_nfoldli (inv_fun bia) (fn _ => (fn () => true))
               (fn aia => fn bid =>
                 (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
                   (fn xc =>
                     repair_pair_impl_int m xc zero_nata
                       (constraint_clk aia)))))
   ()) ())
   (fn x_b =>
     (fn f_ => fn () => f_ ((check_diag_impl_inta m m x_b) ()) ())
       (fn x_c =>
         (if x_c
           then mtx_set (heap_DBMEntry heap_int) (suc m) x_b
                  (zero_nata, zero_nata) (Lt zero_inta)
           else (fn f_ => fn () => f_
                  ((norm_upd_impl
                     (linordered_ab_group_add_int, equal_int, heap_int) m x_b
                     let
                       val (l, _) = bia;
                     in
                       Vector.fromList
                         (map (fn c =>
                                maxa (ceq_int, ccompare_int, lattice_int,
                                       linorder_int)
                                  (image (ceq_nat, ccompare_nat)
                                    (ceq_int, ccompare_int, set_impl_int)
                                    (fn i => sub (sub (sub k_i i) (nth l i)) c)
                                    (atLeastLessThan
                                      (ceq_nat, ccompare_nat, equal_nat,
interval_nat, set_impl_nat)
                                      zero_nata n_ps)))
                           (upt zero_nata (plus_nata m one_nata)))
                     end
                     m)
                  ()) ())
                  (fw_impl_int m))))))))));
               in
                 (fn (a1, a2) =>
                   imp_nfoldli (trans_impl a1) (fn _ => (fn () => true))
                     (fn xc => fn sigma =>
                       let
                         val (a1a, (_, (a1c, a2c))) = xc;
                       in
                         (fn f_ => fn () => f_
                           ((amtx_copy (heap_DBMEntry heap_int) a2) ()) ())
                           (fn x =>
                             (fn f_ => fn () => f_ ((e_op_impl a1 a1c a1a a2c x)
                               ()) ())
                               (fn xa =>
                                 (fn () => (op_list_prepend (a2c, xa) sigma))))
                       end)
                     [])
               end
                xi)
             ()) ())
             (fn x =>
               (fn f_ => fn () => f_
                 ((imp_nfoldli x (fn _ => (fn () => true))
                    (fn xc => fn sigma =>
                      (fn f_ => fn () => f_
                        (let
                           val (_, a2) = xc;
                         in
                           (fn f_ => fn () => f_ ((check_diag_impl_int m a2) ())
                             ())
                             (fn x_c => (fn () => (not x_c)))
                         end
                        ()) ())
                        (fn x_c =>
                          (fn () =>
                            (if x_c then op_list_prepend xc sigma else sigma))))
                    [])
                 ()) ())
                 (fn xa => (fn () => (op_list_rev xa)))));
       val empty = (fn (_, a) => check_diag_impl_int m a);
       val a =
         (fn a => fn b =>
           (fn n => fn showmstate => fn showshow_stateclock => fn typ => fn x => ()) show_clock a b);
     in
       leadsto_impl
         (heap_prod (heap_prod (heap_list heap_nat) (heap_list heap_int))
           (heap_array (typerep_DBMEntry typerep_int)))
         (equal_prod (equal_list equal_nat) (equal_list equal_int),
           hashable_prod (hashable_list hashable_nat)
             (hashable_list hashable_int),
           heap_prod (heap_list heap_nat) (heap_list heap_int))
         copy succs start suba key succsa empty final finala a
     end
    ()) ())
    (fn r => (fn () => (not r)));

fun alw_ev_checker broadcast bounds automata m num_states num_actions k l_0 s_0
  formula =
  (fn f_ => fn () => f_
    (let
       val key = (fn a => (fn () => a)) o fst;
       val suba =
         (fn ai => fn bi =>
           let
             val (a1, a2) = ai;
             val (a1a, a2a) = bi;
           in
             (if equal_proda (equal_list equal_nat) (equal_list equal_int) a1
                   a1a
               then dbm_subset_impl
                      (linordered_cancel_ab_monoid_add_int, equal_int, heap_int)
                      m a2 a2a
               else (fn () => false))
           end);
       val copy =
         (fn (a1, a2) =>
           (fn f_ => fn () => f_ ((amtx_copy (heap_DBMEntry heap_int) a2) ())
             ())
             (fn x => (fn () => (a1, x))));
       val start =
         (fn f_ => fn () => f_
           ((amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m) (Le zero_inta))
           ()) ())
           (fn x_a =>
             (fn () =>
               ((l_0, map (the o map_of equal_nat s_0)
                        (upt zero_nata (n_vs bounds))),
                 x_a)));
       val succs =
         (fn xi =>
           (fn f_ => fn () => f_
             ((let
                 val n_ps = size_list automata;
                 val k_i =
                   Vector.fromList
                     (map (Vector.fromList o
                            map (Vector.fromList o map int_of_nat))
                       k);
                 val invs =
                   Vector.fromList
                     (map (fn i =>
                            let
                              val ma =
                                default_map_of equal_nat []
                                  (snd (snd (snd (nth automata i))));
                              val mb =
                                Vector.fromList
                                  (map ma (upt zero_nata (num_states i)));
                            in
                              mb
                            end)
                       (upt zero_nata n_ps));
                 val inv_fun =
                   (fn (l, _) =>
                     maps (fn i => sub (sub invs i) (nth l i))
                       (upt zero_nata n_ps));
                 val trans_mapa = trans_map automata;
                 val trans_i_map =
                   (fn i => fn j =>
                     map_filter
                       (fn a =>
                         (case a of (_, (_, (In _, (_, _)))) => NONE
                           | (_, (_, (Out _, (_, _)))) => NONE
                           | (b, (g, (Sil aa, (ma, l)))) =>
                             SOME (b, (g, (aa, (ma, l))))))
                       (trans_mapa i j));
                 val int_trans_from_loc_impl =
                   (fn p => fn l => fn la => fn s =>
                     let
                       val a = trans_i_map p l;
                     in
                       map_filter
                         (fn (b, (g, (aa, (f, (r, lb))))) =>
                           let
                             val sa = mk_updsi s f;
                           in
                             (if bvali (equal_int, linorder_int) s b andalso
                                   check_boundedi bounds sa
                               then SOME (g,
   (Internal aa, (r, (list_update la p lb, sa))))
                               else NONE)
                           end)
                         a
                     end);
                 val int_trans_from_vec_impl =
                   (fn pairs => fn l => fn s =>
                     maps (fn (p, la) => int_trans_from_loc_impl p la l s)
                       pairs);
                 val int_trans_from_all_impl =
                   (fn l => fn s =>
                     maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
                       (upt zero_nata n_ps));
                 val trans_out_map =
                   (fn i => fn j =>
                     map_filter
                       (fn a =>
                         (case a of (_, (_, (In _, (_, _)))) => NONE
                           | (b, (g, (Out aa, (ma, l)))) =>
                             SOME (b, (g, (aa, (ma, l))))
                           | (_, (_, (Sil _, (_, _)))) => NONE))
                       (trans_mapa i j));
                 val trans_in_map =
                   (fn i => fn j =>
                     map_filter
                       (fn a =>
                         (case a
                           of (b, (g, (In aa, (ma, l)))) =>
                             SOME (b, (g, (aa, (ma, l))))
                           | (_, (_, (Out _, (_, _)))) => NONE
                           | (_, (_, (Sil _, (_, _)))) => NONE))
                       (trans_mapa i j));
                 val trans_out_broad_grouped =
                   (fn i => fn j =>
                     actions_by_statea num_actions
                       (map_filter
                         (fn a =>
                           (case a of (_, (_, (In _, (_, _)))) => NONE
                             | (b, (g, (Out aa, (ma, l)))) =>
                               (if membera equal_nat broadcast aa
                                 then SOME (b, (g, (aa, (ma, l)))) else NONE)
                             | (_, (_, (Sil _, (_, _)))) => NONE))
                         (trans_mapa i j)));
                 val trans_in_broad_grouped =
                   (fn i => fn j =>
                     actions_by_statea num_actions
                       (map_filter
                         (fn a =>
                           (case a
                             of (b, (g, (In aa, (ma, l)))) =>
                               (if membera equal_nat broadcast aa
                                 then SOME (b, (g, (aa, (ma, l)))) else NONE)
                             | (_, (_, (Out _, (_, _)))) => NONE
                             | (_, (_, (Sil _, (_, _)))) => NONE))
                         (trans_mapa i j)));
                 val broad_trans_impl =
                   (fn (l, s) =>
                     let
                       val pairs = get_committed broadcast bounds automata l;
                       val ina =
                         map (fn p => trans_in_broad_grouped p (nth l p))
                           (upt zero_nata n_ps);
                       val out =
                         map (fn p => trans_out_broad_grouped p (nth l p))
                           (upt zero_nata n_ps);
                       val inb =
                         map (map (filter
                                    (fn (b, _) =>
                                      bvali (equal_int, linorder_int) s b)))
                           ina;
                       val outa =
                         map (map (filter
                                    (fn (b, _) =>
                                      bvali (equal_int, linorder_int) s b)))
                           out;
                     in
                       (if null pairs
                         then maps (fn a =>
                                     maps (fn p =>
    let
      val outs = nth (nth outa p) a;
    in
      (if null outs then []
        else let
               val combs = make_combs broadcast bounds automata p a inb;
               val outsa = map (fn aa => (p, aa)) outs;
               val combsa =
                 (if null combs then map (fn x => [x]) outsa
                   else maps (fn x => map (fn aa => x :: aa) combs) outsa);
               val init = ([], (Broad a, ([], (l, s))));
             in
               compute_upds_impl bounds init combsa
             end)
    end)
                                       (upt zero_nata n_ps))
                                (upt zero_nata num_actions)
                         else maps (fn a =>
                                     let
                                       val ins_committed =
 map_filter
   (fn (p, _) => (if not (null (nth (nth inb p) a)) then SOME p else NONE))
   pairs;
                                       val always_committed =
 less_nat one_nata (size_list ins_committed);
                                     in
                                       maps
 (fn p =>
   let
     val outs = nth (nth outa p) a;
   in
     (if null outs then []
       else (if not always_committed andalso
                  ((equal_lista equal_nat ins_committed [p] orelse
                     null ins_committed) andalso
                    not (list_ex (fn (q, _) => equal_nata q p) pairs))
              then []
              else let
                     val combs = make_combs broadcast bounds automata p a inb;
                     val outsa = map (fn aa => (p, aa)) outs;
                     val combsa =
                       (if null combs then map (fn x => [x]) outsa
                         else maps (fn x => map (fn aa => x :: aa) combs)
                                outsa);
                     val init = ([], (Broad a, ([], (l, s))));
                   in
                     compute_upds_impl bounds init combsa
                   end))
   end)
 (upt zero_nata n_ps)
                                     end)
                                (upt zero_nata num_actions))
                     end);
                 val bin_trans_impl =
                   (fn (l, s) =>
                     let
                       val pairs = get_committed broadcast bounds automata l;
                       val ina =
                         all_actions_by_state broadcast bounds automata
                           num_actions trans_in_map l;
                       val out =
                         all_actions_by_state broadcast bounds automata
                           num_actions trans_out_map l;
                     in
                       (if null pairs
                         then maps (fn a =>
                                     pairs_by_action_impl bounds l s (nth out a)
                                       (nth ina a))
                                (bin_actions broadcast num_actions)
                         else let
                                val in2 =
                                  all_actions_from_vec num_actions trans_in_map
                                    pairs;
                                val out2 =
                                  all_actions_from_vec num_actions trans_out_map
                                    pairs;
                              in
                                maps (fn a =>
                                       pairs_by_action_impl bounds l s
 (nth out a) (nth in2 a))
                                  (bin_actions broadcast num_actions) @
                                  maps (fn a =>
 pairs_by_action_impl bounds l s (nth out2 a) (nth ina a))
                                    (bin_actions broadcast num_actions)
                              end)
                     end);
                 val int_trans_impl =
                   (fn (l, s) =>
                     let
                       val pairs = get_committed broadcast bounds automata l;
                     in
                       (if null pairs then int_trans_from_all_impl l s
                         else int_trans_from_vec_impl pairs l s)
                     end);
                 val trans_impl =
                   (fn st =>
                     int_trans_impl st @
                       bin_trans_impl st @ broad_trans_impl st);
                 val e_op_impl =
                   (fn ai => fn bic => fn bib => fn bia => fn bi =>
                     (fn f_ => fn () => f_ ((up_canonical_upd_impl_int m bi m)
                       ()) ())
                       (fn x =>
                         (fn f_ => fn () => f_
                           ((imp_nfoldli (inv_fun ai) (fn _ => (fn () => true))
                              (fn aia => fn bid =>
                                (fn f_ => fn () => f_
                                  ((abstra_upd_impl_int m aia bid) ()) ())
                                  (fn xa =>
                                    repair_pair_impl_int m xa zero_nata
                                      (constraint_clk aia)))
                              x)
                           ()) ())
                           (fn xa =>
                             (fn f_ => fn () => f_
                               ((check_diag_impl_inta m m xa) ()) ())
                               (fn xaa =>
                                 (fn f_ => fn () => f_
                                   ((if xaa
                                      then mtx_set (heap_DBMEntry heap_int)
     (suc m) xa (zero_nata, zero_nata) (Lt zero_inta)
                                      else imp_nfoldli bib
     (fn _ => (fn () => true))
     (fn aia => fn bid =>
       (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
         (fn xb => repair_pair_impl_int m xb zero_nata (constraint_clk aia)))
     xa)
                                   ()) ())
                                   (fn x_a =>
                                     (fn f_ => fn () => f_
                                       ((check_diag_impl_inta m m x_a) ()) ())
                                       (fn xb =>
 (fn f_ => fn () => f_
   ((if xb
      then mtx_set (heap_DBMEntry heap_int) (suc m) x_a (zero_nata, zero_nata)
             (Lt zero_inta)
      else (fn f_ => fn () => f_
             ((imp_nfoldli bic (fn _ => (fn () => true))
                (fn xc => fn sigma =>
                  reset_canonical_upd_impl_int m sigma m xc zero_inta)
                x_a)
             ()) ())
             (imp_nfoldli (inv_fun bia) (fn _ => (fn () => true))
               (fn aia => fn bid =>
                 (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
                   (fn xc =>
                     repair_pair_impl_int m xc zero_nata
                       (constraint_clk aia)))))
   ()) ())
   (fn x_b =>
     (fn f_ => fn () => f_ ((check_diag_impl_inta m m x_b) ()) ())
       (fn x_c =>
         (if x_c
           then mtx_set (heap_DBMEntry heap_int) (suc m) x_b
                  (zero_nata, zero_nata) (Lt zero_inta)
           else (fn f_ => fn () => f_
                  ((norm_upd_impl
                     (linordered_ab_group_add_int, equal_int, heap_int) m x_b
                     let
                       val (l, _) = bia;
                     in
                       Vector.fromList
                         (map (fn c =>
                                maxa (ceq_int, ccompare_int, lattice_int,
                                       linorder_int)
                                  (image (ceq_nat, ccompare_nat)
                                    (ceq_int, ccompare_int, set_impl_int)
                                    (fn i => sub (sub (sub k_i i) (nth l i)) c)
                                    (atLeastLessThan
                                      (ceq_nat, ccompare_nat, equal_nat,
interval_nat, set_impl_nat)
                                      zero_nata n_ps)))
                           (upt zero_nata (plus_nata m one_nata)))
                     end
                     m)
                  ()) ())
                  (fw_impl_int m))))))))));
               in
                 (fn (a1, a2) =>
                   imp_nfoldli (trans_impl a1) (fn _ => (fn () => true))
                     (fn xc => fn sigma =>
                       let
                         val (a1a, (_, (a1c, a2c))) = xc;
                       in
                         (if let
                               val (a, b) = a2c;
                             in
                               hd_of_formulai equal_nat formula a b
                             end
                           then (fn f_ => fn () => f_
                                  ((amtx_copy (heap_DBMEntry heap_int) a2) ())
                                  ())
                                  (fn x =>
                                    (fn f_ => fn () => f_
                                      ((e_op_impl a1 a1c a1a a2c x) ()) ())
                                      (fn xa =>
(fn () => (op_list_prepend (a2c, xa) sigma))))
                           else (fn () => sigma))
                       end)
                     [])
               end
                xi)
             ()) ())
             (fn x =>
               (fn f_ => fn () => f_
                 ((imp_nfoldli x (fn _ => (fn () => true))
                    (fn xc => fn sigma =>
                      (fn f_ => fn () => f_
                        (let
                           val (_, a2) = xc;
                         in
                           (fn f_ => fn () => f_ ((check_diag_impl_int m a2) ())
                             ())
                             (fn x_c => (fn () => (not x_c)))
                         end
                        ()) ())
                        (fn x_c =>
                          (fn () =>
                            (if x_c then op_list_prepend xc sigma else sigma))))
                    [])
                 ()) ())
                 (fn xa => (fn () => (op_list_rev xa)))));
     in
       dfs_map_impl
         (heap_prod (heap_prod (heap_list heap_nat) (heap_list heap_int))
           (heap_array (typerep_DBMEntry typerep_int)))
         (equal_prod (equal_list equal_nat) (equal_list equal_int),
           hashable_prod (hashable_list hashable_nat)
             (hashable_list hashable_int),
           heap_prod (heap_list heap_nat) (heap_list heap_int))
         succs start suba key copy
     end
    ()) ())
    (fn x =>
      (fn f_ => fn () => f_ ((fn () => ()) ()) ()) (fn _ => (fn () => x)));

fun check_sexp A_ (C1_, C2_) Truea uu uv = true
  | check_sexp A_ (C1_, C2_) (Notb e) l s = not (check_sexp A_ (C1_, C2_) e l s)
  | check_sexp A_ (C1_, C2_) (Andb (e1, e2)) l s =
    check_sexp A_ (C1_, C2_) e1 l s andalso check_sexp A_ (C1_, C2_) e2 l s
  | check_sexp A_ (C1_, C2_) (Orb (e1, e2)) l s =
    check_sexp A_ (C1_, C2_) e1 l s orelse check_sexp A_ (C1_, C2_) e2 l s
  | check_sexp A_ (C1_, C2_) (Implya (e1, e2)) l s =
    (if check_sexp A_ (C1_, C2_) e1 l s then check_sexp A_ (C1_, C2_) e2 l s
      else true)
  | check_sexp A_ (C1_, C2_) (Eqb (i, x)) l s = eq C1_ (s i) x
  | check_sexp A_ (C1_, C2_) (Leb (i, x)) l s =
    less_eq ((ord_preorder o preorder_order o order_linorder) C2_) (s i) x
  | check_sexp A_ (C1_, C2_) (Ltc (i, x)) l s =
    less ((ord_preorder o preorder_order o order_linorder) C2_) (s i) x
  | check_sexp A_ (C1_, C2_) (Gea (i, x)) l s =
    less_eq ((ord_preorder o preorder_order o order_linorder) C2_) x (s i)
  | check_sexp A_ (C1_, C2_) (Gtb (i, x)) l s =
    less ((ord_preorder o preorder_order o order_linorder) C2_) x (s i)
  | check_sexp A_ (C1_, C2_) (Loc (i, x)) l s = eq A_ (nth l i) x;

fun hd_of_formula A_ (C1_, C2_) (EX phi) l s = check_sexp A_ (C1_, C2_) phi l s
  | hd_of_formula A_ (C1_, C2_) (EG phi) l s = check_sexp A_ (C1_, C2_) phi l s
  | hd_of_formula A_ (C1_, C2_) (AX phi) l s =
    not (check_sexp A_ (C1_, C2_) phi l s)
  | hd_of_formula A_ (C1_, C2_) (AG phi) l s =
    not (check_sexp A_ (C1_, C2_) phi l s)
  | hd_of_formula A_ (C1_, C2_) (Leadsto (phi, uu)) l s =
    check_sexp A_ (C1_, C2_) phi l s;

fun model_checker broadcast bounds automata m num_states num_actions k l_0 s_0
  formula show_clock show_state =
  (case formula
    of EX _ =>
      reachability_checker broadcast bounds automata m num_states num_actions k
        l_0 s_0 formula show_clock show_state
    | EG _ =>
      (if hd_of_formula equal_nat (equal_int, linorder_int) formula l_0
            (the o map_of equal_nat s_0)
        then alw_ev_checker broadcast bounds automata m num_states num_actions k
               l_0 s_0 formula
        else (fn () => false))
    | AX _ =>
      (fn f_ => fn () => f_
        ((if hd_of_formula equal_nat (equal_int, linorder_int) formula l_0
               (the o map_of equal_nat s_0)
           then alw_ev_checker broadcast bounds automata m num_states
                  num_actions k l_0 s_0 formula
           else (fn () => false))
        ()) ())
        (fn r => (fn () => (not r)))
    | AG _ =>
      (fn f_ => fn () => f_
        ((reachability_checker broadcast bounds automata m num_states
           num_actions k l_0 s_0 formula show_clock show_state)
        ()) ())
        (fn r => (fn () => (not r)))
    | Leadsto (_, psi) =>
      leadsto_checker broadcast bounds automata m num_states num_actions k l_0
        s_0 formula psi show_clock show_state);

fun precond_mc show_clock show_state broadcast bounds automata m num_states
  num_actions k l_0 s_0 formula =
  (if simple_Network_Impl_nat_ceiling_start_state broadcast bounds automata m
        num_states num_actions k l_0 s_0 formula
    then (fn f_ => fn () => f_
           ((model_checker broadcast bounds automata m num_states num_actions k
              l_0 s_0 formula show_clock show_state)
           ()) ())
           (fn x => (fn () => (SOME x)))
    else (fn () => NONE));

fun rename_mc A_ B_ C_ dc broadcast bounds automata k urge l_0 s_0 formula m
  num_states num_actions renum_acts renum_vars renum_clocks renum_states
  inv_renum_states inv_renum_vars inv_renum_clocks =
  (case do_rename_mc show_int A_ B_ C_ (if dc then precond_dc else precond_mc)
          dc broadcast bounds automata k urge l_0 s_0 formula m num_states
          num_actions renum_acts renum_vars renum_clocks renum_states
          inv_renum_states inv_renum_vars inv_renum_clocks
    of NONE => (fn () => Renaming_Failed)
    | SOME r =>
      (fn f_ => fn () => f_ (r ()) ())
        (fn a =>
          (case a of NONE => (fn () => Preconds_Unsat)
            | SOME true => (fn () => Sat) | SOME false => (fn () => Unsat))));

fun shows_rat r =
  let
    val Rata (s, f, b) = r;
  in
    (if s then []
      else [Chara (true, false, true, true, false, true, false, false)]) @
      shows_prec_int zero_nata f [] @
        (if not (equal_inta b zero_inta)
          then [Chara (false, true, true, true, false, true, false, false)] @
                 shows_prec_int zero_nata b []
          else [])
  end;

fun check_and_make_network_opt problem =
  (case check_and_make_network problem
    of Inl e =>
      let
        val _ =
          map (fn a => writeln a) ["Could not make network", implode (e () [])];
      in
        NONE
      end
    | Inr (clocks, (names, network)) => SOME (clocks, (names, network)));

fun concat_str x = (implode o concat o map explode) x;

fun preproc_mc A_ =
  (fn dc => fn ids_to_names => fn (broadcast, (automata, bounds)) => fn l_0 =>
    fn s_0 => fn formula =>
    let
      val _ = writeln "Make renaming";
    in
      (case make_renaming
              (ceq_nat, ccompare_nat, equal_nat, set_impl_nat, show_nat)
              broadcast automata bounds
        of Result
             (m, (num_states,
                   (num_actions,
                     (renum_acts,
                       (renum_vars,
                         (renum_clocks,
                           (renum_states,
                             (inv_renum_states,
                               (inv_renum_vars, inv_renum_clocks)))))))))
          => let
               val _ = writeln "Renaming";
               val (broadcasta, (automataa, boundsa)) =
                 rename_network countable_literal countable_literal
                   countable_nat countable_literal broadcast bounds automata
                   renum_acts renum_vars renum_clocks renum_states;
               val _ = writeln "Calculating ceiling";
               val k = local_ceiling broadcasta boundsa automataa m num_states;
               val _ = writeln "Running model checker";
               val inv_renum_statesa =
                 (fn i => ids_to_names i o inv_renum_states i);
             in
               (fn f_ => fn () => f_
                 ((rename_mc A_ show_literal show_literal dc broadcast bounds
                    automata k "_urge" l_0 s_0 formula m num_states num_actions
                    renum_acts renum_vars renum_clocks renum_states
                    inv_renum_statesa inv_renum_vars inv_renum_clocks)
                 ()) ())
                 (fn r => (fn () => (Result r)))
             end
        | Error e => (fn () => (Error e)))
    end);

fun shows_json n (Nata m) = pad n (shows_prec_nat zero_nata m [])
  | shows_json n (Rat r) = pad n (shows_rat r)
  | shows_json n (Int r) = pad n (shows_prec_int zero_nata r [])
  | shows_json n (Boolean b) =
    pad n (if b then [Chara (false, false, true, false, true, true, true,
                              false),
                       Chara (false, true, false, false, true, true, true,
                               false),
                       Chara (true, false, true, false, true, true, true,
                               false),
                       Chara (true, false, true, false, false, true, true,
                               false)]
            else [Chara (false, true, true, false, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (true, true, false, false, true, true, true, false),
                   Chara (true, false, true, false, false, true, true, false)])
  | shows_json n Null =
    pad n [Chara (false, true, true, true, false, true, true, false),
            Chara (true, false, true, false, true, true, true, false),
            Chara (false, false, true, true, false, true, true, false),
            Chara (false, false, true, true, false, true, true, false)]
  | shows_json n (Stringa s) =
    pad n ([Chara (false, true, false, false, false, true, false, false)] @
            s @ [Chara (false, true, false, false, false, true, false, false)])
  | shows_json n (Arraya xs) =
    (if null xs
      then pad n [Chara (true, true, false, true, true, false, true, false),
                   Chara (true, false, true, true, true, false, true, false)]
      else pad n [Chara (true, true, false, true, true, false, true, false),
                   Chara (false, true, false, true, false, false, false,
                           false)] @
             concat
               (intersperse
                 [Chara (false, false, true, true, false, true, false, false),
                   Chara (false, true, false, true, false, false, false, false)]
                 (map (shows_json
                        (plus_nata n (nat_of_integer (2 : Int.int))))
                   xs)) @
               [Chara (false, true, false, true, false, false, false, false)] @
                 pad n [Chara (true, false, true, true, true, false, true,
                                false)])
  | shows_json n (Object xs) =
    (if null xs
      then pad n [Chara (true, true, false, true, true, true, true, false),
                   Chara (true, false, true, true, true, true, true, false)]
      else pad n [Chara (true, true, false, true, true, true, true, false),
                   Chara (false, true, false, true, false, false, false,
                           false)] @
             concat
               (intersperse
                 [Chara (false, false, true, true, false, true, false, false),
                   Chara (false, true, false, true, false, false, false, false)]
                 (map (fn (k, v) =>
                        pad (plus_nata n (nat_of_integer (2 : Int.int)))
                          ([Chara (false, true, false, false, false, true,
                                    false, false)] @
                            k @ [Chara (false, true, false, false, false, true,
 false, false)]) @
                          [Chara (false, true, false, true, true, true, false,
                                   false),
                            Chara (false, true, false, true, false, false,
                                    false, false)] @
                            shows_json
                              (plus_nata n (nat_of_integer (4 : Int.int))) v)
                   xs)) @
               [Chara (false, true, false, true, false, false, false, false)] @
                 pad n [Chara (true, false, true, true, true, true, true,
                                false)]);

fun check_and_cert_pddl_problem problem mode num_split certifier show_cert =
  (case make_certified_net problem certifier
    of Result (network, (renaming, cert)) =>
      (fn f_ => fn () => f_
        ((convert_check mode num_split false network renaming cert show_cert)
        ()) ())
        (fn res =>
          let
            val _ =
              (case res
                of Result Renaming_Failed =>
                  let
                    val _ = writeln "Something went wrong.";
                  in
                    (fn () => ())
                  end
                | Result Preconds_Unsat =>
                  let
                    val _ = writeln "Something went wrong.";
                  in
                    (fn () => ())
                  end
                | Result Sat =>
                  let
                    val _ = writeln "The planning problem is unsolvable.";
                  in
                    (fn () => ())
                  end
                | Result Unsat => let
                                    val _ = writeln "Something went wrong.";
                                  in
                                    (fn () => ())
                                  end
                | Error es => let
                                val _ = map (fn a => writeln a) es;
                              in
                                (fn () => ())
                              end);
          in
            (fn () => res)
          end)
    | Error es => let
                    val _ = map (fn a => writeln a) es;
                  in
                    (fn () => (Error es))
                  end);

fun show_str A_ = implode o (fn x => shows_prec A_ zero_nata x []);

fun do_preproc_mc A_ =
  (fn dc => fn ids_to_names => fn (broadcast, (automata, bounds)) => fn l_0 =>
    fn s_0 => fn formula =>
    (fn f_ => fn () => f_
      ((preproc_mc A_ dc ids_to_names (broadcast, (automata, bounds)) l_0 s_0
         formula)
      ()) ())
      (fn r =>
        (fn () =>
          (case r of Result Renaming_Failed => err "Renaming failed"
            | Result Preconds_Unsat => err "Input invalid"
            | Result Sat =>
              Result
                (if dc then "Model has a deadlock!"
                  else "Property is satisfied!")
            | Result Unsat =>
              Result
                (if dc then "Model has no deadlock!"
                  else "Property is not satisfied!")
            | Error es =>
              err ("Error during preprocessing:\n" ^
                    concat_str (intersperse "\n" es))))));

fun map_of_debug (A1_, A2_) prefix m =
  let
    val ma = map_of A1_ m;
  in
    (fn x =>
      (case ma x
        of NONE =>
          let
            val _ = writeln ("Key error(" ^ prefix ^ "): " ^ show_lit A2_ x);
          in
            NONE
          end
        | SOME a => SOME a))
  end;

fun shows_prec_JSON p x rest = shows_json zero_nata x @ rest;

fun parse_convert_run dc s =
  (case binda (parse json s)
          (fn r =>
            let
              val sa = implode (shows_prec_JSON zero_nata r []);
              val _ =
                (fn _ => fn s => writeln (s ())) (Int_of_integer
           (2 : Int.int)) ((fn _ => (fn () => sa)) ());
            in
              binda (parse json sa)
                (fn ra =>
                  binda (assert (equal_JSONa r ra)
                          "Parse-print-parse loop failed!")
                    (fn _ => convert r))
            end)
    of Result
         (ids_to_names,
           (_, (broadcast, (automata, (bounds, (formula, (l_0, s_0)))))))
      => do_preproc_mc show_literal dc ids_to_names
           (broadcast, (automata, bounds)) l_0 s_0 formula
    | Error es => (fn () => (Error es)));

fun list_of_json_object obj =
  (case obj of Object a => Result a | Arraya _ => Error ["Not an object"]
    | Stringa _ => Error ["Not an object"] | Int _ => Error ["Not an object"]
    | Nata _ => Error ["Not an object"] | Rat _ => Error ["Not an object"]
    | Boolean _ => Error ["Not an object"] | Null => Error ["Not an object"]);

fun nat_renaming_of_json prefix max_id json =
  binda (list_of_json_object json)
    (fn vars =>
      binda (combine_map
              (fn (a, b) =>
                binda (parse lx_nat (implode a))
                  (fn aa => binda (of_nat b) (fn ba => Result (aa, ba))))
              vars)
        (fn varsa =>
          let
            val ids =
              image (ceq_prod ceq_nat ceq_nat,
                      ccompare_prod ccompare_nat ccompare_nat)
                (ceq_nat, ccompare_nat, set_impl_nat) fst
                (set (ceq_prod ceq_nat ceq_nat,
                       ccompare_prod ccompare_nat ccompare_nat,
                       set_impl_prod set_impl_nat set_impl_nat)
                  varsa);
            val missing =
              filter (fn i => not (member (ceq_nat, ccompare_nat) i ids))
                (upt zero_nata max_id);
            val m = the o map_of_debug (equal_nat, show_nat) prefix varsa;
            val ma =
              extend_domain equal_nat (one_nat, plus_nat) m missing
                (size_list varsa);
          in
            Result
              (ma, the o map_of_debug (equal_nat, show_nat) prefix
                           (map swap varsa))
          end));

fun renaming_of_jsona opt prefix json =
  binda (list_of_json_object json)
    (fn vars =>
      binda (combine_map
              (fn (a, b) => binda (of_nat b) (fn ba => Result (implode a, ba)))
              vars)
        (fn varsa =>
          let
            val varsb =
              varsa @
                (case opt of NONE => []
                  | SOME x =>
                    [(x, plus_nata (fold (max ord_nat o snd) varsa zero_nata)
                           one_nata)]);
          in
            Result
              (the o map_of_debug (equal_literal, show_literal) prefix varsb,
                the o map_of_debug (equal_nat, show_nat) prefix
                        (map swap varsb))
          end));

fun renaming_of_json x = renaming_of_jsona NONE x;

fun convert_renaming ids_to_names process_names_to_index json =
  binda (of_object json)
    (fn jsona =>
      binda (geta (show_list show_char) jsona
              [Chara (false, true, true, false, true, true, true, false),
                Chara (true, false, false, false, false, true, true, false),
                Chara (false, true, false, false, true, true, true, false),
                Chara (true, true, false, false, true, true, true, false)])
        (fn vars =>
          binda (renaming_of_json "var renaming" vars)
            (fn (var_renaming, var_inv) =>
              binda (geta (show_list show_char) jsona
                      [Chara (true, true, false, false, false, true, true,
                               false),
                        Chara (false, false, true, true, false, true, true,
                                false),
                        Chara (true, true, true, true, false, true, true,
                                false),
                        Chara (true, true, false, false, false, true, true,
                                false),
                        Chara (true, true, false, true, false, true, true,
                                false),
                        Chara (true, true, false, false, true, true, true,
                                false)])
                (fn clocks =>
                  binda (renaming_of_jsona (SOME "_urge") "clock renaming"
                          clocks)
                    (fn (clock_renaming, clock_inv) =>
                      binda (geta (show_list show_char) jsona
                              [Chara (false, false, false, false, true, true,
                                       true, false),
                                Chara (false, true, false, false, true, true,
true, false),
                                Chara (true, true, true, true, false, true,
true, false),
                                Chara (true, true, false, false, false, true,
true, false),
                                Chara (true, false, true, false, false, true,
true, false),
                                Chara (true, true, false, false, true, true,
true, false),
                                Chara (true, true, false, false, true, true,
true, false),
                                Chara (true, false, true, false, false, true,
true, false),
                                Chara (true, true, false, false, true, true,
true, false)])
                        (fn processes =>
                          binda (renaming_of_json "process renaming" processes)
                            (fn (process_renaming, _) =>
                              binda (geta (show_list show_char) jsona
                                      [Chara
 (false, false, true, true, false, true, true, false),
Chara (true, true, true, true, false, true, true, false),
Chara (true, true, false, false, false, true, true, false),
Chara (true, false, false, false, false, true, true, false),
Chara (false, false, true, false, true, true, true, false),
Chara (true, false, false, true, false, true, true, false),
Chara (true, true, true, true, false, true, true, false),
Chara (false, true, true, true, false, true, true, false),
Chara (true, true, false, false, true, true, true, false)])
                                (fn locations =>
                                  binda (list_of_json_object locations)
                                    (fn locationsa =>
                                      binda
(combine_map
  (fn (name, renaming) =>
    let
      val p_num = process_names_to_index (implode name);
    in
      binda (assert (equal_nata (process_renaming (implode name)) p_num)
              ("Process renamings do not agree on " ^ implode name))
        (fn _ =>
          let
            val max_id = nat_of_integer (1000 : Int.int);
          in
            binda (nat_renaming_of_json ("process" ^ show_str show_nat p_num)
                    max_id renaming)
              (fn renaminga => Result (p_num, renaminga))
          end)
    end)
  locationsa)
(fn locationsb =>
  let
    val location_renaming =
      the o map_of_debug (equal_nat, show_nat) "location"
              (map (fn (i, (f, _)) => (i, f)) locationsb);
    val location_inv =
      the o map_of_debug (equal_nat, show_nat) "location inv"
              (map (fn (i, (_, a)) => (i, a)) locationsb);
  in
    Result
      (var_renaming,
        (clock_renaming,
          (location_renaming, (var_inv, (clock_inv, location_inv)))))
  end))))))))));

fun parse_compute model renaming =
  binda (parse json model)
    (fn modela =>
      binda (convert modela)
        (fn (ids_to_names,
              (process_names_to_index,
                (broadcast, (automata, (bounds, (formula, (l_0, s_0)))))))
           =>
          binda (parse json renaming)
            (fn renaminga =>
              binda (convert_renaming ids_to_names process_names_to_index
                      renaminga)
                (fn (var_renaming,
                      (clock_renaming,
                        (location_renaming,
                          (inv_renum_vars,
                            (inv_renum_clocks, inv_renum_states)))))
                   =>
                  binda (make_renaming
                          (ceq_nat, ccompare_nat, equal_nat, set_impl_nat,
                            show_nat)
                          broadcast automata bounds)
                    (fn (m, (num_states,
                              (num_actions,
                                (renum_acts,
                                  (_, (renum_clocks, (_, (_, (_, _)))))))))
                       =>
                      binda (assert (equal_nata (renum_clocks "_urge") m)
                              "Computed renaming: _urge is not last clock!")
                        (fn _ =>
                          let
                            val renum_vars = var_renaming;
                            val renum_clocksa = clock_renaming;
                            val renum_states = location_renaming;
                          in
                            binda (assert (equal_nata (renum_clocksa "_urge") m)
                                    "Given renaming: _urge is not last clock!")
                              (fn _ =>
                                let
                                  val _ = writeln "Renaming";
                                  val (broadcasta, (automataa, boundsa)) =
                                    rename_network countable_literal
                                      countable_literal countable_nat
                                      countable_literal broadcast bounds
                                      automata renum_acts renum_vars
                                      renum_clocksa renum_states;
                                  val _ = writeln "Calculating ceiling";
                                  val k =
                                    local_ceiling broadcasta boundsa automataa m
                                      num_states;
                                  val urgent_locations =
                                    map (fn (_, (urgent, (_, _))) => urgent)
                                      automataa;
                                in
                                  Result
                                    (broadcast,
                                      (bounds,
(automata,
  (urgent_locations,
    (k, (l_0, (s_0, (formula,
                      (m, (num_states,
                            (num_actions,
                              (renum_acts,
                                (renum_vars,
                                  (renum_clocksa,
                                    (renum_states,
                                      (inv_renum_states,
(inv_renum_vars, inv_renum_clocks)))))))))))))))))
                                end)
                          end))))));

fun check_and_cert_pddl_problem_no_return problem mode num_split certifier
  show_cert =
  (fn f_ => fn () => f_
    ((check_and_cert_pddl_problem problem mode num_split certifier show_cert)
    ()) ())
    (fn _ => (fn () => ()));

fun parse_convert_check mode num_split dc model renaming state_space show_cert =
  (case parse_compute model renaming
    of Result
         (broadcast,
           (bounds,
             (automata,
               (urgent_locations,
                 (k, (l_0, (s_0, (formula,
                                   (m, (num_states,
 (num_actions,
   (renum_acts,
     (renum_vars,
       (renum_clocks,
         (renum_states,
           (inv_renum_states, (inv_renum_vars, inv_renum_clocks)))))))))))))))))
      => let
           val is_urgent =
             (fn (l, _) =>
               list_ex
                 (fn (la, urgent) =>
                   membera equal_int (map int_of_nat urgent) la)
                 (zip l urgent_locations));
           val inv_renum_clocksa =
             (fn i => (if equal_nata i m then "_urge" else inv_renum_clocks i));
           val t = Time.now ();
           val state_spacea = convert_state_space m is_urgent state_space;
           val ta = (fn x => fn y => Time.- (x, y)) (Time.now ()) t;
           val _ =
             writeln ("Time for converting state space: " ^
                       (fn x => Time.toString x) ta);
           val _ = Timing.start_timer ();
           val _ = Timing.save_time "Time for converting DBMs in certificate";
           val _ =
             writeln ("Number of discrete states: " ^
                       show_lit show_nat (len_of_state_space state_spacea));
           val _ =
             (if show_cert
               then let
                      val _ = print_sep ();
                      val _ = writeln "Certificate";
                      val _ = print_sep ();
                      val _ =
                        show_state_space m inv_renum_states inv_renum_vars
                          inv_renum_clocksa state_spacea;
                      val _ = print_sep ();
                    in
                      (fn () => ())
                    end
               else (fn () => ()));
           val tb = Time.now ();
         in
           (fn f_ => fn () => f_
             ((case mode
                of Impl1 =>
                  rename_check num_split dc broadcast bounds automata k l_0 s_0
                    formula m num_states num_actions renum_acts renum_vars
                    renum_clocks renum_states (reach_of state_spacea)
                | Impl2 =>
                  (fn () =>
                    (rename_check2 num_split dc broadcast bounds automata k l_0
                      s_0 formula m num_states num_actions renum_acts renum_vars
                      renum_clocks renum_states (reach_of state_spacea)))
                | Impl3 =>
                  (fn () =>
                    (rename_check3 num_split dc broadcast bounds automata k l_0
                      s_0 formula m num_states num_actions renum_acts renum_vars
                      renum_clocks renum_states (reach_of state_spacea)))
                | Buechi =>
                  (fn () =>
                    (rename_check_buechi num_split broadcast bounds automata k
                      l_0 s_0 formula m num_states num_actions renum_acts
                      renum_vars renum_clocks renum_states
                      (buechi_of state_spacea)))
                | Debug =>
                  rename_check_dbg show_nat show_literal show_literal num_split
                    dc broadcast bounds automata k l_0 s_0 formula m num_states
                    num_actions renum_acts renum_vars renum_clocks renum_states
                    inv_renum_states inv_renum_vars inv_renum_clocksa
                    (reach_of state_spacea))
             ()) ())
             (fn check =>
               let
                 val tc = (fn x => fn y => Time.- (x, y)) (Time.now ()) tb;
                 val _ =
                   writeln ("Time for certificate checking: " ^
                             (fn x => Time.toString x) tc);
               in
                 (case check
                   of Renaming_Failed => let
   val _ = writeln "Renaming failed";
 in
   (fn () => ())
 end
                   | Preconds_Unsat =>
                     let
                       val _ = writeln "Preconditions were not met";
                     in
                       (fn () => ())
                     end
                   | Sat => let
                              val _ = writeln "Certificate was accepted";
                            in
                              (fn () => ())
                            end
                   | Unsat => let
                                val _ = writeln "Certificate was rejected";
                              in
                                (fn () => ())
                              end)
               end)
         end
    | Error es => let
                    val _ = map (fn a => writeln a) es;
                  in
                    (fn () => ())
                  end);

end; (*struct Converter*)
