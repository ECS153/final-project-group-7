(* Copyright@Xinyuan Sun, sxysun@ucdavis.edu   *)
Require Import BuiltIn.
Require BuiltIn.
Require HighOrd.
Require int.Int.
Require int.Abs.
Require int.MinMax.
Require int.EuclideanDivision.
Require int.ComputerDivision.
Require map.Map.
Require bv.Pow2int.
Require bv.BV_Gen.
Require bool.Bool.
Require list.List.
Require list.Length.
Require list.Mem.
Require list.NthNoOpt.
Require list.HdTlNoOpt.
Require list.Append.

(* Why3 assumption *)
Inductive ref (a:Type) :=
  | ref'mk : a -> ref a.
Axiom ref_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (ref a).
Existing Instance ref_WhyType.
Arguments ref'mk {a}.

(* Why3 assumption *)
Definition contents {a:Type} {a_WT:WhyType a} (v:ref a) : a :=
  match v with
  | ref'mk x => x
  end.

Axiom array : forall (a:Type), Type.
Parameter array_WhyType :
  forall (a:Type) {a_WT:WhyType a}, WhyType (array a).
Existing Instance array_WhyType.

Parameter elts:
  forall {a:Type} {a_WT:WhyType a}, array a -> Numbers.BinNums.Z -> a.

Parameter length:
  forall {a:Type} {a_WT:WhyType a}, array a -> Numbers.BinNums.Z.

Axiom array'invariant :
  forall {a:Type} {a_WT:WhyType a},
  forall (self:array a), (0%Z <= (length self))%Z.

(* Why3 assumption *)
Definition mixfix_lbrb {a:Type} {a_WT:WhyType a} (a1:array a)
    (i:Numbers.BinNums.Z) : a :=
  elts a1 i.

Parameter mixfix_lblsmnrb:
  forall {a:Type} {a_WT:WhyType a}, array a -> Numbers.BinNums.Z -> a ->
  array a.

Axiom mixfix_lblsmnrb'spec :
  forall {a:Type} {a_WT:WhyType a},
  forall (a1:array a) (i:Numbers.BinNums.Z) (v:a),
  ((length (mixfix_lblsmnrb a1 i v)) = (length a1)) /\
  ((elts (mixfix_lblsmnrb a1 i v)) = (map.Map.set (elts a1) i v)).

Parameter make:
  forall {a:Type} {a_WT:WhyType a}, Numbers.BinNums.Z -> a -> array a.

Axiom make'spec :
  forall {a:Type} {a_WT:WhyType a},
  forall (n:Numbers.BinNums.Z) (v:a), (0%Z <= n)%Z ->
  (forall (i:Numbers.BinNums.Z), (0%Z <= i)%Z /\ (i < n)%Z ->
   ((mixfix_lbrb (make n v) i) = v)) /\
  ((length (make n v)) = n).

Axiom t : Type.
Parameter t_WhyType : WhyType t.
Existing Instance t_WhyType.

Parameter max: Numbers.BinNums.Z.

Parameter to_int: t -> Numbers.BinNums.Z.

(* Why3 assumption *)
Definition in_bounds (n:Numbers.BinNums.Z) : Prop :=
  (0%Z <= n)%Z /\ (n <= max)%Z.

Axiom to_int_in_bounds : forall (n:t), in_bounds (to_int n).

Axiom extensionality :
  forall (x:t) (y:t), ((to_int x) = (to_int y)) -> (x = y).

Parameter zero_unsigned: t.

Axiom zero_unsigned_is_zero : ((to_int zero_unsigned) = 0%Z).

Parameter radix: Numbers.BinNums.Z.

Axiom radix_def : (radix = (max + 1%Z)%Z).

(* Why3 assumption *)
Definition b2i (b:Init.Datatypes.bool) : Numbers.BinNums.Z :=
  match b with
  | Init.Datatypes.true => 1%Z
  | Init.Datatypes.false => 0%Z
  end.

Parameter i2b: Numbers.BinNums.Z -> Init.Datatypes.bool.

Axiom i2b'def :
  forall (i:Numbers.BinNums.Z), (i = 0%Z) \/ (i = 1%Z) ->
  ((i = 1%Z) -> ((i2b i) = Init.Datatypes.true)) /\
  (~ (i = 1%Z) -> ((i2b i) = Init.Datatypes.false)).

(* Why3 assumption *)
Definition word := Numbers.BinNums.Z.

(* Why3 assumption *)
Inductive t1 :=
  | t'mk : Init.Datatypes.list Numbers.BinNums.Z -> Numbers.BinNums.Z ->
      Numbers.BinNums.Z -> t1.
Axiom t1_WhyType : WhyType t1.
Existing Instance t1_WhyType.

(* Why3 assumption *)
Definition peek (v:t1) : Numbers.BinNums.Z :=
  match v with
  | t'mk x x1 x2 => x2
  end.

(* Why3 assumption *)
Definition cur_size (v:t1) : Numbers.BinNums.Z :=
  match v with
  | t'mk x x1 x2 => x1
  end.

(* Why3 assumption *)
Definition data (v:t1) : Init.Datatypes.list Numbers.BinNums.Z :=
  match v with
  | t'mk x x1 x2 => x
  end.

(* Why3 assumption *)
Definition ceiling (x:Numbers.BinNums.Z) : Numbers.BinNums.Z :=
  ZArith.BinInt.Z.quot (x + (ZArith.BinInt.Z.quot 256%Z 8%Z))%Z
  (ZArith.BinInt.Z.quot 256%Z 8%Z).

(* Why3 assumption *)
Definition round_up_word_index (max_index:Numbers.BinNums.Z)
    (i:Numbers.BinNums.Z) : Numbers.BinNums.Z :=
  ZArith.BinInt.Z.max max_index
  (ceiling (i + (ZArith.BinInt.Z.quot 256%Z 8%Z))%Z).

Parameter k_zeroes:
  Numbers.BinNums.Z -> Init.Datatypes.list Numbers.BinNums.Z.

Axiom k_zeroes'def :
  forall (k:Numbers.BinNums.Z),
  ((k < 0%Z)%Z -> ((k_zeroes k) = Init.Datatypes.nil)) /\
  (~ (k < 0%Z)%Z ->
   ((k_zeroes k) =
    (Init.Datatypes.app (Init.Datatypes.cons 0%Z Init.Datatypes.nil)
     (k_zeroes (k - 1%Z)%Z)))).

(* Why3 assumption *)
Definition pad_mem_up_to (data1:Init.Datatypes.list Numbers.BinNums.Z)
    (cur_size1:Numbers.BinNums.Z) (new_size:Numbers.BinNums.Z) :
    Init.Datatypes.list Numbers.BinNums.Z :=
  Init.Datatypes.app data1 (k_zeroes (new_size - cur_size1)%Z).

Parameter get_mem: Numbers.BinNums.Z -> t1 -> t1.

Axiom get_mem'def :
  forall (byte_idx:Numbers.BinNums.Z) (mem:t1),
  ((byte_idx < ((cur_size mem) * 32%Z)%Z)%Z ->
   ((get_mem byte_idx mem) =
    (t'mk (data mem) (cur_size mem)
     (list.NthNoOpt.nth (ZArith.BinInt.Z.quot byte_idx 32%Z) (data mem))))) /\
  (~ (byte_idx < ((cur_size mem) * 32%Z)%Z)%Z ->
   ((get_mem byte_idx mem) =
    (let new_size := round_up_word_index (cur_size mem) byte_idx in
     t'mk (pad_mem_up_to (data mem) (cur_size mem) new_size) new_size 0%Z))).

Parameter replace_nth:
  Init.Datatypes.list Numbers.BinNums.Z -> Numbers.BinNums.Z ->
  Numbers.BinNums.Z -> Init.Datatypes.list Numbers.BinNums.Z.

Axiom replace_nth'def :
  forall (li:Init.Datatypes.list Numbers.BinNums.Z) (idx:Numbers.BinNums.Z)
    (value:Numbers.BinNums.Z),
  match li with
  | Init.Datatypes.nil => ((replace_nth li idx value) = Init.Datatypes.nil)
  | Init.Datatypes.cons ushd ustl =>
      ((idx = 0%Z) ->
       ((replace_nth li idx value) =
        (Init.Datatypes.app (Init.Datatypes.cons value Init.Datatypes.nil)
         ustl))) /\
      (~ (idx = 0%Z) ->
       ((replace_nth li idx value) =
        (Init.Datatypes.app (Init.Datatypes.cons ushd Init.Datatypes.nil)
         (replace_nth ustl (idx - 1%Z)%Z value))))
  end.

Parameter set_mem: Numbers.BinNums.Z -> Numbers.BinNums.Z -> t1 -> t1.

Axiom set_mem'def :
  forall (byte_idx:Numbers.BinNums.Z) (new_val:Numbers.BinNums.Z) (mem:t1),
  let word_idx := ZArith.BinInt.Z.quot byte_idx 32%Z in
  (((cur_size mem) <= word_idx)%Z ->
   ((set_mem byte_idx new_val mem) =
    (let new_size := round_up_word_index (cur_size mem) byte_idx in
     t'mk
     (replace_nth (pad_mem_up_to (data mem) (cur_size mem) new_size) word_idx
      new_val)
     new_size (peek mem)))) /\
  (~ ((cur_size mem) <= word_idx)%Z ->
   ((set_mem byte_idx new_val mem) =
    (t'mk (replace_nth (data mem) word_idx new_val)
     (round_up_word_index (cur_size mem) byte_idx) (peek mem)))).

Parameter trim_fst:
  forall {a:Type} {a_WT:WhyType a}, Init.Datatypes.list a ->
  Numbers.BinNums.Z -> Init.Datatypes.list a.

Axiom trim_fst'def :
  forall {a:Type} {a_WT:WhyType a},
  forall (li:Init.Datatypes.list a) (n:Numbers.BinNums.Z),
  ((n <= 0%Z)%Z \/ list.List.is_nil li -> ((trim_fst li n) = li)) /\
  (~ ((n <= 0%Z)%Z \/ list.List.is_nil li) ->
   ((trim_fst li n) = (trim_fst (list.HdTlNoOpt.tl li) (n - 1%Z)%Z))).

Parameter n_val:
  forall {a:Type} {a_WT:WhyType a}, Init.Datatypes.list a ->
  Numbers.BinNums.Z -> Init.Datatypes.list a.

Axiom n_val'def :
  forall {a:Type} {a_WT:WhyType a},
  forall (li:Init.Datatypes.list a) (n:Numbers.BinNums.Z),
  ((n <= 0%Z)%Z \/ list.List.is_nil li ->
   ((n_val li n) = Init.Datatypes.nil)) /\
  (~ ((n <= 0%Z)%Z \/ list.List.is_nil li) ->
   ((n_val li n) =
    (Init.Datatypes.app
     (Init.Datatypes.cons (list.HdTlNoOpt.hd li) Init.Datatypes.nil)
     (n_val (list.HdTlNoOpt.tl li) (n - 1%Z)%Z)))).

(* Why3 assumption *)
Definition subseq {a:Type} {a_WT:WhyType a} (li:Init.Datatypes.list a)
    (base:Numbers.BinNums.Z) (len:Numbers.BinNums.Z) : Init.Datatypes.list a :=
  n_val (trim_fst li base) len.

(* Why3 assumption *)
Fixpoint set_mem_range (mstart:Numbers.BinNums.Z)
  (data1:Init.Datatypes.list Numbers.BinNums.Z)
  (mem:t1) {struct data1}: t1 :=
  match data1 with
  | Init.Datatypes.nil => mem
  | Init.Datatypes.cons hd tl =>
      set_mem_range (mstart + 1%Z)%Z tl (set_mem mstart hd mem)
  end.

(* Why3 assumption *)
Definition get_mem_range (mem:t1) (mstart:Numbers.BinNums.Z)
    (msize:Numbers.BinNums.Z) : Init.Datatypes.list Numbers.BinNums.Z :=
  subseq (data mem) mstart msize.

(* Why3 assumption *)
Definition copy_block_data_to_mem (mem:t1)
    (block:Init.Datatypes.list Numbers.BinNums.Z) (mstart:Numbers.BinNums.Z)
    (dstart:Numbers.BinNums.Z) (size:Numbers.BinNums.Z) : t1 :=
  set_mem_range mstart (subseq block dstart size) mem.

(* Why3 assumption *)
Inductive t2 :=
  | t'mk1 : Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z ->
      Numbers.BinNums.Z -> t2.
Axiom t2_WhyType : WhyType t2.
Existing Instance t2_WhyType.

(* Why3 assumption *)
Definition msg_gas (v:t2) : Numbers.BinNums.Z :=
  match v with
  | t'mk1 x x1 x2 x3 => x3
  end.

(* Why3 assumption *)
Definition value (v:t2) : Numbers.BinNums.Z :=
  match v with
  | t'mk1 x x1 x2 x3 => x2
  end.

(* Why3 assumption *)
Definition sender (v:t2) : Numbers.BinNums.Z :=
  match v with
  | t'mk1 x x1 x2 x3 => x1
  end.

(* Why3 assumption *)
Definition recipient (v:t2) : Numbers.BinNums.Z :=
  match v with
  | t'mk1 x x1 x2 x3 => x
  end.

(* Why3 assumption *)
Inductive storage_entry :=
  | storage_entry'mk : Numbers.BinNums.Z -> Numbers.BinNums.Z ->
      storage_entry.
Axiom storage_entry_WhyType : WhyType storage_entry.
Existing Instance storage_entry_WhyType.

(* Why3 assumption *)
Definition sval (v:storage_entry) : Numbers.BinNums.Z :=
  match v with
  | storage_entry'mk x x1 => x1
  end.

(* Why3 assumption *)
Definition sloc (v:storage_entry) : Numbers.BinNums.Z :=
  match v with
  | storage_entry'mk x x1 => x
  end.

(* Why3 assumption *)
Definition t3 := Init.Datatypes.list storage_entry.

(* Why3 assumption *)
Definition set_storage (s:Init.Datatypes.list storage_entry)
    (addr:Numbers.BinNums.Z) (value1:Numbers.BinNums.Z) :
    Init.Datatypes.list storage_entry :=
  Init.Datatypes.app
  (Init.Datatypes.cons (storage_entry'mk addr value1) Init.Datatypes.nil) s.

Parameter get_storage:
  Init.Datatypes.list storage_entry -> Numbers.BinNums.Z ->
  Numbers.BinNums.Z.

Axiom get_storage'def :
  forall (s:Init.Datatypes.list storage_entry) (addr:Numbers.BinNums.Z),
  match s with
  | Init.Datatypes.nil => ((get_storage s addr) = 0%Z)
  | Init.Datatypes.cons hd tl =>
      (((sloc hd) = addr) -> ((get_storage s addr) = (sval hd))) /\
      (~ ((sloc hd) = addr) ->
       ((get_storage s addr) = (get_storage tl addr)))
  end.

(* Why3 assumption *)
Inductive t4 :=
  | t'mk2 : Init.Datatypes.list Numbers.BinNums.Z ->
      Init.Datatypes.list Numbers.BinNums.Z -> t4.
Axiom t4_WhyType : WhyType t4.
Existing Instance t4_WhyType.

(* Why3 assumption *)
Definition logged_mem (v:t4) : Init.Datatypes.list Numbers.BinNums.Z :=
  match v with
  | t'mk2 x x1 => x1
  end.

(* Why3 assumption *)
Definition topics (v:t4) : Init.Datatypes.list Numbers.BinNums.Z :=
  match v with
  | t'mk2 x x1 => x
  end.

(* Why3 assumption *)
Inductive t5 :=
  | t'mk3 : Init.Datatypes.list Numbers.BinNums.Z ->
      Init.Datatypes.list t4 -> Numbers.BinNums.Z -> t5.
Axiom t5_WhyType : WhyType t5.
Existing Instance t5_WhyType.

(* Why3 assumption *)
Definition refund (v:t5) : Numbers.BinNums.Z :=
  match v with
  | t'mk3 x x1 x2 => x2
  end.

(* Why3 assumption *)
Definition logs (v:t5) : Init.Datatypes.list t4 :=
  match v with
  | t'mk3 x x1 x2 => x1
  end.

(* Why3 assumption *)
Definition suicides (v:t5) : Init.Datatypes.list Numbers.BinNums.Z :=
  match v with
  | t'mk3 x x1 x2 => x
  end.

(* Why3 assumption *)
Definition add_log (subs:t5) (ust:Init.Datatypes.list Numbers.BinNums.Z)
    (mem:Init.Datatypes.list Numbers.BinNums.Z) : t5 :=
  t'mk3 (suicides subs)
  (Init.Datatypes.app
   (Init.Datatypes.cons (t'mk2 ust mem) Init.Datatypes.nil) (logs subs))
  (refund subs).

(* Why3 assumption *)
Inductive exit_explanation :=
  | Running : exit_explanation
  | Stop_instruction : exit_explanation
  | Revert_instruction : exit_explanation
  | Return_instruction : exit_explanation
  | Invalid_instruction : exit_explanation
  | Out_of_gas : exit_explanation.
Axiom exit_explanation_WhyType : WhyType exit_explanation.
Existing Instance exit_explanation_WhyType.

(* Why3 assumption *)
Inductive exit_status :=
  | exit_status'mk : Init.Datatypes.bool -> Numbers.BinNums.Z ->
      Init.Datatypes.list Numbers.BinNums.Z -> exit_explanation ->
      exit_status.
Axiom exit_status_WhyType : WhyType exit_status.
Existing Instance exit_status_WhyType.

(* Why3 assumption *)
Definition e_desc (v:exit_status) : exit_explanation :=
  match v with
  | exit_status'mk x x1 x2 x3 => x3
  end.

(* Why3 assumption *)
Definition e_data (v:exit_status) : Init.Datatypes.list Numbers.BinNums.Z :=
  match v with
  | exit_status'mk x x1 x2 x3 => x2
  end.

(* Why3 assumption *)
Definition e_gas (v:exit_status) : Numbers.BinNums.Z :=
  match v with
  | exit_status'mk x x1 x2 x3 => x1
  end.

(* Why3 assumption *)
Definition e_flag (v:exit_status) : Init.Datatypes.bool :=
  match v with
  | exit_status'mk x x1 x2 x3 => x
  end.

(* Why3 assumption *)
Inductive t6 :=
  | t'mk4 : Init.Datatypes.list Numbers.BinNums.Z ->
      Init.Datatypes.list Numbers.BinNums.Z -> t1 ->
      Init.Datatypes.list storage_entry -> t2 -> t5 -> Numbers.BinNums.Z ->
      exit_status -> t6.
Axiom t6_WhyType : WhyType t6.
Existing Instance t6_WhyType.

(* Why3 assumption *)
Definition e_stat (v:t6) : exit_status :=
  match v with
  | t'mk4 x x1 x2 x3 x4 x5 x6 x7 => x7
  end.

(* Why3 assumption *)
Definition pc (v:t6) : Numbers.BinNums.Z :=
  match v with
  | t'mk4 x x1 x2 x3 x4 x5 x6 x7 => x6
  end.

(* Why3 assumption *)
Definition subs (v:t6) : t5 :=
  match v with
  | t'mk4 x x1 x2 x3 x4 x5 x6 x7 => x5
  end.

(* Why3 assumption *)
Definition msg (v:t6) : t2 :=
  match v with
  | t'mk4 x x1 x2 x3 x4 x5 x6 x7 => x4
  end.

(* Why3 assumption *)
Definition st (v:t6) : Init.Datatypes.list storage_entry :=
  match v with
  | t'mk4 x x1 x2 x3 x4 x5 x6 x7 => x3
  end.

(* Why3 assumption *)
Definition m (v:t6) : t1 :=
  match v with
  | t'mk4 x x1 x2 x3 x4 x5 x6 x7 => x2
  end.

(* Why3 assumption *)
Definition cd (v:t6) : Init.Datatypes.list Numbers.BinNums.Z :=
  match v with
  | t'mk4 x x1 x2 x3 x4 x5 x6 x7 => x1
  end.

(* Why3 assumption *)
Definition sk (v:t6) : Init.Datatypes.list Numbers.BinNums.Z :=
  match v with
  | t'mk4 x x1 x2 x3 x4 x5 x6 x7 => x
  end.

(* Why3 assumption *)
Definition evmState := t6.

(* Why3 assumption *)
Definition lp (s:t6) (p:Init.Datatypes.list Numbers.BinNums.Z) : t6 :=
  t'mk4 (sk s) p (m s) (st s) (msg s) (subs s) (pc s) (e_stat s).

(* Why3 assumption *)
Definition ur (s:t6) : Numbers.BinNums.Z := list.NthNoOpt.nth 0%Z (sk s).

(* Why3 assumption *)
Definition getParam (s:t6) (i:Numbers.BinNums.Z) : Numbers.BinNums.Z :=
  list.NthNoOpt.nth i (cd s).

(* Why3 assumption *)
Definition setRet (s:t6) (v:Numbers.BinNums.Z) : t6 :=
  t'mk4 (Init.Datatypes.cons v Init.Datatypes.nil) (cd s) (m s) (st s)
  (msg s) (subs s) (pc s) (e_stat s).

(* Why3 assumption *)
Definition getRet (s:t6) (i:Numbers.BinNums.Z) : Numbers.BinNums.Z :=
  list.NthNoOpt.nth i (cd s).

Parameter i2b1: Numbers.BinNums.Z -> Init.Datatypes.bool.

Axiom i2b'def1 :
  forall (i:Numbers.BinNums.Z),
  (~ (i = 0%Z) -> ((i2b1 i) = Init.Datatypes.true)) /\
  ((i = 0%Z) -> ((i2b1 i) = Init.Datatypes.false)).

Parameter b2i1: Init.Datatypes.bool -> Numbers.BinNums.Z.

Axiom b2i'def :
  forall (b:Init.Datatypes.bool),
  ((b = Init.Datatypes.true) -> ((b2i1 b) = 1%Z)) /\
  (~ (b = Init.Datatypes.true) -> ((b2i1 b) = 0%Z)).

(* Why3 assumption *)
Definition t7 := Numbers.BinNums.Z.

Parameter nth: Numbers.BinNums.Z -> Numbers.BinNums.Z -> Init.Datatypes.bool.

Axiom nth_out_of_bound :
  forall (x:Numbers.BinNums.Z) (n:Numbers.BinNums.Z),
  (n < 0%Z)%Z \/ (8%Z <= n)%Z -> ((nth x n) = Init.Datatypes.false).

Parameter zeros: Numbers.BinNums.Z.

Axiom Nth_zeros :
  forall (n:Numbers.BinNums.Z), ((nth zeros n) = Init.Datatypes.false).

Parameter one: Numbers.BinNums.Z.

Parameter ones: Numbers.BinNums.Z.

Axiom Nth_ones :
  forall (n:Numbers.BinNums.Z), (0%Z <= n)%Z /\ (n < 8%Z)%Z ->
  ((nth ones n) = Init.Datatypes.true).

Parameter bw_and:
  Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom Nth_bw_and :
  forall (v1:Numbers.BinNums.Z) (v2:Numbers.BinNums.Z) (n:Numbers.BinNums.Z),
  (0%Z <= n)%Z /\ (n < 8%Z)%Z ->
  ((nth (bw_and v1 v2) n) = (Init.Datatypes.andb (nth v1 n) (nth v2 n))).

Parameter bw_or: Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom Nth_bw_or :
  forall (v1:Numbers.BinNums.Z) (v2:Numbers.BinNums.Z) (n:Numbers.BinNums.Z),
  (0%Z <= n)%Z /\ (n < 8%Z)%Z ->
  ((nth (bw_or v1 v2) n) = (Init.Datatypes.orb (nth v1 n) (nth v2 n))).

Parameter bw_xor:
  Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom Nth_bw_xor :
  forall (v1:Numbers.BinNums.Z) (v2:Numbers.BinNums.Z) (n:Numbers.BinNums.Z),
  (0%Z <= n)%Z /\ (n < 8%Z)%Z ->
  ((nth (bw_xor v1 v2) n) = (Init.Datatypes.xorb (nth v1 n) (nth v2 n))).

Parameter bw_not: Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom Nth_bw_not :
  forall (v:Numbers.BinNums.Z) (n:Numbers.BinNums.Z),
  (0%Z <= n)%Z /\ (n < 8%Z)%Z ->
  ((nth (bw_not v) n) = (Init.Datatypes.negb (nth v n))).

Parameter lsr: Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom Lsr_nth_low :
  forall (b:Numbers.BinNums.Z) (n:Numbers.BinNums.Z) (s:Numbers.BinNums.Z),
  (0%Z <= s)%Z -> (0%Z <= n)%Z -> ((n + s)%Z < 8%Z)%Z ->
  ((nth (lsr b s) n) = (nth b (n + s)%Z)).

Axiom Lsr_nth_high :
  forall (b:Numbers.BinNums.Z) (n:Numbers.BinNums.Z) (s:Numbers.BinNums.Z),
  (0%Z <= s)%Z -> (0%Z <= n)%Z -> (8%Z <= (n + s)%Z)%Z ->
  ((nth (lsr b s) n) = Init.Datatypes.false).

Axiom lsr_zeros : forall (x:Numbers.BinNums.Z), ((lsr x 0%Z) = x).

Parameter asr: Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom Asr_nth_low :
  forall (b:Numbers.BinNums.Z) (n:Numbers.BinNums.Z) (s:Numbers.BinNums.Z),
  (0%Z <= s)%Z -> (0%Z <= n)%Z /\ (n < 8%Z)%Z -> ((n + s)%Z < 8%Z)%Z ->
  ((nth (asr b s) n) = (nth b (n + s)%Z)).

Axiom Asr_nth_high :
  forall (b:Numbers.BinNums.Z) (n:Numbers.BinNums.Z) (s:Numbers.BinNums.Z),
  (0%Z <= s)%Z -> (0%Z <= n)%Z /\ (n < 8%Z)%Z -> (8%Z <= (n + s)%Z)%Z ->
  ((nth (asr b s) n) = (nth b (8%Z - 1%Z)%Z)).

Axiom asr_zeros : forall (x:Numbers.BinNums.Z), ((asr x 0%Z) = x).

Parameter lsl: Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom Lsl_nth_high :
  forall (b:Numbers.BinNums.Z) (n:Numbers.BinNums.Z) (s:Numbers.BinNums.Z),
  (0%Z <= s)%Z /\ (s <= n)%Z /\ (n < 8%Z)%Z ->
  ((nth (lsl b s) n) = (nth b (n - s)%Z)).

Axiom Lsl_nth_low :
  forall (b:Numbers.BinNums.Z) (n:Numbers.BinNums.Z) (s:Numbers.BinNums.Z),
  (0%Z <= n)%Z /\ (n < s)%Z -> ((nth (lsl b s) n) = Init.Datatypes.false).

Axiom lsl_zeros : forall (x:Numbers.BinNums.Z), ((lsl x 0%Z) = x).

Parameter rotate_right:
  Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom Nth_rotate_right :
  forall (v:Numbers.BinNums.Z) (n:Numbers.BinNums.Z) (i:Numbers.BinNums.Z),
  (0%Z <= i)%Z /\ (i < 8%Z)%Z -> (0%Z <= n)%Z ->
  ((nth (rotate_right v n) i) =
   (nth v (int.EuclideanDivision.mod1 (i + n)%Z 8%Z))).

Parameter rotate_left:
  Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom Nth_rotate_left :
  forall (v:Numbers.BinNums.Z) (n:Numbers.BinNums.Z) (i:Numbers.BinNums.Z),
  (0%Z <= i)%Z /\ (i < 8%Z)%Z -> (0%Z <= n)%Z ->
  ((nth (rotate_left v n) i) =
   (nth v (int.EuclideanDivision.mod1 (i - n)%Z 8%Z))).

Parameter is_signed_positive: Numbers.BinNums.Z -> Prop.

Parameter to_uint: Numbers.BinNums.Z -> Numbers.BinNums.Z.

Parameter of_int: Numbers.BinNums.Z -> Numbers.BinNums.Z.

Parameter to_int1: Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom to_int'def :
  forall (x:Numbers.BinNums.Z),
  (is_signed_positive x -> ((to_int1 x) = (to_uint x))) /\
  (~ is_signed_positive x -> ((to_int1 x) = (-(256%Z - (to_uint x))%Z)%Z)).

Axiom to_uint_extensionality :
  forall (v:Numbers.BinNums.Z) (v':Numbers.BinNums.Z),
  ((to_uint v) = (to_uint v')) -> (v = v').

Axiom to_int_extensionality :
  forall (v:Numbers.BinNums.Z) (v':Numbers.BinNums.Z),
  ((to_int1 v) = (to_int1 v')) -> (v = v').

(* Why3 assumption *)
Definition uint_in_range (i:Numbers.BinNums.Z) : Prop :=
  (0%Z <= i)%Z /\ (i <= (256%Z - 1%Z)%Z)%Z.

Axiom to_uint_bounds :
  forall (v:Numbers.BinNums.Z),
  (0%Z <= (to_uint v))%Z /\ ((to_uint v) < 256%Z)%Z.

Axiom to_uint_of_int :
  forall (i:Numbers.BinNums.Z), (0%Z <= i)%Z /\ (i < 256%Z)%Z ->
  ((to_uint (of_int i)) = i).

Parameter size_bv: Numbers.BinNums.Z.

Axiom to_uint_size_bv : ((to_uint size_bv) = 8%Z).

Axiom to_uint_zeros : ((to_uint zeros) = 0%Z).

Axiom to_uint_one : ((to_uint one) = 1%Z).

Axiom to_uint_ones : ((to_uint ones) = (256%Z - 1%Z)%Z).

(* Why3 assumption *)
Definition ult (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z) : Prop :=
  ((to_uint x) < (to_uint y))%Z.

(* Why3 assumption *)
Definition ule (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z) : Prop :=
  ((to_uint x) <= (to_uint y))%Z.

(* Why3 assumption *)
Definition ugt (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z) : Prop :=
  ((to_uint y) < (to_uint x))%Z.

(* Why3 assumption *)
Definition uge (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z) : Prop :=
  ((to_uint y) <= (to_uint x))%Z.

(* Why3 assumption *)
Definition slt (v1:Numbers.BinNums.Z) (v2:Numbers.BinNums.Z) : Prop :=
  ((to_int1 v1) < (to_int1 v2))%Z.

(* Why3 assumption *)
Definition sle (v1:Numbers.BinNums.Z) (v2:Numbers.BinNums.Z) : Prop :=
  ((to_int1 v1) <= (to_int1 v2))%Z.

(* Why3 assumption *)
Definition sgt (v1:Numbers.BinNums.Z) (v2:Numbers.BinNums.Z) : Prop :=
  ((to_int1 v2) < (to_int1 v1))%Z.

(* Why3 assumption *)
Definition sge (v1:Numbers.BinNums.Z) (v2:Numbers.BinNums.Z) : Prop :=
  ((to_int1 v2) <= (to_int1 v1))%Z.

Axiom positive_is_ge_zeros :
  forall (x:Numbers.BinNums.Z), is_signed_positive x <-> sge x zeros.

Parameter add: Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom to_uint_add :
  forall (v1:Numbers.BinNums.Z) (v2:Numbers.BinNums.Z),
  ((to_uint (add v1 v2)) =
   (int.EuclideanDivision.mod1 ((to_uint v1) + (to_uint v2))%Z 256%Z)).

Axiom to_uint_add_bounded :
  forall (v1:Numbers.BinNums.Z) (v2:Numbers.BinNums.Z),
  (((to_uint v1) + (to_uint v2))%Z < 256%Z)%Z ->
  ((to_uint (add v1 v2)) = ((to_uint v1) + (to_uint v2))%Z).

Parameter sub: Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom to_uint_sub :
  forall (v1:Numbers.BinNums.Z) (v2:Numbers.BinNums.Z),
  ((to_uint (sub v1 v2)) =
   (int.EuclideanDivision.mod1 ((to_uint v1) - (to_uint v2))%Z 256%Z)).

Axiom to_uint_sub_bounded :
  forall (v1:Numbers.BinNums.Z) (v2:Numbers.BinNums.Z),
  (0%Z <= ((to_uint v1) - (to_uint v2))%Z)%Z /\
  (((to_uint v1) - (to_uint v2))%Z < 256%Z)%Z ->
  ((to_uint (sub v1 v2)) = ((to_uint v1) - (to_uint v2))%Z).

Parameter neg: Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom to_uint_neg :
  forall (v:Numbers.BinNums.Z),
  ((to_uint (neg v)) = (int.EuclideanDivision.mod1 (-(to_uint v))%Z 256%Z)).

Parameter mul: Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom to_uint_mul :
  forall (v1:Numbers.BinNums.Z) (v2:Numbers.BinNums.Z),
  ((to_uint (mul v1 v2)) =
   (int.EuclideanDivision.mod1 ((to_uint v1) * (to_uint v2))%Z 256%Z)).

Axiom to_uint_mul_bounded :
  forall (v1:Numbers.BinNums.Z) (v2:Numbers.BinNums.Z),
  (((to_uint v1) * (to_uint v2))%Z < 256%Z)%Z ->
  ((to_uint (mul v1 v2)) = ((to_uint v1) * (to_uint v2))%Z).

Parameter udiv: Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom to_uint_udiv :
  forall (v1:Numbers.BinNums.Z) (v2:Numbers.BinNums.Z),
  ((to_uint (udiv v1 v2)) =
   (int.EuclideanDivision.div (to_uint v1) (to_uint v2))).

Parameter urem: Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom to_uint_urem :
  forall (v1:Numbers.BinNums.Z) (v2:Numbers.BinNums.Z),
  ((to_uint (urem v1 v2)) =
   (int.EuclideanDivision.mod1 (to_uint v1) (to_uint v2))).

Parameter lsr_bv:
  Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom lsr_bv_is_lsr :
  forall (x:Numbers.BinNums.Z) (n:Numbers.BinNums.Z),
  ((lsr_bv x n) = (lsr x (to_uint n))).

Axiom to_uint_lsr :
  forall (v:Numbers.BinNums.Z) (n:Numbers.BinNums.Z),
  ((to_uint (lsr_bv v n)) =
   (int.EuclideanDivision.div (to_uint v) (bv.Pow2int.pow2 (to_uint n)))).

Parameter asr_bv:
  Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom asr_bv_is_asr :
  forall (x:Numbers.BinNums.Z) (n:Numbers.BinNums.Z),
  ((asr_bv x n) = (asr x (to_uint n))).

Parameter lsl_bv:
  Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom lsl_bv_is_lsl :
  forall (x:Numbers.BinNums.Z) (n:Numbers.BinNums.Z),
  ((lsl_bv x n) = (lsl x (to_uint n))).

Axiom to_uint_lsl :
  forall (v:Numbers.BinNums.Z) (n:Numbers.BinNums.Z),
  ((to_uint (lsl_bv v n)) =
   (int.EuclideanDivision.mod1
    ((to_uint v) * (bv.Pow2int.pow2 (to_uint n)))%Z 256%Z)).

Parameter rotate_right_bv:
  Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Parameter rotate_left_bv:
  Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom rotate_left_bv_is_rotate_left :
  forall (v:Numbers.BinNums.Z) (n:Numbers.BinNums.Z),
  ((rotate_left_bv v n) = (rotate_left v (to_uint n))).

Axiom rotate_right_bv_is_rotate_right :
  forall (v:Numbers.BinNums.Z) (n:Numbers.BinNums.Z),
  ((rotate_right_bv v n) = (rotate_right v (to_uint n))).

Parameter nth_bv:
  Numbers.BinNums.Z -> Numbers.BinNums.Z -> Init.Datatypes.bool.

Axiom nth_bv_def :
  forall (x:Numbers.BinNums.Z) (i:Numbers.BinNums.Z),
  ((nth_bv x i) = Init.Datatypes.true) <->
  ~ ((bw_and (lsr_bv x i) one) = zeros).

Axiom Nth_bv_is_nth :
  forall (x:Numbers.BinNums.Z) (i:Numbers.BinNums.Z),
  ((nth x (to_uint i)) = (nth_bv x i)).

Axiom Nth_bv_is_nth2 :
  forall (x:Numbers.BinNums.Z) (i:Numbers.BinNums.Z),
  (0%Z <= i)%Z /\ (i < 256%Z)%Z -> ((nth_bv x (of_int i)) = (nth x i)).

Parameter eq_sub_bv:
  Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z ->
  Numbers.BinNums.Z -> Prop.

Axiom eq_sub_bv_def :
  forall (a:Numbers.BinNums.Z) (b:Numbers.BinNums.Z) (i:Numbers.BinNums.Z)
    (n:Numbers.BinNums.Z),
  let mask := lsl_bv (sub (lsl_bv one n) one) i in
  eq_sub_bv a b i n <-> ((bw_and b mask) = (bw_and a mask)).

(* Why3 assumption *)
Definition eq_sub (a:Numbers.BinNums.Z) (b:Numbers.BinNums.Z)
    (i:Numbers.BinNums.Z) (n:Numbers.BinNums.Z) : Prop :=
  forall (j:Numbers.BinNums.Z), (i <= j)%Z /\ (j < (i + n)%Z)%Z ->
  ((nth a j) = (nth b j)).

Axiom eq_sub_equiv :
  forall (a:Numbers.BinNums.Z) (b:Numbers.BinNums.Z) (i:Numbers.BinNums.Z)
    (n:Numbers.BinNums.Z),
  eq_sub a b (to_uint i) (to_uint n) <-> eq_sub_bv a b i n.

Axiom Extensionality :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z), eq_sub x y 0%Z 8%Z ->
  (x = y).

Axiom state : Type.
Parameter state_WhyType : WhyType state.
Existing Instance state_WhyType.

(* Why3 assumption *)
Definition param (s:t6) (i:Numbers.BinNums.Z) : Numbers.BinNums.Z :=
  list.NthNoOpt.nth i (cd s).

(* Why3 assumption *)
Definition ret1 (s:t6) (v:Numbers.BinNums.Z) : t6 :=
  t'mk4 (Init.Datatypes.cons v Init.Datatypes.nil) (cd s) (m s) (st s)
  (msg s) (subs s) (pc s) (e_stat s).

(* Why3 assumption *)
Definition ret2 (s:t6) (v1:Numbers.BinNums.Z) (v2:Numbers.BinNums.Z) : t6 :=
  t'mk4 (Init.Datatypes.cons v1 (Init.Datatypes.cons v2 Init.Datatypes.nil))
  (cd s) (m s) (st s) (msg s) (subs s) (pc s) (e_stat s).

(* Why3 assumption *)
Definition add1 (s:t6) : t6 := ret1 s ((param s 0%Z) + (param s 1%Z))%Z.

(* Why3 assumption *)
Definition sub1 (s:t6) : t6 := ret1 s ((param s 0%Z) - (param s 1%Z))%Z.

(* Why3 assumption *)
Definition mul1 (s:t6) : t6 := ret1 s ((param s 0%Z) * (param s 1%Z))%Z.

(* Why3 assumption *)
Definition div (s:t6) : t6 :=
  ret1 s (ZArith.BinInt.Z.quot (param s 0%Z) (param s 1%Z)).

(* Why3 assumption *)
Definition mod1 (s:t6) : t6 :=
  ret1 s (ZArith.BinInt.Z.rem (param s 0%Z) (param s 1%Z)).

Parameter lt: t6 -> t6.

Axiom lt'def :
  forall (s:t6),
  (((param s 0%Z) < (param s 1%Z))%Z ->
   ((lt s) = (ret1 s (b2i Init.Datatypes.true)))) /\
  (~ ((param s 0%Z) < (param s 1%Z))%Z ->
   ((lt s) = (ret1 s (b2i Init.Datatypes.false)))).

Parameter gt: t6 -> t6.

Axiom gt'def :
  forall (s:t6),
  (((param s 1%Z) < (param s 0%Z))%Z ->
   ((gt s) = (ret1 s (b2i Init.Datatypes.true)))) /\
  (~ ((param s 1%Z) < (param s 0%Z))%Z ->
   ((gt s) = (ret1 s (b2i Init.Datatypes.false)))).

Parameter slt1: t6 -> t6.

Axiom slt'def :
  forall (s:t6),
  (((param s 0%Z) < (param s 1%Z))%Z ->
   ((slt1 s) = (ret1 s (b2i Init.Datatypes.true)))) /\
  (~ ((param s 0%Z) < (param s 1%Z))%Z ->
   ((slt1 s) = (ret1 s (b2i Init.Datatypes.false)))).

Parameter sgt1: t6 -> t6.

Axiom sgt'def :
  forall (s:t6),
  (((param s 1%Z) < (param s 0%Z))%Z ->
   ((sgt1 s) = (ret1 s (b2i Init.Datatypes.true)))) /\
  (~ ((param s 1%Z) < (param s 0%Z))%Z ->
   ((sgt1 s) = (ret1 s (b2i Init.Datatypes.false)))).

Parameter eq: t6 -> t6.

Axiom eq'def :
  forall (s:t6),
  (((param s 0%Z) = (param s 1%Z)) ->
   ((eq s) = (ret1 s (b2i Init.Datatypes.true)))) /\
  (~ ((param s 0%Z) = (param s 1%Z)) ->
   ((eq s) = (ret1 s (b2i Init.Datatypes.false)))).

Parameter iszero: t6 -> t6.

Axiom iszero'def :
  forall (s:t6),
  (((param s 0%Z) = 0%Z) ->
   ((iszero s) = (ret1 s (b2i Init.Datatypes.true)))) /\
  (~ ((param s 0%Z) = 0%Z) ->
   ((iszero s) = (ret1 s (b2i Init.Datatypes.false)))).

Parameter and: t6 -> t6.

Axiom and'def :
  forall (s:t6),
  (((i2b (param s 0%Z)) = Init.Datatypes.true) ->
   ((and s) = (ret1 s (b2i (i2b (param s 1%Z)))))) /\
  (~ ((i2b (param s 0%Z)) = Init.Datatypes.true) ->
   ((and s) = (ret1 s (b2i Init.Datatypes.false)))).

Parameter or: t6 -> t6.

Axiom or'def :
  forall (s:t6),
  (((i2b (param s 0%Z)) = Init.Datatypes.true) ->
   ((or s) = (ret1 s (b2i Init.Datatypes.true)))) /\
  (~ ((i2b (param s 0%Z)) = Init.Datatypes.true) ->
   ((or s) = (ret1 s (b2i (i2b (param s 1%Z)))))).

(* Why3 assumption *)
Definition bw_not1 (s:t6) : t6 := ret1 s (bw_not (param s 0%Z)).

(* Why3 assumption *)
Definition bw_and1 (s:t6) : t6 :=
  ret1 s (bw_and (param s 0%Z) (param s 1%Z)).

(* Why3 assumption *)
Definition bw_or1 (s:t6) : t6 := ret1 s (bw_or (param s 0%Z) (param s 1%Z)).

(* Why3 assumption *)
Definition bw_xor1 (s:t6) : t6 :=
  ret1 s (bw_xor (param s 0%Z) (param s 1%Z)).

(* Why3 assumption *)
Definition shl (s:t6) : t6 := ret1 s (lsl (param s 0%Z) (param s 1%Z)).

(* Why3 assumption *)
Definition shr (s:t6) : t6 := ret1 s (lsr (param s 0%Z) (param s 1%Z)).

(* Why3 assumption *)
Definition mload (s:t6) : t6 :=
  let mem' := get_mem (param s 0%Z) (m s) in
  t'mk4 (Init.Datatypes.cons (peek mem') Init.Datatypes.nil) (cd s) mem'
  (st s) (msg s) (subs s) (pc s) (e_stat s).

(* Why3 assumption *)
Definition mstore (s:t6) : t6 :=
  t'mk4 (sk s) (cd s) (set_mem (param s 0%Z) (param s 1%Z) (m s)) (st s)
  (msg s) (subs s) (pc s) (e_stat s).

(* Why3 assumption *)
Definition sload (s:t6) : t6 := ret1 s (get_storage (st s) (param s 0%Z)).

Parameter sstore: t6 -> t6.

Axiom sstore'def :
  forall (s:t6), ~ ((st s) = Init.Datatypes.nil) ->
  ((sstore s) =
   (t'mk4 (sk s) (cd s) (m s)
    (set_storage (st s) (param s 0%Z) (param s 1%Z)) (msg s) (subs s) 
    (pc s) (e_stat s))).

(* Why3 assumption *)
Definition log1 (s:t6) : t6 :=
  t'mk4 (sk s) (cd s) (m s) (st s) (msg s)
  (add_log (subs s) (Init.Datatypes.cons (param s 2%Z) Init.Datatypes.nil)
   (get_mem_range (m s) (param s 0%Z) (param s 1%Z)))
  (pc s) (e_stat s).

(* Why3 assumption *)
Definition caller (s:t6) : t6 := ret1 s (sender (msg s)).

(* Why3 assumption *)
Definition callvalue (s:t6) : t6 := ret1 s (value (msg s)).

(* Why3 assumption *)
Definition calldatacopy (s:t6) : t6 :=
  t'mk4 (sk s) (cd s)
  (copy_block_data_to_mem (m s) (cd s) (param s 0%Z) (param s 1%Z)
   (param s 2%Z))
  (st s) (msg s) (subs s) (pc s) (e_stat s).

(* Why3 assumption *)
Definition stop (s:t6) : t6 :=
  t'mk4 (sk s) (cd s) (m s) (st s) (msg s) (subs s) (pc s)
  (let q_ := e_stat s in
   exit_status'mk Init.Datatypes.true (e_gas q_) (e_data q_) Stop_instruction).

(* Why3 assumption *)
Definition revert (s:t6) : t6 :=
  t'mk4 (sk s) (cd s) (m s) (st s) (msg s) (subs s) (pc s)
  (let q_ := e_stat s in
   exit_status'mk Init.Datatypes.true (e_gas q_) (e_data q_)
   Revert_instruction).

(* Why3 assumption *)
Definition invalid (s:t6) : t6 :=
  t'mk4 (sk s) (cd s) (m s) (st s) (msg s) (subs s) (pc s)
  (let q_ := e_stat s in
   exit_status'mk Init.Datatypes.true (e_gas q_) (e_data q_)
   Invalid_instruction).

Parameter zero_value_for_split_t_array__t_address__dyn_memory_ptr: t6 -> t6.

Axiom zero_value_for_split_t_array__t_address__dyn_memory_ptr'spec :
  forall (st_c:t6),
  ((0%Z <=
    (ur (zero_value_for_split_t_array__t_address__dyn_memory_ptr st_c)))%Z /\
   ((ur (zero_value_for_split_t_array__t_address__dyn_memory_ptr st_c)) <=
    255%Z)%Z) /\
  ((ur (zero_value_for_split_t_array__t_address__dyn_memory_ptr st_c)) =
   96%Z).

Parameter zero_value_for_split_t_address: t6 -> t6.

Axiom zero_value_for_split_t_address'spec :
  forall (st_c:t6),
  ((0%Z <= (ur (zero_value_for_split_t_address st_c)))%Z /\
   ((ur (zero_value_for_split_t_address st_c)) <= 255%Z)%Z) /\
  ((ur (zero_value_for_split_t_address st_c)) = 0%Z).

Parameter zero_memory_chunk_t_address:
  t6 -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> t6.

Parameter shift_right_0_unsigned: t6 -> Numbers.BinNums.Z -> t6.

Parameter shift_left_dynamic:
  t6 -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> t6.

Parameter shift_left_0: t6 -> Numbers.BinNums.Z -> t6.

Parameter require_helper: t6 -> Numbers.BinNums.Z -> t6.

Parameter prepare_store_t_uint256: t6 -> Numbers.BinNums.Z -> t6.

Parameter prepare_store_t_address: t6 -> Numbers.BinNums.Z -> t6.

Parameter cleanup_t_uint160: t6 -> Numbers.BinNums.Z -> t6.

Parameter cleanup_from_storage_t_uint256: t6 -> Numbers.BinNums.Z -> t6.

Parameter cleanup_from_storage_t_address: t6 -> Numbers.BinNums.Z -> t6.

Parameter array_length_t_array__t_address__dyn_memory_ptr:
  t6 -> Numbers.BinNums.Z -> t6.

Parameter array_allocation_size_t_array__t_address__dyn_memory_ptr:
  t6 -> Numbers.BinNums.Z -> t6.

Axiom array_allocation_size_t_array__t_address__dyn_memory_ptr'spec :
  forall (st_c:t6) (length1:Numbers.BinNums.Z),
  (0%Z <= length1)%Z /\ (length1 <= 255%Z)%Z ->
  ((ur
    (array_allocation_size_t_array__t_address__dyn_memory_ptr st_c length1))
   = ((length1 * 32%Z)%Z + 32%Z)%Z).

Parameter allocateMemory: t6 -> Numbers.BinNums.Z -> t6.

Parameter abi_decode_tuple__fromMemory:
  t6 -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> t6.

Parameter update_byte_slice_dynamic20:
  t6 -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> t6.

Parameter update_byte_slice_32_shift_0:
  t6 -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> t6.

Parameter update_byte_slice_20_shift_0:
  t6 -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> t6.

Parameter memory_array_index_access_t_array__t_address__dyn_memory_ptr:
  t6 -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> t6.

Parameter extract_from_storage_value_offset_0t_uint256:
  t6 -> Numbers.BinNums.Z -> t6.

Parameter extract_from_storage_value_offset_0t_address:
  t6 -> Numbers.BinNums.Z -> t6.

Parameter convert_t_uint160_to_t_uint160: t6 -> Numbers.BinNums.Z -> t6.

Parameter cleanup_t_address: t6 -> Numbers.BinNums.Z -> t6.

Parameter allocate_and_zero_memory_array_t_array__t_address__dyn_memory_ptr:
  t6 -> Numbers.BinNums.Z -> t6.

Parameter write_to_memory_t_address:
  t6 -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> t6.

Parameter update_storage_value_t_address:
  t6 -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> t6.

Parameter update_storage_value_offset_0t_uint256:
  t6 -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> t6.

Parameter update_storage_value_offset_0t_address:
  t6 -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> t6.

Parameter read_from_storage_offset_0_t_uint256:
  t6 -> Numbers.BinNums.Z -> t6.

Parameter read_from_storage_offset_0_t_address:
  t6 -> Numbers.BinNums.Z -> t6.

Parameter convert_t_uint160_to_t_address: t6 -> Numbers.BinNums.Z -> t6.

Parameter storage_set_to_zero_t_address:
  t6 -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> t6.

Parameter convert_t_address_to_t_address: t6 -> Numbers.BinNums.Z -> t6.

Parameter convert_t_address_payable_to_t_address:
  t6 -> Numbers.BinNums.Z -> t6.

Parameter mapping_index_access_t_mapping__t_address___t_uint256___of_t_address_payable:
  t6 -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> t6.

Parameter mapping_index_access_t_mapping__t_address___t_uint256___of_t_address:
  t6 -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> t6.

Parameter mapping_index_access_t_mapping__t_address___t_address___of_t_address_payable:
  t6 -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> t6.

Parameter mapping_index_access_t_mapping__t_address___t_address___of_t_address:
  t6 -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> t6.

(* Why3 goal *)
Theorem fun_topStakers_234'vc :
  forall (st_c:t6) (vloc_count_179:Numbers.BinNums.Z),
  (0%Z <= vloc_count_179)%Z /\ (vloc_count_179 <= 255%Z)%Z ->
  let o := zero_value_for_split_t_array__t_address__dyn_memory_ptr st_c in
  ((0%Z <= (ur o))%Z /\ ((ur o) <= 255%Z)%Z) /\ ((ur o) = 96%Z) ->
  forall (st_g:t6), (st_g = o) -> forall (usr:Numbers.BinNums.Z),
  (usr = (ur st_g)) ->
  ((0%Z <= vloc_count_179)%Z /\ (vloc_count_179 <= 255%Z)%Z) /\
  (forall (st_g1:t6),
   (st_g1 =
    (allocate_and_zero_memory_array_t_array__t_address__dyn_memory_ptr st_g
     vloc_count_179)) ->
   (let rv := ur st_g1 in
    ((0%Z <= 0%Z)%Z /\ (0%Z <= 255%Z)%Z) /\
    (forall (st_g2:t6),
     (st_g2 = (read_from_storage_offset_0_t_address st_g1 0%Z)) ->
     (let rv1 := ur st_g2 in
      (((0%Z <= 3%Z)%Z /\ (3%Z <= 255%Z)%Z) /\
       (0%Z <= rv1)%Z /\ (rv1 <= 255%Z)%Z) /\
      (forall (st_g3:t6),
       (st_g3 =
        (mapping_index_access_t_mapping__t_address___t_address___of_t_address
         st_g2 3%Z rv1)) ->
       (let rv2 := ur st_g3 in
        ((0%Z <= rv2)%Z /\ (rv2 <= 255%Z)%Z) /\
        (forall (st_g4:t6),
         (st_g4 = (read_from_storage_offset_0_t_address st_g3 rv2)) ->
         (let rv3 := ur st_g4 in
          forall (st_g5:t6), ~ ((i2b1 1%Z) = Init.Datatypes.true) ->
          ((0%Z <= 1%Z)%Z /\ (1%Z <= 255%Z)%Z) /\
          (forall (st_g6:t6),
           (st_g6 = (read_from_storage_offset_0_t_address st_g5 1%Z)) ->
           (forall (st_g7:t6),
            (st_g7 =
             (lp st_g6
              (Init.Datatypes.cons rv3
               (Init.Datatypes.cons (ur st_g6) Init.Datatypes.nil)))) ->
            (forall (st_g8:t6), (st_g8 = (eq st_g7)) ->
             (forall (st_g9:t6),
              (st_g9 =
               (lp st_g8 (Init.Datatypes.cons (ur st_g8) Init.Datatypes.nil))) ->
              (forall (st_g10:t6), (st_g10 = (iszero st_g9)) ->
               (let rv4 := ur st_g10 in
                (((i2b1 rv4) = Init.Datatypes.true) ->
                 (forall (st_g11:t6),
                  (st_g11 =
                   (lp st_g10
                    (Init.Datatypes.cons 0%Z
                     (Init.Datatypes.cons vloc_count_179 Init.Datatypes.nil)))) ->
                  (forall (st_g12:t6), (st_g12 = (lt st_g11)) ->
                   (forall (st_g13:t6),
                    (st_g13 =
                     (lp st_g12 (Init.Datatypes.cons rv4 Init.Datatypes.nil))) ->
                    (forall (st_g14:t6), (st_g14 = (iszero st_g13)) ->
                     ~ ((i2b1 (ur st_g14)) = Init.Datatypes.true) ->
                     (((0%Z <= rv)%Z /\ (rv <= 255%Z)%Z) /\
                      (0%Z <= 0%Z)%Z /\ (0%Z <= 255%Z)%Z) /\
                     (forall (st_g15:t6),
                      (st_g15 =
                       (memory_array_index_access_t_array__t_address__dyn_memory_ptr
                        st_g14 rv 0%Z)) ->
                      (forall (st_g16:t6),
                       (st_g16 =
                        (write_to_memory_t_address st_g15 (ur st_g15) rv3)) ->
                       (forall (st_g17:t6),
                        (st_g17 =
                         (lp st_g16
                          (Init.Datatypes.cons 0%Z
                           (Init.Datatypes.cons 1%Z Init.Datatypes.nil)))) ->
                        (forall (st_g18:t6), (st_g18 = (add1 st_g17)) ->
                         (let rv5 := ur st_g18 in
                          ((0%Z <= rv5)%Z /\ (rv5 <= 255%Z)%Z) /\
                          (((0%Z <= 3%Z)%Z /\ (3%Z <= 255%Z)%Z) /\
                           (0%Z <= rv3)%Z /\ (rv3 <= 255%Z)%Z) /\
                          (forall (st_g19:t6),
                           (st_g19 =
                            (mapping_index_access_t_mapping__t_address___t_address___of_t_address
                             st_g18 3%Z rv3)) ->
                           (let rv6 := ur st_g19 in
                            ((0%Z <= rv6)%Z /\ (rv6 <= 255%Z)%Z) /\
                            (forall (st_g20:t6),
                             ~ (st_g20 =
                                (read_from_storage_offset_0_t_address st_g19
                                 rv6))))))))))))))) /\
                (~ ((i2b1 rv4) = Init.Datatypes.true) ->
                 (forall (st_g11:t6),
                  (st_g11 =
                   (lp st_g10 (Init.Datatypes.cons rv4 Init.Datatypes.nil))) ->
                  (forall (st_g12:t6), (st_g12 = (iszero st_g11)) ->
                   ~ ((i2b1 (ur st_g12)) = Init.Datatypes.true) ->
                   (((0%Z <= rv)%Z /\ (rv <= 255%Z)%Z) /\
                    (0%Z <= 0%Z)%Z /\ (0%Z <= 255%Z)%Z) /\
                   (forall (st_g13:t6),
                    (st_g13 =
                     (memory_array_index_access_t_array__t_address__dyn_memory_ptr
                      st_g12 rv 0%Z)) ->
                    (forall (st_g14:t6),
                     (st_g14 =
                      (write_to_memory_t_address st_g13 (ur st_g13) rv3)) ->
                     (forall (st_g15:t6),
                      (st_g15 =
                       (lp st_g14
                        (Init.Datatypes.cons 0%Z
                         (Init.Datatypes.cons 1%Z Init.Datatypes.nil)))) ->
                      (forall (st_g16:t6), (st_g16 = (add1 st_g15)) ->
                       (let rv5 := ur st_g16 in
                        ((0%Z <= rv5)%Z /\ (rv5 <= 255%Z)%Z) /\
                        (((0%Z <= 3%Z)%Z /\ (3%Z <= 255%Z)%Z) /\
                         (0%Z <= rv3)%Z /\ (rv3 <= 255%Z)%Z) /\
                        (forall (st_g17:t6),
                         (st_g17 =
                          (mapping_index_access_t_mapping__t_address___t_address___of_t_address
                           st_g16 3%Z rv3)) ->
                         (let rv6 := ur st_g17 in
                          ((0%Z <= rv6)%Z /\ (rv6 <= 255%Z)%Z) /\
                          (forall (st_g18:t6),
                           ~ (st_g18 =
                              (read_from_storage_offset_0_t_address st_g17
                               rv6))))))))))))))))))))))))))).
Proof.
intros st_c vloc_count_179 (h1,h2) o ((h3,h4),h5) st_g h6 usr h7.

Qed.

