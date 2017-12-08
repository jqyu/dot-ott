Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export Definitions.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme varref_ind' := Induction for varref Sort Prop.

Definition varref_mutind :=
  fun H1 H2 H3 =>
  varref_ind' H1 H2 H3.

Scheme varref_rec' := Induction for varref Sort Set.

Definition varref_mutrec :=
  fun H1 H2 H3 =>
  varref_rec' H1 H2 H3.

Scheme typ_ind' := Induction for typ Sort Prop
  with dec_ind' := Induction for dec Sort Prop.

Definition typ_dec_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  (conj (typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)
  (dec_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)).

Scheme typ_rec' := Induction for typ Sort Set
  with dec_rec' := Induction for dec Sort Set.

Definition typ_dec_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  (pair (typ_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)
  (dec_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)).

Scheme def_ind' := Induction for def Sort Prop
  with defs_ind' := Induction for defs Sort Prop
  with val_ind' := Induction for val Sort Prop
  with trm_ind' := Induction for trm Sort Prop.

Definition def_defs_val_trm_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  (conj (def_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  ((conj (defs_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  ((conj (val_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  (trm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)))))).

Scheme def_rec' := Induction for def Sort Set
  with defs_rec' := Induction for defs Sort Set
  with val_rec' := Induction for val Sort Set
  with trm_rec' := Induction for trm Sort Set.

Definition def_defs_val_trm_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  (pair ((pair ((pair (def_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  (defs_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)))
  (val_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)))
  (trm_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)).


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_varref_wrt_varref_rec (n1 : nat) (x1 : termvar) (v1 : varref) {struct v1} : varref :=
  match v1 with
    | var_termvar_f x2 => if (x1 == x2) then (var_termvar_b n1) else (var_termvar_f x2)
    | var_termvar_b n2 => if (lt_ge_dec n2 n1) then (var_termvar_b n2) else (var_termvar_b (S n2))
  end.

Definition close_varref_wrt_varref x1 v1 := close_varref_wrt_varref_rec 0 x1 v1.

Fixpoint close_typ_wrt_varref_rec (n1 : nat) (x1 : termvar) (T1 : typ) {struct T1} : typ :=
  match T1 with
    | typ_all T2 T3 => typ_all (close_typ_wrt_varref_rec n1 x1 T2) (close_typ_wrt_varref_rec (S n1) x1 T3)
    | typ_bnd T2 => typ_bnd (close_typ_wrt_varref_rec (S n1) x1 T2)
    | typ_dec dec1 => typ_dec (close_dec_wrt_varref_rec n1 x1 dec1)
    | typ_sel v1 A1 => typ_sel (close_varref_wrt_varref_rec n1 x1 v1) A1
    | typ_and T2 T3 => typ_and (close_typ_wrt_varref_rec n1 x1 T2) (close_typ_wrt_varref_rec n1 x1 T3)
    | typ_top => typ_top
    | typ_bot => typ_bot
  end

with close_dec_wrt_varref_rec (n1 : nat) (x1 : termvar) (dec1 : dec) {struct dec1} : dec :=
  match dec1 with
    | dec_trm a1 T1 => dec_trm a1 (close_typ_wrt_varref_rec n1 x1 T1)
    | dec_typ A1 T1 T2 => dec_typ A1 (close_typ_wrt_varref_rec n1 x1 T1) (close_typ_wrt_varref_rec n1 x1 T2)
  end.

Definition close_typ_wrt_varref x1 T1 := close_typ_wrt_varref_rec 0 x1 T1.

Definition close_dec_wrt_varref x1 dec1 := close_dec_wrt_varref_rec 0 x1 dec1.

Fixpoint close_def_wrt_varref_rec (n1 : nat) (x1 : termvar) (d1 : def) {struct d1} : def :=
  match d1 with
    | def_trm a1 t1 => def_trm a1 (close_trm_wrt_varref_rec n1 x1 t1)
    | def_typ A1 T1 => def_typ A1 (close_typ_wrt_varref_rec n1 x1 T1)
  end

with close_defs_wrt_varref_rec (n1 : nat) (x1 : termvar) (defs1 : defs) {struct defs1} : defs :=
  match defs1 with
    | defs_nil => defs_nil
    | defs_cons d1 defs2 => defs_cons (close_def_wrt_varref_rec n1 x1 d1) (close_defs_wrt_varref_rec n1 x1 defs2)
  end

with close_val_wrt_varref_rec (n1 : nat) (x1 : termvar) (val1 : val) {struct val1} : val :=
  match val1 with
    | val_new T1 defs1 => val_new (close_typ_wrt_varref_rec n1 x1 T1) (close_defs_wrt_varref_rec (S n1) x1 defs1)
    | val_lambda T1 t1 => val_lambda (close_typ_wrt_varref_rec n1 x1 T1) (close_trm_wrt_varref_rec (S n1) x1 t1)
  end

with close_trm_wrt_varref_rec (n1 : nat) (x1 : termvar) (t1 : trm) {struct t1} : trm :=
  match t1 with
    | trm_var v1 => trm_var (close_varref_wrt_varref_rec n1 x1 v1)
    | trm_val val1 => trm_val (close_val_wrt_varref_rec n1 x1 val1)
    | trm_sel v1 a1 => trm_sel (close_varref_wrt_varref_rec n1 x1 v1) a1
    | trm_app v1 v2 => trm_app (close_varref_wrt_varref_rec n1 x1 v1) (close_varref_wrt_varref_rec n1 x1 v2)
    | trm_let t2 t3 => trm_let (close_trm_wrt_varref_rec n1 x1 t2) (close_trm_wrt_varref_rec (S n1) x1 t3)
  end.

Definition close_def_wrt_varref x1 d1 := close_def_wrt_varref_rec 0 x1 d1.

Definition close_defs_wrt_varref x1 defs1 := close_defs_wrt_varref_rec 0 x1 defs1.

Definition close_val_wrt_varref x1 val1 := close_val_wrt_varref_rec 0 x1 val1.

Definition close_trm_wrt_varref x1 t1 := close_trm_wrt_varref_rec 0 x1 t1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_varref (v1 : varref) {struct v1} : nat :=
  match v1 with
    | var_termvar_f x1 => 1
    | var_termvar_b n1 => 1
  end.

Fixpoint size_typ (T1 : typ) {struct T1} : nat :=
  match T1 with
    | typ_all T2 T3 => 1 + (size_typ T2) + (size_typ T3)
    | typ_bnd T2 => 1 + (size_typ T2)
    | typ_dec dec1 => 1 + (size_dec dec1)
    | typ_sel v1 A1 => 1 + (size_varref v1)
    | typ_and T2 T3 => 1 + (size_typ T2) + (size_typ T3)
    | typ_top => 1
    | typ_bot => 1
  end

with size_dec (dec1 : dec) {struct dec1} : nat :=
  match dec1 with
    | dec_trm a1 T1 => 1 + (size_typ T1)
    | dec_typ A1 T1 T2 => 1 + (size_typ T1) + (size_typ T2)
  end.

Fixpoint size_def (d1 : def) {struct d1} : nat :=
  match d1 with
    | def_trm a1 t1 => 1 + (size_trm t1)
    | def_typ A1 T1 => 1 + (size_typ T1)
  end

with size_defs (defs1 : defs) {struct defs1} : nat :=
  match defs1 with
    | defs_nil => 1
    | defs_cons d1 defs2 => 1 + (size_def d1) + (size_defs defs2)
  end

with size_val (val1 : val) {struct val1} : nat :=
  match val1 with
    | val_new T1 defs1 => 1 + (size_typ T1) + (size_defs defs1)
    | val_lambda T1 t1 => 1 + (size_typ T1) + (size_trm t1)
  end

with size_trm (t1 : trm) {struct t1} : nat :=
  match t1 with
    | trm_var v1 => 1 + (size_varref v1)
    | trm_val val1 => 1 + (size_val val1)
    | trm_sel v1 a1 => 1 + (size_varref v1)
    | trm_app v1 v2 => 1 + (size_varref v1) + (size_varref v2)
    | trm_let t2 t3 => 1 + (size_trm t2) + (size_trm t3)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_varref_wrt_varref : nat -> varref -> Prop :=
  | degree_wrt_varref_var_termvar_f : forall n1 x1,
    degree_varref_wrt_varref n1 (var_termvar_f x1)
  | degree_wrt_varref_var_termvar_b : forall n1 n2,
    lt n2 n1 ->
    degree_varref_wrt_varref n1 (var_termvar_b n2).

Scheme degree_varref_wrt_varref_ind' := Induction for degree_varref_wrt_varref Sort Prop.

Definition degree_varref_wrt_varref_mutind :=
  fun H1 H2 H3 =>
  degree_varref_wrt_varref_ind' H1 H2 H3.

Hint Constructors degree_varref_wrt_varref : core lngen.

Inductive degree_typ_wrt_varref : nat -> typ -> Prop :=
  | degree_wrt_varref_typ_all : forall n1 T1 T2,
    degree_typ_wrt_varref n1 T1 ->
    degree_typ_wrt_varref (S n1) T2 ->
    degree_typ_wrt_varref n1 (typ_all T1 T2)
  | degree_wrt_varref_typ_bnd : forall n1 T1,
    degree_typ_wrt_varref (S n1) T1 ->
    degree_typ_wrt_varref n1 (typ_bnd T1)
  | degree_wrt_varref_typ_dec : forall n1 dec1,
    degree_dec_wrt_varref n1 dec1 ->
    degree_typ_wrt_varref n1 (typ_dec dec1)
  | degree_wrt_varref_typ_sel : forall n1 v1 A1,
    degree_varref_wrt_varref n1 v1 ->
    degree_typ_wrt_varref n1 (typ_sel v1 A1)
  | degree_wrt_varref_typ_and : forall n1 T1 T2,
    degree_typ_wrt_varref n1 T1 ->
    degree_typ_wrt_varref n1 T2 ->
    degree_typ_wrt_varref n1 (typ_and T1 T2)
  | degree_wrt_varref_typ_top : forall n1,
    degree_typ_wrt_varref n1 (typ_top)
  | degree_wrt_varref_typ_bot : forall n1,
    degree_typ_wrt_varref n1 (typ_bot)

with degree_dec_wrt_varref : nat -> dec -> Prop :=
  | degree_wrt_varref_dec_trm : forall n1 a1 T1,
    degree_typ_wrt_varref n1 T1 ->
    degree_dec_wrt_varref n1 (dec_trm a1 T1)
  | degree_wrt_varref_dec_typ : forall n1 A1 T1 T2,
    degree_typ_wrt_varref n1 T1 ->
    degree_typ_wrt_varref n1 T2 ->
    degree_dec_wrt_varref n1 (dec_typ A1 T1 T2).

Scheme degree_typ_wrt_varref_ind' := Induction for degree_typ_wrt_varref Sort Prop
  with degree_dec_wrt_varref_ind' := Induction for degree_dec_wrt_varref Sort Prop.

Definition degree_typ_wrt_varref_degree_dec_wrt_varref_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  (conj (degree_typ_wrt_varref_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)
  (degree_dec_wrt_varref_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)).

Hint Constructors degree_typ_wrt_varref : core lngen.

Hint Constructors degree_dec_wrt_varref : core lngen.

Inductive degree_def_wrt_varref : nat -> def -> Prop :=
  | degree_wrt_varref_def_trm : forall n1 a1 t1,
    degree_trm_wrt_varref n1 t1 ->
    degree_def_wrt_varref n1 (def_trm a1 t1)
  | degree_wrt_varref_def_typ : forall n1 A1 T1,
    degree_typ_wrt_varref n1 T1 ->
    degree_def_wrt_varref n1 (def_typ A1 T1)

with degree_defs_wrt_varref : nat -> defs -> Prop :=
  | degree_wrt_varref_defs_nil : forall n1,
    degree_defs_wrt_varref n1 (defs_nil)
  | degree_wrt_varref_defs_cons : forall n1 d1 defs1,
    degree_def_wrt_varref n1 d1 ->
    degree_defs_wrt_varref n1 defs1 ->
    degree_defs_wrt_varref n1 (defs_cons d1 defs1)

with degree_val_wrt_varref : nat -> val -> Prop :=
  | degree_wrt_varref_val_new : forall n1 T1 defs1,
    degree_typ_wrt_varref n1 T1 ->
    degree_defs_wrt_varref (S n1) defs1 ->
    degree_val_wrt_varref n1 (val_new T1 defs1)
  | degree_wrt_varref_val_lambda : forall n1 T1 t1,
    degree_typ_wrt_varref n1 T1 ->
    degree_trm_wrt_varref (S n1) t1 ->
    degree_val_wrt_varref n1 (val_lambda T1 t1)

with degree_trm_wrt_varref : nat -> trm -> Prop :=
  | degree_wrt_varref_trm_var : forall n1 v1,
    degree_varref_wrt_varref n1 v1 ->
    degree_trm_wrt_varref n1 (trm_var v1)
  | degree_wrt_varref_trm_val : forall n1 val1,
    degree_val_wrt_varref n1 val1 ->
    degree_trm_wrt_varref n1 (trm_val val1)
  | degree_wrt_varref_trm_sel : forall n1 v1 a1,
    degree_varref_wrt_varref n1 v1 ->
    degree_trm_wrt_varref n1 (trm_sel v1 a1)
  | degree_wrt_varref_trm_app : forall n1 v1 v2,
    degree_varref_wrt_varref n1 v1 ->
    degree_varref_wrt_varref n1 v2 ->
    degree_trm_wrt_varref n1 (trm_app v1 v2)
  | degree_wrt_varref_trm_let : forall n1 t1 t2,
    degree_trm_wrt_varref n1 t1 ->
    degree_trm_wrt_varref (S n1) t2 ->
    degree_trm_wrt_varref n1 (trm_let t1 t2).

Scheme degree_def_wrt_varref_ind' := Induction for degree_def_wrt_varref Sort Prop
  with degree_defs_wrt_varref_ind' := Induction for degree_defs_wrt_varref Sort Prop
  with degree_val_wrt_varref_ind' := Induction for degree_val_wrt_varref Sort Prop
  with degree_trm_wrt_varref_ind' := Induction for degree_trm_wrt_varref Sort Prop.

Definition degree_def_wrt_varref_degree_defs_wrt_varref_degree_val_wrt_varref_degree_trm_wrt_varref_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  (conj (degree_def_wrt_varref_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  ((conj (degree_defs_wrt_varref_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  ((conj (degree_val_wrt_varref_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  (degree_trm_wrt_varref_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)))))).

Hint Constructors degree_def_wrt_varref : core lngen.

Hint Constructors degree_defs_wrt_varref : core lngen.

Hint Constructors degree_val_wrt_varref : core lngen.

Hint Constructors degree_trm_wrt_varref : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_varref : varref -> Set :=
  | lc_set_var_termvar_f : forall x1,
    lc_set_varref (var_termvar_f x1).

Scheme lc_varref_ind' := Induction for lc_varref Sort Prop.

Definition lc_varref_mutind :=
  fun H1 H2 =>
  lc_varref_ind' H1 H2.

Scheme lc_set_varref_ind' := Induction for lc_set_varref Sort Prop.

Definition lc_set_varref_mutind :=
  fun H1 H2 =>
  lc_set_varref_ind' H1 H2.

Scheme lc_set_varref_rec' := Induction for lc_set_varref Sort Set.

Definition lc_set_varref_mutrec :=
  fun H1 H2 =>
  lc_set_varref_rec' H1 H2.

Hint Constructors lc_varref : core lngen.

Hint Constructors lc_set_varref : core lngen.

Inductive lc_set_typ : typ -> Set :=
  | lc_set_typ_all : forall T1 T2,
    lc_set_typ T1 ->
    (forall x1 : termvar, lc_set_typ (open_typ_wrt_varref T2 (var_termvar_f x1))) ->
    lc_set_typ (typ_all T1 T2)
  | lc_set_typ_bnd : forall T1,
    (forall x1 : termvar, lc_set_typ (open_typ_wrt_varref T1 (var_termvar_f x1))) ->
    lc_set_typ (typ_bnd T1)
  | lc_set_typ_dec : forall dec1,
    lc_set_dec dec1 ->
    lc_set_typ (typ_dec dec1)
  | lc_set_typ_sel : forall v1 A1,
    lc_set_varref v1 ->
    lc_set_typ (typ_sel v1 A1)
  | lc_set_typ_and : forall T1 T2,
    lc_set_typ T1 ->
    lc_set_typ T2 ->
    lc_set_typ (typ_and T1 T2)
  | lc_set_typ_top :
    lc_set_typ (typ_top)
  | lc_set_typ_bot :
    lc_set_typ (typ_bot)

with lc_set_dec : dec -> Set :=
  | lc_set_dec_trm : forall a1 T1,
    lc_set_typ T1 ->
    lc_set_dec (dec_trm a1 T1)
  | lc_set_dec_typ : forall A1 T1 T2,
    lc_set_typ T1 ->
    lc_set_typ T2 ->
    lc_set_dec (dec_typ A1 T1 T2).

Scheme lc_typ_ind' := Induction for lc_typ Sort Prop
  with lc_dec_ind' := Induction for lc_dec Sort Prop.

Definition lc_typ_lc_dec_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  (conj (lc_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)
  (lc_dec_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)).

Scheme lc_set_typ_ind' := Induction for lc_set_typ Sort Prop
  with lc_set_dec_ind' := Induction for lc_set_dec Sort Prop.

Definition lc_set_typ_lc_set_dec_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  (conj (lc_set_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)
  (lc_set_dec_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)).

Scheme lc_set_typ_rec' := Induction for lc_set_typ Sort Set
  with lc_set_dec_rec' := Induction for lc_set_dec Sort Set.

Definition lc_set_typ_lc_set_dec_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  (pair (lc_set_typ_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)
  (lc_set_dec_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)).

Hint Constructors lc_typ : core lngen.

Hint Constructors lc_dec : core lngen.

Hint Constructors lc_set_typ : core lngen.

Hint Constructors lc_set_dec : core lngen.

Inductive lc_set_def : def -> Set :=
  | lc_set_def_trm : forall a1 t1,
    lc_set_trm t1 ->
    lc_set_def (def_trm a1 t1)
  | lc_set_def_typ : forall A1 T1,
    lc_set_typ T1 ->
    lc_set_def (def_typ A1 T1)

with lc_set_defs : defs -> Set :=
  | lc_set_defs_nil :
    lc_set_defs (defs_nil)
  | lc_set_defs_cons : forall d1 defs1,
    lc_set_def d1 ->
    lc_set_defs defs1 ->
    lc_set_defs (defs_cons d1 defs1)

with lc_set_val : val -> Set :=
  | lc_set_val_new : forall T1 defs1,
    lc_set_typ T1 ->
    (forall x1 : termvar, lc_set_defs (open_defs_wrt_varref defs1 (var_termvar_f x1))) ->
    lc_set_val (val_new T1 defs1)
  | lc_set_val_lambda : forall T1 t1,
    lc_set_typ T1 ->
    (forall x1 : termvar, lc_set_trm (open_trm_wrt_varref t1 (var_termvar_f x1))) ->
    lc_set_val (val_lambda T1 t1)

with lc_set_trm : trm -> Set :=
  | lc_set_trm_var : forall v1,
    lc_set_varref v1 ->
    lc_set_trm (trm_var v1)
  | lc_set_trm_val : forall val1,
    lc_set_val val1 ->
    lc_set_trm (trm_val val1)
  | lc_set_trm_sel : forall v1 a1,
    lc_set_varref v1 ->
    lc_set_trm (trm_sel v1 a1)
  | lc_set_trm_app : forall v1 v2,
    lc_set_varref v1 ->
    lc_set_varref v2 ->
    lc_set_trm (trm_app v1 v2)
  | lc_set_trm_let : forall t1 t2,
    lc_set_trm t1 ->
    (forall x1 : termvar, lc_set_trm (open_trm_wrt_varref t2 (var_termvar_f x1))) ->
    lc_set_trm (trm_let t1 t2).

Scheme lc_def_ind' := Induction for lc_def Sort Prop
  with lc_defs_ind' := Induction for lc_defs Sort Prop
  with lc_val_ind' := Induction for lc_val Sort Prop
  with lc_trm_ind' := Induction for lc_trm Sort Prop.

Definition lc_def_lc_defs_lc_val_lc_trm_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  (conj (lc_def_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  ((conj (lc_defs_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  ((conj (lc_val_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  (lc_trm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)))))).

Scheme lc_set_def_ind' := Induction for lc_set_def Sort Prop
  with lc_set_defs_ind' := Induction for lc_set_defs Sort Prop
  with lc_set_val_ind' := Induction for lc_set_val Sort Prop
  with lc_set_trm_ind' := Induction for lc_set_trm Sort Prop.

Definition lc_set_def_lc_set_defs_lc_set_val_lc_set_trm_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  (conj (lc_set_def_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  ((conj (lc_set_defs_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  ((conj (lc_set_val_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  (lc_set_trm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)))))).

Scheme lc_set_def_rec' := Induction for lc_set_def Sort Set
  with lc_set_defs_rec' := Induction for lc_set_defs Sort Set
  with lc_set_val_rec' := Induction for lc_set_val Sort Set
  with lc_set_trm_rec' := Induction for lc_set_trm Sort Set.

Definition lc_set_def_lc_set_defs_lc_set_val_lc_set_trm_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  (pair ((pair ((pair (lc_set_def_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)
  (lc_set_defs_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)))
  (lc_set_val_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)))
  (lc_set_trm_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)).

Hint Constructors lc_def : core lngen.

Hint Constructors lc_defs : core lngen.

Hint Constructors lc_val : core lngen.

Hint Constructors lc_trm : core lngen.

Hint Constructors lc_set_def : core lngen.

Hint Constructors lc_set_defs : core lngen.

Hint Constructors lc_set_val : core lngen.

Hint Constructors lc_set_trm : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_varref_wrt_varref v1 := forall x1, lc_varref (open_varref_wrt_varref v1 (var_termvar_f x1)).

Hint Unfold body_varref_wrt_varref.

Definition body_typ_wrt_varref T1 := forall x1, lc_typ (open_typ_wrt_varref T1 (var_termvar_f x1)).

Definition body_dec_wrt_varref dec1 := forall x1, lc_dec (open_dec_wrt_varref dec1 (var_termvar_f x1)).

Hint Unfold body_typ_wrt_varref.

Hint Unfold body_dec_wrt_varref.

Definition body_def_wrt_varref d1 := forall x1, lc_def (open_def_wrt_varref d1 (var_termvar_f x1)).

Definition body_defs_wrt_varref defs1 := forall x1, lc_defs (open_defs_wrt_varref defs1 (var_termvar_f x1)).

Definition body_val_wrt_varref val1 := forall x1, lc_val (open_val_wrt_varref val1 (var_termvar_f x1)).

Definition body_trm_wrt_varref t1 := forall x1, lc_trm (open_trm_wrt_varref t1 (var_termvar_f x1)).

Hint Unfold body_def_wrt_varref.

Hint Unfold body_defs_wrt_varref.

Hint Unfold body_val_wrt_varref.

Hint Unfold body_trm_wrt_varref.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_varref_min_mutual :
(forall v1, 1 <= size_varref v1).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_varref_min :
forall v1, 1 <= size_varref v1.
Proof.
pose proof size_varref_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_varref_min : lngen.

(* begin hide *)

Lemma size_typ_min_size_dec_min_mutual :
(forall T1, 1 <= size_typ T1) /\
(forall dec1, 1 <= size_dec dec1).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_typ_min :
forall T1, 1 <= size_typ T1.
Proof.
pose proof size_typ_min_size_dec_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_min : lngen.

Lemma size_dec_min :
forall dec1, 1 <= size_dec dec1.
Proof.
pose proof size_typ_min_size_dec_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dec_min : lngen.

(* begin hide *)

Lemma size_def_min_size_defs_min_size_val_min_size_trm_min_mutual :
(forall d1, 1 <= size_def d1) /\
(forall defs1, 1 <= size_defs defs1) /\
(forall val1, 1 <= size_val val1) /\
(forall t1, 1 <= size_trm t1).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_def_min :
forall d1, 1 <= size_def d1.
Proof.
pose proof size_def_min_size_defs_min_size_val_min_size_trm_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_def_min : lngen.

Lemma size_defs_min :
forall defs1, 1 <= size_defs defs1.
Proof.
pose proof size_def_min_size_defs_min_size_val_min_size_trm_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_defs_min : lngen.

Lemma size_val_min :
forall val1, 1 <= size_val val1.
Proof.
pose proof size_def_min_size_defs_min_size_val_min_size_trm_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_val_min : lngen.

Lemma size_trm_min :
forall t1, 1 <= size_trm t1.
Proof.
pose proof size_def_min_size_defs_min_size_val_min_size_trm_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_trm_min : lngen.

(* begin hide *)

Lemma size_varref_close_varref_wrt_varref_rec_mutual :
(forall v1 x1 n1,
  size_varref (close_varref_wrt_varref_rec n1 x1 v1) = size_varref v1).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_varref_close_varref_wrt_varref_rec :
forall v1 x1 n1,
  size_varref (close_varref_wrt_varref_rec n1 x1 v1) = size_varref v1.
Proof.
pose proof size_varref_close_varref_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_varref_close_varref_wrt_varref_rec : lngen.
Hint Rewrite size_varref_close_varref_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_typ_close_typ_wrt_varref_rec_size_dec_close_dec_wrt_varref_rec_mutual :
(forall T1 x1 n1,
  size_typ (close_typ_wrt_varref_rec n1 x1 T1) = size_typ T1) /\
(forall dec1 x1 n1,
  size_dec (close_dec_wrt_varref_rec n1 x1 dec1) = size_dec dec1).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_close_typ_wrt_varref_rec :
forall T1 x1 n1,
  size_typ (close_typ_wrt_varref_rec n1 x1 T1) = size_typ T1.
Proof.
pose proof size_typ_close_typ_wrt_varref_rec_size_dec_close_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_close_typ_wrt_varref_rec : lngen.
Hint Rewrite size_typ_close_typ_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dec_close_dec_wrt_varref_rec :
forall dec1 x1 n1,
  size_dec (close_dec_wrt_varref_rec n1 x1 dec1) = size_dec dec1.
Proof.
pose proof size_typ_close_typ_wrt_varref_rec_size_dec_close_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dec_close_dec_wrt_varref_rec : lngen.
Hint Rewrite size_dec_close_dec_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_def_close_def_wrt_varref_rec_size_defs_close_defs_wrt_varref_rec_size_val_close_val_wrt_varref_rec_size_trm_close_trm_wrt_varref_rec_mutual :
(forall d1 x1 n1,
  size_def (close_def_wrt_varref_rec n1 x1 d1) = size_def d1) /\
(forall defs1 x1 n1,
  size_defs (close_defs_wrt_varref_rec n1 x1 defs1) = size_defs defs1) /\
(forall val1 x1 n1,
  size_val (close_val_wrt_varref_rec n1 x1 val1) = size_val val1) /\
(forall t1 x1 n1,
  size_trm (close_trm_wrt_varref_rec n1 x1 t1) = size_trm t1).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_def_close_def_wrt_varref_rec :
forall d1 x1 n1,
  size_def (close_def_wrt_varref_rec n1 x1 d1) = size_def d1.
Proof.
pose proof size_def_close_def_wrt_varref_rec_size_defs_close_defs_wrt_varref_rec_size_val_close_val_wrt_varref_rec_size_trm_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_def_close_def_wrt_varref_rec : lngen.
Hint Rewrite size_def_close_def_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_defs_close_defs_wrt_varref_rec :
forall defs1 x1 n1,
  size_defs (close_defs_wrt_varref_rec n1 x1 defs1) = size_defs defs1.
Proof.
pose proof size_def_close_def_wrt_varref_rec_size_defs_close_defs_wrt_varref_rec_size_val_close_val_wrt_varref_rec_size_trm_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_defs_close_defs_wrt_varref_rec : lngen.
Hint Rewrite size_defs_close_defs_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_val_close_val_wrt_varref_rec :
forall val1 x1 n1,
  size_val (close_val_wrt_varref_rec n1 x1 val1) = size_val val1.
Proof.
pose proof size_def_close_def_wrt_varref_rec_size_defs_close_defs_wrt_varref_rec_size_val_close_val_wrt_varref_rec_size_trm_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_val_close_val_wrt_varref_rec : lngen.
Hint Rewrite size_val_close_val_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_trm_close_trm_wrt_varref_rec :
forall t1 x1 n1,
  size_trm (close_trm_wrt_varref_rec n1 x1 t1) = size_trm t1.
Proof.
pose proof size_def_close_def_wrt_varref_rec_size_defs_close_defs_wrt_varref_rec_size_val_close_val_wrt_varref_rec_size_trm_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_trm_close_trm_wrt_varref_rec : lngen.
Hint Rewrite size_trm_close_trm_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_varref_close_varref_wrt_varref :
forall v1 x1,
  size_varref (close_varref_wrt_varref x1 v1) = size_varref v1.
Proof.
unfold close_varref_wrt_varref; default_simp.
Qed.

Hint Resolve size_varref_close_varref_wrt_varref : lngen.
Hint Rewrite size_varref_close_varref_wrt_varref using solve [auto] : lngen.

Lemma size_typ_close_typ_wrt_varref :
forall T1 x1,
  size_typ (close_typ_wrt_varref x1 T1) = size_typ T1.
Proof.
unfold close_typ_wrt_varref; default_simp.
Qed.

Hint Resolve size_typ_close_typ_wrt_varref : lngen.
Hint Rewrite size_typ_close_typ_wrt_varref using solve [auto] : lngen.

Lemma size_dec_close_dec_wrt_varref :
forall dec1 x1,
  size_dec (close_dec_wrt_varref x1 dec1) = size_dec dec1.
Proof.
unfold close_dec_wrt_varref; default_simp.
Qed.

Hint Resolve size_dec_close_dec_wrt_varref : lngen.
Hint Rewrite size_dec_close_dec_wrt_varref using solve [auto] : lngen.

Lemma size_def_close_def_wrt_varref :
forall d1 x1,
  size_def (close_def_wrt_varref x1 d1) = size_def d1.
Proof.
unfold close_def_wrt_varref; default_simp.
Qed.

Hint Resolve size_def_close_def_wrt_varref : lngen.
Hint Rewrite size_def_close_def_wrt_varref using solve [auto] : lngen.

Lemma size_defs_close_defs_wrt_varref :
forall defs1 x1,
  size_defs (close_defs_wrt_varref x1 defs1) = size_defs defs1.
Proof.
unfold close_defs_wrt_varref; default_simp.
Qed.

Hint Resolve size_defs_close_defs_wrt_varref : lngen.
Hint Rewrite size_defs_close_defs_wrt_varref using solve [auto] : lngen.

Lemma size_val_close_val_wrt_varref :
forall val1 x1,
  size_val (close_val_wrt_varref x1 val1) = size_val val1.
Proof.
unfold close_val_wrt_varref; default_simp.
Qed.

Hint Resolve size_val_close_val_wrt_varref : lngen.
Hint Rewrite size_val_close_val_wrt_varref using solve [auto] : lngen.

Lemma size_trm_close_trm_wrt_varref :
forall t1 x1,
  size_trm (close_trm_wrt_varref x1 t1) = size_trm t1.
Proof.
unfold close_trm_wrt_varref; default_simp.
Qed.

Hint Resolve size_trm_close_trm_wrt_varref : lngen.
Hint Rewrite size_trm_close_trm_wrt_varref using solve [auto] : lngen.

(* begin hide *)

Lemma size_varref_open_varref_wrt_varref_rec_mutual :
(forall v1 v2 n1,
  size_varref v1 <= size_varref (open_varref_wrt_varref_rec n1 v2 v1)).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_varref_open_varref_wrt_varref_rec :
forall v1 v2 n1,
  size_varref v1 <= size_varref (open_varref_wrt_varref_rec n1 v2 v1).
Proof.
pose proof size_varref_open_varref_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_varref_open_varref_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_varref_rec_size_dec_open_dec_wrt_varref_rec_mutual :
(forall T1 v1 n1,
  size_typ T1 <= size_typ (open_typ_wrt_varref_rec n1 v1 T1)) /\
(forall dec1 v1 n1,
  size_dec dec1 <= size_dec (open_dec_wrt_varref_rec n1 v1 dec1)).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_varref_rec :
forall T1 v1 n1,
  size_typ T1 <= size_typ (open_typ_wrt_varref_rec n1 v1 T1).
Proof.
pose proof size_typ_open_typ_wrt_varref_rec_size_dec_open_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_open_typ_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dec_open_dec_wrt_varref_rec :
forall dec1 v1 n1,
  size_dec dec1 <= size_dec (open_dec_wrt_varref_rec n1 v1 dec1).
Proof.
pose proof size_typ_open_typ_wrt_varref_rec_size_dec_open_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dec_open_dec_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_def_open_def_wrt_varref_rec_size_defs_open_defs_wrt_varref_rec_size_val_open_val_wrt_varref_rec_size_trm_open_trm_wrt_varref_rec_mutual :
(forall d1 v1 n1,
  size_def d1 <= size_def (open_def_wrt_varref_rec n1 v1 d1)) /\
(forall defs1 v1 n1,
  size_defs defs1 <= size_defs (open_defs_wrt_varref_rec n1 v1 defs1)) /\
(forall val1 v1 n1,
  size_val val1 <= size_val (open_val_wrt_varref_rec n1 v1 val1)) /\
(forall t1 v1 n1,
  size_trm t1 <= size_trm (open_trm_wrt_varref_rec n1 v1 t1)).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_def_open_def_wrt_varref_rec :
forall d1 v1 n1,
  size_def d1 <= size_def (open_def_wrt_varref_rec n1 v1 d1).
Proof.
pose proof size_def_open_def_wrt_varref_rec_size_defs_open_defs_wrt_varref_rec_size_val_open_val_wrt_varref_rec_size_trm_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_def_open_def_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_defs_open_defs_wrt_varref_rec :
forall defs1 v1 n1,
  size_defs defs1 <= size_defs (open_defs_wrt_varref_rec n1 v1 defs1).
Proof.
pose proof size_def_open_def_wrt_varref_rec_size_defs_open_defs_wrt_varref_rec_size_val_open_val_wrt_varref_rec_size_trm_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_defs_open_defs_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_val_open_val_wrt_varref_rec :
forall val1 v1 n1,
  size_val val1 <= size_val (open_val_wrt_varref_rec n1 v1 val1).
Proof.
pose proof size_def_open_def_wrt_varref_rec_size_defs_open_defs_wrt_varref_rec_size_val_open_val_wrt_varref_rec_size_trm_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_val_open_val_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_trm_open_trm_wrt_varref_rec :
forall t1 v1 n1,
  size_trm t1 <= size_trm (open_trm_wrt_varref_rec n1 v1 t1).
Proof.
pose proof size_def_open_def_wrt_varref_rec_size_defs_open_defs_wrt_varref_rec_size_val_open_val_wrt_varref_rec_size_trm_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_trm_open_trm_wrt_varref_rec : lngen.

(* end hide *)

Lemma size_varref_open_varref_wrt_varref :
forall v1 v2,
  size_varref v1 <= size_varref (open_varref_wrt_varref v1 v2).
Proof.
unfold open_varref_wrt_varref; default_simp.
Qed.

Hint Resolve size_varref_open_varref_wrt_varref : lngen.

Lemma size_typ_open_typ_wrt_varref :
forall T1 v1,
  size_typ T1 <= size_typ (open_typ_wrt_varref T1 v1).
Proof.
unfold open_typ_wrt_varref; default_simp.
Qed.

Hint Resolve size_typ_open_typ_wrt_varref : lngen.

Lemma size_dec_open_dec_wrt_varref :
forall dec1 v1,
  size_dec dec1 <= size_dec (open_dec_wrt_varref dec1 v1).
Proof.
unfold open_dec_wrt_varref; default_simp.
Qed.

Hint Resolve size_dec_open_dec_wrt_varref : lngen.

Lemma size_def_open_def_wrt_varref :
forall d1 v1,
  size_def d1 <= size_def (open_def_wrt_varref d1 v1).
Proof.
unfold open_def_wrt_varref; default_simp.
Qed.

Hint Resolve size_def_open_def_wrt_varref : lngen.

Lemma size_defs_open_defs_wrt_varref :
forall defs1 v1,
  size_defs defs1 <= size_defs (open_defs_wrt_varref defs1 v1).
Proof.
unfold open_defs_wrt_varref; default_simp.
Qed.

Hint Resolve size_defs_open_defs_wrt_varref : lngen.

Lemma size_val_open_val_wrt_varref :
forall val1 v1,
  size_val val1 <= size_val (open_val_wrt_varref val1 v1).
Proof.
unfold open_val_wrt_varref; default_simp.
Qed.

Hint Resolve size_val_open_val_wrt_varref : lngen.

Lemma size_trm_open_trm_wrt_varref :
forall t1 v1,
  size_trm t1 <= size_trm (open_trm_wrt_varref t1 v1).
Proof.
unfold open_trm_wrt_varref; default_simp.
Qed.

Hint Resolve size_trm_open_trm_wrt_varref : lngen.

(* begin hide *)

Lemma size_varref_open_varref_wrt_varref_rec_var_mutual :
(forall v1 x1 n1,
  size_varref (open_varref_wrt_varref_rec n1 (var_termvar_f x1) v1) = size_varref v1).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_varref_open_varref_wrt_varref_rec_var :
forall v1 x1 n1,
  size_varref (open_varref_wrt_varref_rec n1 (var_termvar_f x1) v1) = size_varref v1.
Proof.
pose proof size_varref_open_varref_wrt_varref_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_varref_open_varref_wrt_varref_rec_var : lngen.
Hint Rewrite size_varref_open_varref_wrt_varref_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_varref_rec_var_size_dec_open_dec_wrt_varref_rec_var_mutual :
(forall T1 x1 n1,
  size_typ (open_typ_wrt_varref_rec n1 (var_termvar_f x1) T1) = size_typ T1) /\
(forall dec1 x1 n1,
  size_dec (open_dec_wrt_varref_rec n1 (var_termvar_f x1) dec1) = size_dec dec1).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_varref_rec_var :
forall T1 x1 n1,
  size_typ (open_typ_wrt_varref_rec n1 (var_termvar_f x1) T1) = size_typ T1.
Proof.
pose proof size_typ_open_typ_wrt_varref_rec_var_size_dec_open_dec_wrt_varref_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_open_typ_wrt_varref_rec_var : lngen.
Hint Rewrite size_typ_open_typ_wrt_varref_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dec_open_dec_wrt_varref_rec_var :
forall dec1 x1 n1,
  size_dec (open_dec_wrt_varref_rec n1 (var_termvar_f x1) dec1) = size_dec dec1.
Proof.
pose proof size_typ_open_typ_wrt_varref_rec_var_size_dec_open_dec_wrt_varref_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dec_open_dec_wrt_varref_rec_var : lngen.
Hint Rewrite size_dec_open_dec_wrt_varref_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_def_open_def_wrt_varref_rec_var_size_defs_open_defs_wrt_varref_rec_var_size_val_open_val_wrt_varref_rec_var_size_trm_open_trm_wrt_varref_rec_var_mutual :
(forall d1 x1 n1,
  size_def (open_def_wrt_varref_rec n1 (var_termvar_f x1) d1) = size_def d1) /\
(forall defs1 x1 n1,
  size_defs (open_defs_wrt_varref_rec n1 (var_termvar_f x1) defs1) = size_defs defs1) /\
(forall val1 x1 n1,
  size_val (open_val_wrt_varref_rec n1 (var_termvar_f x1) val1) = size_val val1) /\
(forall t1 x1 n1,
  size_trm (open_trm_wrt_varref_rec n1 (var_termvar_f x1) t1) = size_trm t1).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_def_open_def_wrt_varref_rec_var :
forall d1 x1 n1,
  size_def (open_def_wrt_varref_rec n1 (var_termvar_f x1) d1) = size_def d1.
Proof.
pose proof size_def_open_def_wrt_varref_rec_var_size_defs_open_defs_wrt_varref_rec_var_size_val_open_val_wrt_varref_rec_var_size_trm_open_trm_wrt_varref_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_def_open_def_wrt_varref_rec_var : lngen.
Hint Rewrite size_def_open_def_wrt_varref_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_defs_open_defs_wrt_varref_rec_var :
forall defs1 x1 n1,
  size_defs (open_defs_wrt_varref_rec n1 (var_termvar_f x1) defs1) = size_defs defs1.
Proof.
pose proof size_def_open_def_wrt_varref_rec_var_size_defs_open_defs_wrt_varref_rec_var_size_val_open_val_wrt_varref_rec_var_size_trm_open_trm_wrt_varref_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_defs_open_defs_wrt_varref_rec_var : lngen.
Hint Rewrite size_defs_open_defs_wrt_varref_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_val_open_val_wrt_varref_rec_var :
forall val1 x1 n1,
  size_val (open_val_wrt_varref_rec n1 (var_termvar_f x1) val1) = size_val val1.
Proof.
pose proof size_def_open_def_wrt_varref_rec_var_size_defs_open_defs_wrt_varref_rec_var_size_val_open_val_wrt_varref_rec_var_size_trm_open_trm_wrt_varref_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_val_open_val_wrt_varref_rec_var : lngen.
Hint Rewrite size_val_open_val_wrt_varref_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_trm_open_trm_wrt_varref_rec_var :
forall t1 x1 n1,
  size_trm (open_trm_wrt_varref_rec n1 (var_termvar_f x1) t1) = size_trm t1.
Proof.
pose proof size_def_open_def_wrt_varref_rec_var_size_defs_open_defs_wrt_varref_rec_var_size_val_open_val_wrt_varref_rec_var_size_trm_open_trm_wrt_varref_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_trm_open_trm_wrt_varref_rec_var : lngen.
Hint Rewrite size_trm_open_trm_wrt_varref_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_varref_open_varref_wrt_varref_var :
forall v1 x1,
  size_varref (open_varref_wrt_varref v1 (var_termvar_f x1)) = size_varref v1.
Proof.
unfold open_varref_wrt_varref; default_simp.
Qed.

Hint Resolve size_varref_open_varref_wrt_varref_var : lngen.
Hint Rewrite size_varref_open_varref_wrt_varref_var using solve [auto] : lngen.

Lemma size_typ_open_typ_wrt_varref_var :
forall T1 x1,
  size_typ (open_typ_wrt_varref T1 (var_termvar_f x1)) = size_typ T1.
Proof.
unfold open_typ_wrt_varref; default_simp.
Qed.

Hint Resolve size_typ_open_typ_wrt_varref_var : lngen.
Hint Rewrite size_typ_open_typ_wrt_varref_var using solve [auto] : lngen.

Lemma size_dec_open_dec_wrt_varref_var :
forall dec1 x1,
  size_dec (open_dec_wrt_varref dec1 (var_termvar_f x1)) = size_dec dec1.
Proof.
unfold open_dec_wrt_varref; default_simp.
Qed.

Hint Resolve size_dec_open_dec_wrt_varref_var : lngen.
Hint Rewrite size_dec_open_dec_wrt_varref_var using solve [auto] : lngen.

Lemma size_def_open_def_wrt_varref_var :
forall d1 x1,
  size_def (open_def_wrt_varref d1 (var_termvar_f x1)) = size_def d1.
Proof.
unfold open_def_wrt_varref; default_simp.
Qed.

Hint Resolve size_def_open_def_wrt_varref_var : lngen.
Hint Rewrite size_def_open_def_wrt_varref_var using solve [auto] : lngen.

Lemma size_defs_open_defs_wrt_varref_var :
forall defs1 x1,
  size_defs (open_defs_wrt_varref defs1 (var_termvar_f x1)) = size_defs defs1.
Proof.
unfold open_defs_wrt_varref; default_simp.
Qed.

Hint Resolve size_defs_open_defs_wrt_varref_var : lngen.
Hint Rewrite size_defs_open_defs_wrt_varref_var using solve [auto] : lngen.

Lemma size_val_open_val_wrt_varref_var :
forall val1 x1,
  size_val (open_val_wrt_varref val1 (var_termvar_f x1)) = size_val val1.
Proof.
unfold open_val_wrt_varref; default_simp.
Qed.

Hint Resolve size_val_open_val_wrt_varref_var : lngen.
Hint Rewrite size_val_open_val_wrt_varref_var using solve [auto] : lngen.

Lemma size_trm_open_trm_wrt_varref_var :
forall t1 x1,
  size_trm (open_trm_wrt_varref t1 (var_termvar_f x1)) = size_trm t1.
Proof.
unfold open_trm_wrt_varref; default_simp.
Qed.

Hint Resolve size_trm_open_trm_wrt_varref_var : lngen.
Hint Rewrite size_trm_open_trm_wrt_varref_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_varref_wrt_varref_S_mutual :
(forall n1 v1,
  degree_varref_wrt_varref n1 v1 ->
  degree_varref_wrt_varref (S n1) v1).
Proof.
apply_mutual_ind degree_varref_wrt_varref_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_varref_wrt_varref_S :
forall n1 v1,
  degree_varref_wrt_varref n1 v1 ->
  degree_varref_wrt_varref (S n1) v1.
Proof.
pose proof degree_varref_wrt_varref_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_varref_wrt_varref_S : lngen.

(* begin hide *)

Lemma degree_typ_wrt_varref_S_degree_dec_wrt_varref_S_mutual :
(forall n1 T1,
  degree_typ_wrt_varref n1 T1 ->
  degree_typ_wrt_varref (S n1) T1) /\
(forall n1 dec1,
  degree_dec_wrt_varref n1 dec1 ->
  degree_dec_wrt_varref (S n1) dec1).
Proof.
apply_mutual_ind degree_typ_wrt_varref_degree_dec_wrt_varref_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_typ_wrt_varref_S :
forall n1 T1,
  degree_typ_wrt_varref n1 T1 ->
  degree_typ_wrt_varref (S n1) T1.
Proof.
pose proof degree_typ_wrt_varref_S_degree_dec_wrt_varref_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_varref_S : lngen.

Lemma degree_dec_wrt_varref_S :
forall n1 dec1,
  degree_dec_wrt_varref n1 dec1 ->
  degree_dec_wrt_varref (S n1) dec1.
Proof.
pose proof degree_typ_wrt_varref_S_degree_dec_wrt_varref_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dec_wrt_varref_S : lngen.

(* begin hide *)

Lemma degree_def_wrt_varref_S_degree_defs_wrt_varref_S_degree_val_wrt_varref_S_degree_trm_wrt_varref_S_mutual :
(forall n1 d1,
  degree_def_wrt_varref n1 d1 ->
  degree_def_wrt_varref (S n1) d1) /\
(forall n1 defs1,
  degree_defs_wrt_varref n1 defs1 ->
  degree_defs_wrt_varref (S n1) defs1) /\
(forall n1 val1,
  degree_val_wrt_varref n1 val1 ->
  degree_val_wrt_varref (S n1) val1) /\
(forall n1 t1,
  degree_trm_wrt_varref n1 t1 ->
  degree_trm_wrt_varref (S n1) t1).
Proof.
apply_mutual_ind degree_def_wrt_varref_degree_defs_wrt_varref_degree_val_wrt_varref_degree_trm_wrt_varref_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_def_wrt_varref_S :
forall n1 d1,
  degree_def_wrt_varref n1 d1 ->
  degree_def_wrt_varref (S n1) d1.
Proof.
pose proof degree_def_wrt_varref_S_degree_defs_wrt_varref_S_degree_val_wrt_varref_S_degree_trm_wrt_varref_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_def_wrt_varref_S : lngen.

Lemma degree_defs_wrt_varref_S :
forall n1 defs1,
  degree_defs_wrt_varref n1 defs1 ->
  degree_defs_wrt_varref (S n1) defs1.
Proof.
pose proof degree_def_wrt_varref_S_degree_defs_wrt_varref_S_degree_val_wrt_varref_S_degree_trm_wrt_varref_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_defs_wrt_varref_S : lngen.

Lemma degree_val_wrt_varref_S :
forall n1 val1,
  degree_val_wrt_varref n1 val1 ->
  degree_val_wrt_varref (S n1) val1.
Proof.
pose proof degree_def_wrt_varref_S_degree_defs_wrt_varref_S_degree_val_wrt_varref_S_degree_trm_wrt_varref_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_val_wrt_varref_S : lngen.

Lemma degree_trm_wrt_varref_S :
forall n1 t1,
  degree_trm_wrt_varref n1 t1 ->
  degree_trm_wrt_varref (S n1) t1.
Proof.
pose proof degree_def_wrt_varref_S_degree_defs_wrt_varref_S_degree_val_wrt_varref_S_degree_trm_wrt_varref_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_trm_wrt_varref_S : lngen.

Lemma degree_varref_wrt_varref_O :
forall n1 v1,
  degree_varref_wrt_varref O v1 ->
  degree_varref_wrt_varref n1 v1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_varref_wrt_varref_O : lngen.

Lemma degree_typ_wrt_varref_O :
forall n1 T1,
  degree_typ_wrt_varref O T1 ->
  degree_typ_wrt_varref n1 T1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_typ_wrt_varref_O : lngen.

Lemma degree_dec_wrt_varref_O :
forall n1 dec1,
  degree_dec_wrt_varref O dec1 ->
  degree_dec_wrt_varref n1 dec1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_dec_wrt_varref_O : lngen.

Lemma degree_def_wrt_varref_O :
forall n1 d1,
  degree_def_wrt_varref O d1 ->
  degree_def_wrt_varref n1 d1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_def_wrt_varref_O : lngen.

Lemma degree_defs_wrt_varref_O :
forall n1 defs1,
  degree_defs_wrt_varref O defs1 ->
  degree_defs_wrt_varref n1 defs1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_defs_wrt_varref_O : lngen.

Lemma degree_val_wrt_varref_O :
forall n1 val1,
  degree_val_wrt_varref O val1 ->
  degree_val_wrt_varref n1 val1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_val_wrt_varref_O : lngen.

Lemma degree_trm_wrt_varref_O :
forall n1 t1,
  degree_trm_wrt_varref O t1 ->
  degree_trm_wrt_varref n1 t1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_trm_wrt_varref_O : lngen.

(* begin hide *)

Lemma degree_varref_wrt_varref_close_varref_wrt_varref_rec_mutual :
(forall v1 x1 n1,
  degree_varref_wrt_varref n1 v1 ->
  degree_varref_wrt_varref (S n1) (close_varref_wrt_varref_rec n1 x1 v1)).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_varref_wrt_varref_close_varref_wrt_varref_rec :
forall v1 x1 n1,
  degree_varref_wrt_varref n1 v1 ->
  degree_varref_wrt_varref (S n1) (close_varref_wrt_varref_rec n1 x1 v1).
Proof.
pose proof degree_varref_wrt_varref_close_varref_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_varref_wrt_varref_close_varref_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_varref_close_typ_wrt_varref_rec_degree_dec_wrt_varref_close_dec_wrt_varref_rec_mutual :
(forall T1 x1 n1,
  degree_typ_wrt_varref n1 T1 ->
  degree_typ_wrt_varref (S n1) (close_typ_wrt_varref_rec n1 x1 T1)) /\
(forall dec1 x1 n1,
  degree_dec_wrt_varref n1 dec1 ->
  degree_dec_wrt_varref (S n1) (close_dec_wrt_varref_rec n1 x1 dec1)).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_varref_close_typ_wrt_varref_rec :
forall T1 x1 n1,
  degree_typ_wrt_varref n1 T1 ->
  degree_typ_wrt_varref (S n1) (close_typ_wrt_varref_rec n1 x1 T1).
Proof.
pose proof degree_typ_wrt_varref_close_typ_wrt_varref_rec_degree_dec_wrt_varref_close_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_varref_close_typ_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dec_wrt_varref_close_dec_wrt_varref_rec :
forall dec1 x1 n1,
  degree_dec_wrt_varref n1 dec1 ->
  degree_dec_wrt_varref (S n1) (close_dec_wrt_varref_rec n1 x1 dec1).
Proof.
pose proof degree_typ_wrt_varref_close_typ_wrt_varref_rec_degree_dec_wrt_varref_close_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dec_wrt_varref_close_dec_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_def_wrt_varref_close_def_wrt_varref_rec_degree_defs_wrt_varref_close_defs_wrt_varref_rec_degree_val_wrt_varref_close_val_wrt_varref_rec_degree_trm_wrt_varref_close_trm_wrt_varref_rec_mutual :
(forall d1 x1 n1,
  degree_def_wrt_varref n1 d1 ->
  degree_def_wrt_varref (S n1) (close_def_wrt_varref_rec n1 x1 d1)) /\
(forall defs1 x1 n1,
  degree_defs_wrt_varref n1 defs1 ->
  degree_defs_wrt_varref (S n1) (close_defs_wrt_varref_rec n1 x1 defs1)) /\
(forall val1 x1 n1,
  degree_val_wrt_varref n1 val1 ->
  degree_val_wrt_varref (S n1) (close_val_wrt_varref_rec n1 x1 val1)) /\
(forall t1 x1 n1,
  degree_trm_wrt_varref n1 t1 ->
  degree_trm_wrt_varref (S n1) (close_trm_wrt_varref_rec n1 x1 t1)).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_def_wrt_varref_close_def_wrt_varref_rec :
forall d1 x1 n1,
  degree_def_wrt_varref n1 d1 ->
  degree_def_wrt_varref (S n1) (close_def_wrt_varref_rec n1 x1 d1).
Proof.
pose proof degree_def_wrt_varref_close_def_wrt_varref_rec_degree_defs_wrt_varref_close_defs_wrt_varref_rec_degree_val_wrt_varref_close_val_wrt_varref_rec_degree_trm_wrt_varref_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_def_wrt_varref_close_def_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_defs_wrt_varref_close_defs_wrt_varref_rec :
forall defs1 x1 n1,
  degree_defs_wrt_varref n1 defs1 ->
  degree_defs_wrt_varref (S n1) (close_defs_wrt_varref_rec n1 x1 defs1).
Proof.
pose proof degree_def_wrt_varref_close_def_wrt_varref_rec_degree_defs_wrt_varref_close_defs_wrt_varref_rec_degree_val_wrt_varref_close_val_wrt_varref_rec_degree_trm_wrt_varref_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_defs_wrt_varref_close_defs_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_val_wrt_varref_close_val_wrt_varref_rec :
forall val1 x1 n1,
  degree_val_wrt_varref n1 val1 ->
  degree_val_wrt_varref (S n1) (close_val_wrt_varref_rec n1 x1 val1).
Proof.
pose proof degree_def_wrt_varref_close_def_wrt_varref_rec_degree_defs_wrt_varref_close_defs_wrt_varref_rec_degree_val_wrt_varref_close_val_wrt_varref_rec_degree_trm_wrt_varref_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_val_wrt_varref_close_val_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_trm_wrt_varref_close_trm_wrt_varref_rec :
forall t1 x1 n1,
  degree_trm_wrt_varref n1 t1 ->
  degree_trm_wrt_varref (S n1) (close_trm_wrt_varref_rec n1 x1 t1).
Proof.
pose proof degree_def_wrt_varref_close_def_wrt_varref_rec_degree_defs_wrt_varref_close_defs_wrt_varref_rec_degree_val_wrt_varref_close_val_wrt_varref_rec_degree_trm_wrt_varref_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_trm_wrt_varref_close_trm_wrt_varref_rec : lngen.

(* end hide *)

Lemma degree_varref_wrt_varref_close_varref_wrt_varref :
forall v1 x1,
  degree_varref_wrt_varref 0 v1 ->
  degree_varref_wrt_varref 1 (close_varref_wrt_varref x1 v1).
Proof.
unfold close_varref_wrt_varref; default_simp.
Qed.

Hint Resolve degree_varref_wrt_varref_close_varref_wrt_varref : lngen.

Lemma degree_typ_wrt_varref_close_typ_wrt_varref :
forall T1 x1,
  degree_typ_wrt_varref 0 T1 ->
  degree_typ_wrt_varref 1 (close_typ_wrt_varref x1 T1).
Proof.
unfold close_typ_wrt_varref; default_simp.
Qed.

Hint Resolve degree_typ_wrt_varref_close_typ_wrt_varref : lngen.

Lemma degree_dec_wrt_varref_close_dec_wrt_varref :
forall dec1 x1,
  degree_dec_wrt_varref 0 dec1 ->
  degree_dec_wrt_varref 1 (close_dec_wrt_varref x1 dec1).
Proof.
unfold close_dec_wrt_varref; default_simp.
Qed.

Hint Resolve degree_dec_wrt_varref_close_dec_wrt_varref : lngen.

Lemma degree_def_wrt_varref_close_def_wrt_varref :
forall d1 x1,
  degree_def_wrt_varref 0 d1 ->
  degree_def_wrt_varref 1 (close_def_wrt_varref x1 d1).
Proof.
unfold close_def_wrt_varref; default_simp.
Qed.

Hint Resolve degree_def_wrt_varref_close_def_wrt_varref : lngen.

Lemma degree_defs_wrt_varref_close_defs_wrt_varref :
forall defs1 x1,
  degree_defs_wrt_varref 0 defs1 ->
  degree_defs_wrt_varref 1 (close_defs_wrt_varref x1 defs1).
Proof.
unfold close_defs_wrt_varref; default_simp.
Qed.

Hint Resolve degree_defs_wrt_varref_close_defs_wrt_varref : lngen.

Lemma degree_val_wrt_varref_close_val_wrt_varref :
forall val1 x1,
  degree_val_wrt_varref 0 val1 ->
  degree_val_wrt_varref 1 (close_val_wrt_varref x1 val1).
Proof.
unfold close_val_wrt_varref; default_simp.
Qed.

Hint Resolve degree_val_wrt_varref_close_val_wrt_varref : lngen.

Lemma degree_trm_wrt_varref_close_trm_wrt_varref :
forall t1 x1,
  degree_trm_wrt_varref 0 t1 ->
  degree_trm_wrt_varref 1 (close_trm_wrt_varref x1 t1).
Proof.
unfold close_trm_wrt_varref; default_simp.
Qed.

Hint Resolve degree_trm_wrt_varref_close_trm_wrt_varref : lngen.

(* begin hide *)

Lemma degree_varref_wrt_varref_close_varref_wrt_varref_rec_inv_mutual :
(forall v1 x1 n1,
  degree_varref_wrt_varref (S n1) (close_varref_wrt_varref_rec n1 x1 v1) ->
  degree_varref_wrt_varref n1 v1).
Proof.
apply_mutual_ind varref_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_varref_wrt_varref_close_varref_wrt_varref_rec_inv :
forall v1 x1 n1,
  degree_varref_wrt_varref (S n1) (close_varref_wrt_varref_rec n1 x1 v1) ->
  degree_varref_wrt_varref n1 v1.
Proof.
pose proof degree_varref_wrt_varref_close_varref_wrt_varref_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_varref_wrt_varref_close_varref_wrt_varref_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_varref_close_typ_wrt_varref_rec_inv_degree_dec_wrt_varref_close_dec_wrt_varref_rec_inv_mutual :
(forall T1 x1 n1,
  degree_typ_wrt_varref (S n1) (close_typ_wrt_varref_rec n1 x1 T1) ->
  degree_typ_wrt_varref n1 T1) /\
(forall dec1 x1 n1,
  degree_dec_wrt_varref (S n1) (close_dec_wrt_varref_rec n1 x1 dec1) ->
  degree_dec_wrt_varref n1 dec1).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_varref_close_typ_wrt_varref_rec_inv :
forall T1 x1 n1,
  degree_typ_wrt_varref (S n1) (close_typ_wrt_varref_rec n1 x1 T1) ->
  degree_typ_wrt_varref n1 T1.
Proof.
pose proof degree_typ_wrt_varref_close_typ_wrt_varref_rec_inv_degree_dec_wrt_varref_close_dec_wrt_varref_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_typ_wrt_varref_close_typ_wrt_varref_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dec_wrt_varref_close_dec_wrt_varref_rec_inv :
forall dec1 x1 n1,
  degree_dec_wrt_varref (S n1) (close_dec_wrt_varref_rec n1 x1 dec1) ->
  degree_dec_wrt_varref n1 dec1.
Proof.
pose proof degree_typ_wrt_varref_close_typ_wrt_varref_rec_inv_degree_dec_wrt_varref_close_dec_wrt_varref_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_dec_wrt_varref_close_dec_wrt_varref_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_def_wrt_varref_close_def_wrt_varref_rec_inv_degree_defs_wrt_varref_close_defs_wrt_varref_rec_inv_degree_val_wrt_varref_close_val_wrt_varref_rec_inv_degree_trm_wrt_varref_close_trm_wrt_varref_rec_inv_mutual :
(forall d1 x1 n1,
  degree_def_wrt_varref (S n1) (close_def_wrt_varref_rec n1 x1 d1) ->
  degree_def_wrt_varref n1 d1) /\
(forall defs1 x1 n1,
  degree_defs_wrt_varref (S n1) (close_defs_wrt_varref_rec n1 x1 defs1) ->
  degree_defs_wrt_varref n1 defs1) /\
(forall val1 x1 n1,
  degree_val_wrt_varref (S n1) (close_val_wrt_varref_rec n1 x1 val1) ->
  degree_val_wrt_varref n1 val1) /\
(forall t1 x1 n1,
  degree_trm_wrt_varref (S n1) (close_trm_wrt_varref_rec n1 x1 t1) ->
  degree_trm_wrt_varref n1 t1).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_def_wrt_varref_close_def_wrt_varref_rec_inv :
forall d1 x1 n1,
  degree_def_wrt_varref (S n1) (close_def_wrt_varref_rec n1 x1 d1) ->
  degree_def_wrt_varref n1 d1.
Proof.
pose proof degree_def_wrt_varref_close_def_wrt_varref_rec_inv_degree_defs_wrt_varref_close_defs_wrt_varref_rec_inv_degree_val_wrt_varref_close_val_wrt_varref_rec_inv_degree_trm_wrt_varref_close_trm_wrt_varref_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_def_wrt_varref_close_def_wrt_varref_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_defs_wrt_varref_close_defs_wrt_varref_rec_inv :
forall defs1 x1 n1,
  degree_defs_wrt_varref (S n1) (close_defs_wrt_varref_rec n1 x1 defs1) ->
  degree_defs_wrt_varref n1 defs1.
Proof.
pose proof degree_def_wrt_varref_close_def_wrt_varref_rec_inv_degree_defs_wrt_varref_close_defs_wrt_varref_rec_inv_degree_val_wrt_varref_close_val_wrt_varref_rec_inv_degree_trm_wrt_varref_close_trm_wrt_varref_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_defs_wrt_varref_close_defs_wrt_varref_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_val_wrt_varref_close_val_wrt_varref_rec_inv :
forall val1 x1 n1,
  degree_val_wrt_varref (S n1) (close_val_wrt_varref_rec n1 x1 val1) ->
  degree_val_wrt_varref n1 val1.
Proof.
pose proof degree_def_wrt_varref_close_def_wrt_varref_rec_inv_degree_defs_wrt_varref_close_defs_wrt_varref_rec_inv_degree_val_wrt_varref_close_val_wrt_varref_rec_inv_degree_trm_wrt_varref_close_trm_wrt_varref_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_val_wrt_varref_close_val_wrt_varref_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_trm_wrt_varref_close_trm_wrt_varref_rec_inv :
forall t1 x1 n1,
  degree_trm_wrt_varref (S n1) (close_trm_wrt_varref_rec n1 x1 t1) ->
  degree_trm_wrt_varref n1 t1.
Proof.
pose proof degree_def_wrt_varref_close_def_wrt_varref_rec_inv_degree_defs_wrt_varref_close_defs_wrt_varref_rec_inv_degree_val_wrt_varref_close_val_wrt_varref_rec_inv_degree_trm_wrt_varref_close_trm_wrt_varref_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_trm_wrt_varref_close_trm_wrt_varref_rec_inv : lngen.

(* end hide *)

Lemma degree_varref_wrt_varref_close_varref_wrt_varref_inv :
forall v1 x1,
  degree_varref_wrt_varref 1 (close_varref_wrt_varref x1 v1) ->
  degree_varref_wrt_varref 0 v1.
Proof.
unfold close_varref_wrt_varref; eauto with lngen.
Qed.

Hint Immediate degree_varref_wrt_varref_close_varref_wrt_varref_inv : lngen.

Lemma degree_typ_wrt_varref_close_typ_wrt_varref_inv :
forall T1 x1,
  degree_typ_wrt_varref 1 (close_typ_wrt_varref x1 T1) ->
  degree_typ_wrt_varref 0 T1.
Proof.
unfold close_typ_wrt_varref; eauto with lngen.
Qed.

Hint Immediate degree_typ_wrt_varref_close_typ_wrt_varref_inv : lngen.

Lemma degree_dec_wrt_varref_close_dec_wrt_varref_inv :
forall dec1 x1,
  degree_dec_wrt_varref 1 (close_dec_wrt_varref x1 dec1) ->
  degree_dec_wrt_varref 0 dec1.
Proof.
unfold close_dec_wrt_varref; eauto with lngen.
Qed.

Hint Immediate degree_dec_wrt_varref_close_dec_wrt_varref_inv : lngen.

Lemma degree_def_wrt_varref_close_def_wrt_varref_inv :
forall d1 x1,
  degree_def_wrt_varref 1 (close_def_wrt_varref x1 d1) ->
  degree_def_wrt_varref 0 d1.
Proof.
unfold close_def_wrt_varref; eauto with lngen.
Qed.

Hint Immediate degree_def_wrt_varref_close_def_wrt_varref_inv : lngen.

Lemma degree_defs_wrt_varref_close_defs_wrt_varref_inv :
forall defs1 x1,
  degree_defs_wrt_varref 1 (close_defs_wrt_varref x1 defs1) ->
  degree_defs_wrt_varref 0 defs1.
Proof.
unfold close_defs_wrt_varref; eauto with lngen.
Qed.

Hint Immediate degree_defs_wrt_varref_close_defs_wrt_varref_inv : lngen.

Lemma degree_val_wrt_varref_close_val_wrt_varref_inv :
forall val1 x1,
  degree_val_wrt_varref 1 (close_val_wrt_varref x1 val1) ->
  degree_val_wrt_varref 0 val1.
Proof.
unfold close_val_wrt_varref; eauto with lngen.
Qed.

Hint Immediate degree_val_wrt_varref_close_val_wrt_varref_inv : lngen.

Lemma degree_trm_wrt_varref_close_trm_wrt_varref_inv :
forall t1 x1,
  degree_trm_wrt_varref 1 (close_trm_wrt_varref x1 t1) ->
  degree_trm_wrt_varref 0 t1.
Proof.
unfold close_trm_wrt_varref; eauto with lngen.
Qed.

Hint Immediate degree_trm_wrt_varref_close_trm_wrt_varref_inv : lngen.

(* begin hide *)

Lemma degree_varref_wrt_varref_open_varref_wrt_varref_rec_mutual :
(forall v1 v2 n1,
  degree_varref_wrt_varref (S n1) v1 ->
  degree_varref_wrt_varref n1 v2 ->
  degree_varref_wrt_varref n1 (open_varref_wrt_varref_rec n1 v2 v1)).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_varref_wrt_varref_open_varref_wrt_varref_rec :
forall v1 v2 n1,
  degree_varref_wrt_varref (S n1) v1 ->
  degree_varref_wrt_varref n1 v2 ->
  degree_varref_wrt_varref n1 (open_varref_wrt_varref_rec n1 v2 v1).
Proof.
pose proof degree_varref_wrt_varref_open_varref_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_varref_wrt_varref_open_varref_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_varref_open_typ_wrt_varref_rec_degree_dec_wrt_varref_open_dec_wrt_varref_rec_mutual :
(forall T1 v1 n1,
  degree_typ_wrt_varref (S n1) T1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_typ_wrt_varref n1 (open_typ_wrt_varref_rec n1 v1 T1)) /\
(forall dec1 v1 n1,
  degree_dec_wrt_varref (S n1) dec1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_dec_wrt_varref n1 (open_dec_wrt_varref_rec n1 v1 dec1)).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_varref_open_typ_wrt_varref_rec :
forall T1 v1 n1,
  degree_typ_wrt_varref (S n1) T1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_typ_wrt_varref n1 (open_typ_wrt_varref_rec n1 v1 T1).
Proof.
pose proof degree_typ_wrt_varref_open_typ_wrt_varref_rec_degree_dec_wrt_varref_open_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_varref_open_typ_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dec_wrt_varref_open_dec_wrt_varref_rec :
forall dec1 v1 n1,
  degree_dec_wrt_varref (S n1) dec1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_dec_wrt_varref n1 (open_dec_wrt_varref_rec n1 v1 dec1).
Proof.
pose proof degree_typ_wrt_varref_open_typ_wrt_varref_rec_degree_dec_wrt_varref_open_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dec_wrt_varref_open_dec_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_def_wrt_varref_open_def_wrt_varref_rec_degree_defs_wrt_varref_open_defs_wrt_varref_rec_degree_val_wrt_varref_open_val_wrt_varref_rec_degree_trm_wrt_varref_open_trm_wrt_varref_rec_mutual :
(forall d1 v1 n1,
  degree_def_wrt_varref (S n1) d1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_def_wrt_varref n1 (open_def_wrt_varref_rec n1 v1 d1)) /\
(forall defs1 v1 n1,
  degree_defs_wrt_varref (S n1) defs1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_defs_wrt_varref n1 (open_defs_wrt_varref_rec n1 v1 defs1)) /\
(forall val1 v1 n1,
  degree_val_wrt_varref (S n1) val1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_val_wrt_varref n1 (open_val_wrt_varref_rec n1 v1 val1)) /\
(forall t1 v1 n1,
  degree_trm_wrt_varref (S n1) t1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_trm_wrt_varref n1 (open_trm_wrt_varref_rec n1 v1 t1)).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_def_wrt_varref_open_def_wrt_varref_rec :
forall d1 v1 n1,
  degree_def_wrt_varref (S n1) d1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_def_wrt_varref n1 (open_def_wrt_varref_rec n1 v1 d1).
Proof.
pose proof degree_def_wrt_varref_open_def_wrt_varref_rec_degree_defs_wrt_varref_open_defs_wrt_varref_rec_degree_val_wrt_varref_open_val_wrt_varref_rec_degree_trm_wrt_varref_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_def_wrt_varref_open_def_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_defs_wrt_varref_open_defs_wrt_varref_rec :
forall defs1 v1 n1,
  degree_defs_wrt_varref (S n1) defs1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_defs_wrt_varref n1 (open_defs_wrt_varref_rec n1 v1 defs1).
Proof.
pose proof degree_def_wrt_varref_open_def_wrt_varref_rec_degree_defs_wrt_varref_open_defs_wrt_varref_rec_degree_val_wrt_varref_open_val_wrt_varref_rec_degree_trm_wrt_varref_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_defs_wrt_varref_open_defs_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_val_wrt_varref_open_val_wrt_varref_rec :
forall val1 v1 n1,
  degree_val_wrt_varref (S n1) val1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_val_wrt_varref n1 (open_val_wrt_varref_rec n1 v1 val1).
Proof.
pose proof degree_def_wrt_varref_open_def_wrt_varref_rec_degree_defs_wrt_varref_open_defs_wrt_varref_rec_degree_val_wrt_varref_open_val_wrt_varref_rec_degree_trm_wrt_varref_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_val_wrt_varref_open_val_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_trm_wrt_varref_open_trm_wrt_varref_rec :
forall t1 v1 n1,
  degree_trm_wrt_varref (S n1) t1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_trm_wrt_varref n1 (open_trm_wrt_varref_rec n1 v1 t1).
Proof.
pose proof degree_def_wrt_varref_open_def_wrt_varref_rec_degree_defs_wrt_varref_open_defs_wrt_varref_rec_degree_val_wrt_varref_open_val_wrt_varref_rec_degree_trm_wrt_varref_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_trm_wrt_varref_open_trm_wrt_varref_rec : lngen.

(* end hide *)

Lemma degree_varref_wrt_varref_open_varref_wrt_varref :
forall v1 v2,
  degree_varref_wrt_varref 1 v1 ->
  degree_varref_wrt_varref 0 v2 ->
  degree_varref_wrt_varref 0 (open_varref_wrt_varref v1 v2).
Proof.
unfold open_varref_wrt_varref; default_simp.
Qed.

Hint Resolve degree_varref_wrt_varref_open_varref_wrt_varref : lngen.

Lemma degree_typ_wrt_varref_open_typ_wrt_varref :
forall T1 v1,
  degree_typ_wrt_varref 1 T1 ->
  degree_varref_wrt_varref 0 v1 ->
  degree_typ_wrt_varref 0 (open_typ_wrt_varref T1 v1).
Proof.
unfold open_typ_wrt_varref; default_simp.
Qed.

Hint Resolve degree_typ_wrt_varref_open_typ_wrt_varref : lngen.

Lemma degree_dec_wrt_varref_open_dec_wrt_varref :
forall dec1 v1,
  degree_dec_wrt_varref 1 dec1 ->
  degree_varref_wrt_varref 0 v1 ->
  degree_dec_wrt_varref 0 (open_dec_wrt_varref dec1 v1).
Proof.
unfold open_dec_wrt_varref; default_simp.
Qed.

Hint Resolve degree_dec_wrt_varref_open_dec_wrt_varref : lngen.

Lemma degree_def_wrt_varref_open_def_wrt_varref :
forall d1 v1,
  degree_def_wrt_varref 1 d1 ->
  degree_varref_wrt_varref 0 v1 ->
  degree_def_wrt_varref 0 (open_def_wrt_varref d1 v1).
Proof.
unfold open_def_wrt_varref; default_simp.
Qed.

Hint Resolve degree_def_wrt_varref_open_def_wrt_varref : lngen.

Lemma degree_defs_wrt_varref_open_defs_wrt_varref :
forall defs1 v1,
  degree_defs_wrt_varref 1 defs1 ->
  degree_varref_wrt_varref 0 v1 ->
  degree_defs_wrt_varref 0 (open_defs_wrt_varref defs1 v1).
Proof.
unfold open_defs_wrt_varref; default_simp.
Qed.

Hint Resolve degree_defs_wrt_varref_open_defs_wrt_varref : lngen.

Lemma degree_val_wrt_varref_open_val_wrt_varref :
forall val1 v1,
  degree_val_wrt_varref 1 val1 ->
  degree_varref_wrt_varref 0 v1 ->
  degree_val_wrt_varref 0 (open_val_wrt_varref val1 v1).
Proof.
unfold open_val_wrt_varref; default_simp.
Qed.

Hint Resolve degree_val_wrt_varref_open_val_wrt_varref : lngen.

Lemma degree_trm_wrt_varref_open_trm_wrt_varref :
forall t1 v1,
  degree_trm_wrt_varref 1 t1 ->
  degree_varref_wrt_varref 0 v1 ->
  degree_trm_wrt_varref 0 (open_trm_wrt_varref t1 v1).
Proof.
unfold open_trm_wrt_varref; default_simp.
Qed.

Hint Resolve degree_trm_wrt_varref_open_trm_wrt_varref : lngen.

(* begin hide *)

Lemma degree_varref_wrt_varref_open_varref_wrt_varref_rec_inv_mutual :
(forall v1 v2 n1,
  degree_varref_wrt_varref n1 (open_varref_wrt_varref_rec n1 v2 v1) ->
  degree_varref_wrt_varref (S n1) v1).
Proof.
apply_mutual_ind varref_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_varref_wrt_varref_open_varref_wrt_varref_rec_inv :
forall v1 v2 n1,
  degree_varref_wrt_varref n1 (open_varref_wrt_varref_rec n1 v2 v1) ->
  degree_varref_wrt_varref (S n1) v1.
Proof.
pose proof degree_varref_wrt_varref_open_varref_wrt_varref_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_varref_wrt_varref_open_varref_wrt_varref_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_varref_open_typ_wrt_varref_rec_inv_degree_dec_wrt_varref_open_dec_wrt_varref_rec_inv_mutual :
(forall T1 v1 n1,
  degree_typ_wrt_varref n1 (open_typ_wrt_varref_rec n1 v1 T1) ->
  degree_typ_wrt_varref (S n1) T1) /\
(forall dec1 v1 n1,
  degree_dec_wrt_varref n1 (open_dec_wrt_varref_rec n1 v1 dec1) ->
  degree_dec_wrt_varref (S n1) dec1).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_varref_open_typ_wrt_varref_rec_inv :
forall T1 v1 n1,
  degree_typ_wrt_varref n1 (open_typ_wrt_varref_rec n1 v1 T1) ->
  degree_typ_wrt_varref (S n1) T1.
Proof.
pose proof degree_typ_wrt_varref_open_typ_wrt_varref_rec_inv_degree_dec_wrt_varref_open_dec_wrt_varref_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_typ_wrt_varref_open_typ_wrt_varref_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dec_wrt_varref_open_dec_wrt_varref_rec_inv :
forall dec1 v1 n1,
  degree_dec_wrt_varref n1 (open_dec_wrt_varref_rec n1 v1 dec1) ->
  degree_dec_wrt_varref (S n1) dec1.
Proof.
pose proof degree_typ_wrt_varref_open_typ_wrt_varref_rec_inv_degree_dec_wrt_varref_open_dec_wrt_varref_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_dec_wrt_varref_open_dec_wrt_varref_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_def_wrt_varref_open_def_wrt_varref_rec_inv_degree_defs_wrt_varref_open_defs_wrt_varref_rec_inv_degree_val_wrt_varref_open_val_wrt_varref_rec_inv_degree_trm_wrt_varref_open_trm_wrt_varref_rec_inv_mutual :
(forall d1 v1 n1,
  degree_def_wrt_varref n1 (open_def_wrt_varref_rec n1 v1 d1) ->
  degree_def_wrt_varref (S n1) d1) /\
(forall defs1 v1 n1,
  degree_defs_wrt_varref n1 (open_defs_wrt_varref_rec n1 v1 defs1) ->
  degree_defs_wrt_varref (S n1) defs1) /\
(forall val1 v1 n1,
  degree_val_wrt_varref n1 (open_val_wrt_varref_rec n1 v1 val1) ->
  degree_val_wrt_varref (S n1) val1) /\
(forall t1 v1 n1,
  degree_trm_wrt_varref n1 (open_trm_wrt_varref_rec n1 v1 t1) ->
  degree_trm_wrt_varref (S n1) t1).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_def_wrt_varref_open_def_wrt_varref_rec_inv :
forall d1 v1 n1,
  degree_def_wrt_varref n1 (open_def_wrt_varref_rec n1 v1 d1) ->
  degree_def_wrt_varref (S n1) d1.
Proof.
pose proof degree_def_wrt_varref_open_def_wrt_varref_rec_inv_degree_defs_wrt_varref_open_defs_wrt_varref_rec_inv_degree_val_wrt_varref_open_val_wrt_varref_rec_inv_degree_trm_wrt_varref_open_trm_wrt_varref_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_def_wrt_varref_open_def_wrt_varref_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_defs_wrt_varref_open_defs_wrt_varref_rec_inv :
forall defs1 v1 n1,
  degree_defs_wrt_varref n1 (open_defs_wrt_varref_rec n1 v1 defs1) ->
  degree_defs_wrt_varref (S n1) defs1.
Proof.
pose proof degree_def_wrt_varref_open_def_wrt_varref_rec_inv_degree_defs_wrt_varref_open_defs_wrt_varref_rec_inv_degree_val_wrt_varref_open_val_wrt_varref_rec_inv_degree_trm_wrt_varref_open_trm_wrt_varref_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_defs_wrt_varref_open_defs_wrt_varref_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_val_wrt_varref_open_val_wrt_varref_rec_inv :
forall val1 v1 n1,
  degree_val_wrt_varref n1 (open_val_wrt_varref_rec n1 v1 val1) ->
  degree_val_wrt_varref (S n1) val1.
Proof.
pose proof degree_def_wrt_varref_open_def_wrt_varref_rec_inv_degree_defs_wrt_varref_open_defs_wrt_varref_rec_inv_degree_val_wrt_varref_open_val_wrt_varref_rec_inv_degree_trm_wrt_varref_open_trm_wrt_varref_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_val_wrt_varref_open_val_wrt_varref_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_trm_wrt_varref_open_trm_wrt_varref_rec_inv :
forall t1 v1 n1,
  degree_trm_wrt_varref n1 (open_trm_wrt_varref_rec n1 v1 t1) ->
  degree_trm_wrt_varref (S n1) t1.
Proof.
pose proof degree_def_wrt_varref_open_def_wrt_varref_rec_inv_degree_defs_wrt_varref_open_defs_wrt_varref_rec_inv_degree_val_wrt_varref_open_val_wrt_varref_rec_inv_degree_trm_wrt_varref_open_trm_wrt_varref_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_trm_wrt_varref_open_trm_wrt_varref_rec_inv : lngen.

(* end hide *)

Lemma degree_varref_wrt_varref_open_varref_wrt_varref_inv :
forall v1 v2,
  degree_varref_wrt_varref 0 (open_varref_wrt_varref v1 v2) ->
  degree_varref_wrt_varref 1 v1.
Proof.
unfold open_varref_wrt_varref; eauto with lngen.
Qed.

Hint Immediate degree_varref_wrt_varref_open_varref_wrt_varref_inv : lngen.

Lemma degree_typ_wrt_varref_open_typ_wrt_varref_inv :
forall T1 v1,
  degree_typ_wrt_varref 0 (open_typ_wrt_varref T1 v1) ->
  degree_typ_wrt_varref 1 T1.
Proof.
unfold open_typ_wrt_varref; eauto with lngen.
Qed.

Hint Immediate degree_typ_wrt_varref_open_typ_wrt_varref_inv : lngen.

Lemma degree_dec_wrt_varref_open_dec_wrt_varref_inv :
forall dec1 v1,
  degree_dec_wrt_varref 0 (open_dec_wrt_varref dec1 v1) ->
  degree_dec_wrt_varref 1 dec1.
Proof.
unfold open_dec_wrt_varref; eauto with lngen.
Qed.

Hint Immediate degree_dec_wrt_varref_open_dec_wrt_varref_inv : lngen.

Lemma degree_def_wrt_varref_open_def_wrt_varref_inv :
forall d1 v1,
  degree_def_wrt_varref 0 (open_def_wrt_varref d1 v1) ->
  degree_def_wrt_varref 1 d1.
Proof.
unfold open_def_wrt_varref; eauto with lngen.
Qed.

Hint Immediate degree_def_wrt_varref_open_def_wrt_varref_inv : lngen.

Lemma degree_defs_wrt_varref_open_defs_wrt_varref_inv :
forall defs1 v1,
  degree_defs_wrt_varref 0 (open_defs_wrt_varref defs1 v1) ->
  degree_defs_wrt_varref 1 defs1.
Proof.
unfold open_defs_wrt_varref; eauto with lngen.
Qed.

Hint Immediate degree_defs_wrt_varref_open_defs_wrt_varref_inv : lngen.

Lemma degree_val_wrt_varref_open_val_wrt_varref_inv :
forall val1 v1,
  degree_val_wrt_varref 0 (open_val_wrt_varref val1 v1) ->
  degree_val_wrt_varref 1 val1.
Proof.
unfold open_val_wrt_varref; eauto with lngen.
Qed.

Hint Immediate degree_val_wrt_varref_open_val_wrt_varref_inv : lngen.

Lemma degree_trm_wrt_varref_open_trm_wrt_varref_inv :
forall t1 v1,
  degree_trm_wrt_varref 0 (open_trm_wrt_varref t1 v1) ->
  degree_trm_wrt_varref 1 t1.
Proof.
unfold open_trm_wrt_varref; eauto with lngen.
Qed.

Hint Immediate degree_trm_wrt_varref_open_trm_wrt_varref_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_varref_wrt_varref_rec_inj_mutual :
(forall v1 v2 x1 n1,
  close_varref_wrt_varref_rec n1 x1 v1 = close_varref_wrt_varref_rec n1 x1 v2 ->
  v1 = v2).
Proof.
apply_mutual_ind varref_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_varref_wrt_varref_rec_inj :
forall v1 v2 x1 n1,
  close_varref_wrt_varref_rec n1 x1 v1 = close_varref_wrt_varref_rec n1 x1 v2 ->
  v1 = v2.
Proof.
pose proof close_varref_wrt_varref_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_varref_wrt_varref_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_varref_rec_inj_close_dec_wrt_varref_rec_inj_mutual :
(forall T1 T2 x1 n1,
  close_typ_wrt_varref_rec n1 x1 T1 = close_typ_wrt_varref_rec n1 x1 T2 ->
  T1 = T2) /\
(forall dec1 dec2 x1 n1,
  close_dec_wrt_varref_rec n1 x1 dec1 = close_dec_wrt_varref_rec n1 x1 dec2 ->
  dec1 = dec2).
Proof.
apply_mutual_ind typ_dec_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_varref_rec_inj :
forall T1 T2 x1 n1,
  close_typ_wrt_varref_rec n1 x1 T1 = close_typ_wrt_varref_rec n1 x1 T2 ->
  T1 = T2.
Proof.
pose proof close_typ_wrt_varref_rec_inj_close_dec_wrt_varref_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_typ_wrt_varref_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dec_wrt_varref_rec_inj :
forall dec1 dec2 x1 n1,
  close_dec_wrt_varref_rec n1 x1 dec1 = close_dec_wrt_varref_rec n1 x1 dec2 ->
  dec1 = dec2.
Proof.
pose proof close_typ_wrt_varref_rec_inj_close_dec_wrt_varref_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_dec_wrt_varref_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_def_wrt_varref_rec_inj_close_defs_wrt_varref_rec_inj_close_val_wrt_varref_rec_inj_close_trm_wrt_varref_rec_inj_mutual :
(forall d1 d2 x1 n1,
  close_def_wrt_varref_rec n1 x1 d1 = close_def_wrt_varref_rec n1 x1 d2 ->
  d1 = d2) /\
(forall defs1 defs2 x1 n1,
  close_defs_wrt_varref_rec n1 x1 defs1 = close_defs_wrt_varref_rec n1 x1 defs2 ->
  defs1 = defs2) /\
(forall val1 val2 x1 n1,
  close_val_wrt_varref_rec n1 x1 val1 = close_val_wrt_varref_rec n1 x1 val2 ->
  val1 = val2) /\
(forall t1 t2 x1 n1,
  close_trm_wrt_varref_rec n1 x1 t1 = close_trm_wrt_varref_rec n1 x1 t2 ->
  t1 = t2).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_def_wrt_varref_rec_inj :
forall d1 d2 x1 n1,
  close_def_wrt_varref_rec n1 x1 d1 = close_def_wrt_varref_rec n1 x1 d2 ->
  d1 = d2.
Proof.
pose proof close_def_wrt_varref_rec_inj_close_defs_wrt_varref_rec_inj_close_val_wrt_varref_rec_inj_close_trm_wrt_varref_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_def_wrt_varref_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_defs_wrt_varref_rec_inj :
forall defs1 defs2 x1 n1,
  close_defs_wrt_varref_rec n1 x1 defs1 = close_defs_wrt_varref_rec n1 x1 defs2 ->
  defs1 = defs2.
Proof.
pose proof close_def_wrt_varref_rec_inj_close_defs_wrt_varref_rec_inj_close_val_wrt_varref_rec_inj_close_trm_wrt_varref_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_defs_wrt_varref_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_val_wrt_varref_rec_inj :
forall val1 val2 x1 n1,
  close_val_wrt_varref_rec n1 x1 val1 = close_val_wrt_varref_rec n1 x1 val2 ->
  val1 = val2.
Proof.
pose proof close_def_wrt_varref_rec_inj_close_defs_wrt_varref_rec_inj_close_val_wrt_varref_rec_inj_close_trm_wrt_varref_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_val_wrt_varref_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_trm_wrt_varref_rec_inj :
forall t1 t2 x1 n1,
  close_trm_wrt_varref_rec n1 x1 t1 = close_trm_wrt_varref_rec n1 x1 t2 ->
  t1 = t2.
Proof.
pose proof close_def_wrt_varref_rec_inj_close_defs_wrt_varref_rec_inj_close_val_wrt_varref_rec_inj_close_trm_wrt_varref_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_trm_wrt_varref_rec_inj : lngen.

(* end hide *)

Lemma close_varref_wrt_varref_inj :
forall v1 v2 x1,
  close_varref_wrt_varref x1 v1 = close_varref_wrt_varref x1 v2 ->
  v1 = v2.
Proof.
unfold close_varref_wrt_varref; eauto with lngen.
Qed.

Hint Immediate close_varref_wrt_varref_inj : lngen.

Lemma close_typ_wrt_varref_inj :
forall T1 T2 x1,
  close_typ_wrt_varref x1 T1 = close_typ_wrt_varref x1 T2 ->
  T1 = T2.
Proof.
unfold close_typ_wrt_varref; eauto with lngen.
Qed.

Hint Immediate close_typ_wrt_varref_inj : lngen.

Lemma close_dec_wrt_varref_inj :
forall dec1 dec2 x1,
  close_dec_wrt_varref x1 dec1 = close_dec_wrt_varref x1 dec2 ->
  dec1 = dec2.
Proof.
unfold close_dec_wrt_varref; eauto with lngen.
Qed.

Hint Immediate close_dec_wrt_varref_inj : lngen.

Lemma close_def_wrt_varref_inj :
forall d1 d2 x1,
  close_def_wrt_varref x1 d1 = close_def_wrt_varref x1 d2 ->
  d1 = d2.
Proof.
unfold close_def_wrt_varref; eauto with lngen.
Qed.

Hint Immediate close_def_wrt_varref_inj : lngen.

Lemma close_defs_wrt_varref_inj :
forall defs1 defs2 x1,
  close_defs_wrt_varref x1 defs1 = close_defs_wrt_varref x1 defs2 ->
  defs1 = defs2.
Proof.
unfold close_defs_wrt_varref; eauto with lngen.
Qed.

Hint Immediate close_defs_wrt_varref_inj : lngen.

Lemma close_val_wrt_varref_inj :
forall val1 val2 x1,
  close_val_wrt_varref x1 val1 = close_val_wrt_varref x1 val2 ->
  val1 = val2.
Proof.
unfold close_val_wrt_varref; eauto with lngen.
Qed.

Hint Immediate close_val_wrt_varref_inj : lngen.

Lemma close_trm_wrt_varref_inj :
forall t1 t2 x1,
  close_trm_wrt_varref x1 t1 = close_trm_wrt_varref x1 t2 ->
  t1 = t2.
Proof.
unfold close_trm_wrt_varref; eauto with lngen.
Qed.

Hint Immediate close_trm_wrt_varref_inj : lngen.

(* begin hide *)

Lemma close_varref_wrt_varref_rec_open_varref_wrt_varref_rec_mutual :
(forall v1 x1 n1,
  x1 `notin` fv_varref v1 ->
  close_varref_wrt_varref_rec n1 x1 (open_varref_wrt_varref_rec n1 (var_termvar_f x1) v1) = v1).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_varref_wrt_varref_rec_open_varref_wrt_varref_rec :
forall v1 x1 n1,
  x1 `notin` fv_varref v1 ->
  close_varref_wrt_varref_rec n1 x1 (open_varref_wrt_varref_rec n1 (var_termvar_f x1) v1) = v1.
Proof.
pose proof close_varref_wrt_varref_rec_open_varref_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_varref_wrt_varref_rec_open_varref_wrt_varref_rec : lngen.
Hint Rewrite close_varref_wrt_varref_rec_open_varref_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_varref_rec_open_typ_wrt_varref_rec_close_dec_wrt_varref_rec_open_dec_wrt_varref_rec_mutual :
(forall T1 x1 n1,
  x1 `notin` fv_typ T1 ->
  close_typ_wrt_varref_rec n1 x1 (open_typ_wrt_varref_rec n1 (var_termvar_f x1) T1) = T1) /\
(forall dec1 x1 n1,
  x1 `notin` fv_dec dec1 ->
  close_dec_wrt_varref_rec n1 x1 (open_dec_wrt_varref_rec n1 (var_termvar_f x1) dec1) = dec1).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_varref_rec_open_typ_wrt_varref_rec :
forall T1 x1 n1,
  x1 `notin` fv_typ T1 ->
  close_typ_wrt_varref_rec n1 x1 (open_typ_wrt_varref_rec n1 (var_termvar_f x1) T1) = T1.
Proof.
pose proof close_typ_wrt_varref_rec_open_typ_wrt_varref_rec_close_dec_wrt_varref_rec_open_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_typ_wrt_varref_rec_open_typ_wrt_varref_rec : lngen.
Hint Rewrite close_typ_wrt_varref_rec_open_typ_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dec_wrt_varref_rec_open_dec_wrt_varref_rec :
forall dec1 x1 n1,
  x1 `notin` fv_dec dec1 ->
  close_dec_wrt_varref_rec n1 x1 (open_dec_wrt_varref_rec n1 (var_termvar_f x1) dec1) = dec1.
Proof.
pose proof close_typ_wrt_varref_rec_open_typ_wrt_varref_rec_close_dec_wrt_varref_rec_open_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_dec_wrt_varref_rec_open_dec_wrt_varref_rec : lngen.
Hint Rewrite close_dec_wrt_varref_rec_open_dec_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_def_wrt_varref_rec_open_def_wrt_varref_rec_close_defs_wrt_varref_rec_open_defs_wrt_varref_rec_close_val_wrt_varref_rec_open_val_wrt_varref_rec_close_trm_wrt_varref_rec_open_trm_wrt_varref_rec_mutual :
(forall d1 x1 n1,
  x1 `notin` fv_def d1 ->
  close_def_wrt_varref_rec n1 x1 (open_def_wrt_varref_rec n1 (var_termvar_f x1) d1) = d1) /\
(forall defs1 x1 n1,
  x1 `notin` fv_defs defs1 ->
  close_defs_wrt_varref_rec n1 x1 (open_defs_wrt_varref_rec n1 (var_termvar_f x1) defs1) = defs1) /\
(forall val1 x1 n1,
  x1 `notin` fv_val val1 ->
  close_val_wrt_varref_rec n1 x1 (open_val_wrt_varref_rec n1 (var_termvar_f x1) val1) = val1) /\
(forall t1 x1 n1,
  x1 `notin` fv_trm t1 ->
  close_trm_wrt_varref_rec n1 x1 (open_trm_wrt_varref_rec n1 (var_termvar_f x1) t1) = t1).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_def_wrt_varref_rec_open_def_wrt_varref_rec :
forall d1 x1 n1,
  x1 `notin` fv_def d1 ->
  close_def_wrt_varref_rec n1 x1 (open_def_wrt_varref_rec n1 (var_termvar_f x1) d1) = d1.
Proof.
pose proof close_def_wrt_varref_rec_open_def_wrt_varref_rec_close_defs_wrt_varref_rec_open_defs_wrt_varref_rec_close_val_wrt_varref_rec_open_val_wrt_varref_rec_close_trm_wrt_varref_rec_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_def_wrt_varref_rec_open_def_wrt_varref_rec : lngen.
Hint Rewrite close_def_wrt_varref_rec_open_def_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_defs_wrt_varref_rec_open_defs_wrt_varref_rec :
forall defs1 x1 n1,
  x1 `notin` fv_defs defs1 ->
  close_defs_wrt_varref_rec n1 x1 (open_defs_wrt_varref_rec n1 (var_termvar_f x1) defs1) = defs1.
Proof.
pose proof close_def_wrt_varref_rec_open_def_wrt_varref_rec_close_defs_wrt_varref_rec_open_defs_wrt_varref_rec_close_val_wrt_varref_rec_open_val_wrt_varref_rec_close_trm_wrt_varref_rec_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_defs_wrt_varref_rec_open_defs_wrt_varref_rec : lngen.
Hint Rewrite close_defs_wrt_varref_rec_open_defs_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_val_wrt_varref_rec_open_val_wrt_varref_rec :
forall val1 x1 n1,
  x1 `notin` fv_val val1 ->
  close_val_wrt_varref_rec n1 x1 (open_val_wrt_varref_rec n1 (var_termvar_f x1) val1) = val1.
Proof.
pose proof close_def_wrt_varref_rec_open_def_wrt_varref_rec_close_defs_wrt_varref_rec_open_defs_wrt_varref_rec_close_val_wrt_varref_rec_open_val_wrt_varref_rec_close_trm_wrt_varref_rec_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_val_wrt_varref_rec_open_val_wrt_varref_rec : lngen.
Hint Rewrite close_val_wrt_varref_rec_open_val_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_trm_wrt_varref_rec_open_trm_wrt_varref_rec :
forall t1 x1 n1,
  x1 `notin` fv_trm t1 ->
  close_trm_wrt_varref_rec n1 x1 (open_trm_wrt_varref_rec n1 (var_termvar_f x1) t1) = t1.
Proof.
pose proof close_def_wrt_varref_rec_open_def_wrt_varref_rec_close_defs_wrt_varref_rec_open_defs_wrt_varref_rec_close_val_wrt_varref_rec_open_val_wrt_varref_rec_close_trm_wrt_varref_rec_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_trm_wrt_varref_rec_open_trm_wrt_varref_rec : lngen.
Hint Rewrite close_trm_wrt_varref_rec_open_trm_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_varref_wrt_varref_open_varref_wrt_varref :
forall v1 x1,
  x1 `notin` fv_varref v1 ->
  close_varref_wrt_varref x1 (open_varref_wrt_varref v1 (var_termvar_f x1)) = v1.
Proof.
unfold close_varref_wrt_varref; unfold open_varref_wrt_varref; default_simp.
Qed.

Hint Resolve close_varref_wrt_varref_open_varref_wrt_varref : lngen.
Hint Rewrite close_varref_wrt_varref_open_varref_wrt_varref using solve [auto] : lngen.

Lemma close_typ_wrt_varref_open_typ_wrt_varref :
forall T1 x1,
  x1 `notin` fv_typ T1 ->
  close_typ_wrt_varref x1 (open_typ_wrt_varref T1 (var_termvar_f x1)) = T1.
Proof.
unfold close_typ_wrt_varref; unfold open_typ_wrt_varref; default_simp.
Qed.

Hint Resolve close_typ_wrt_varref_open_typ_wrt_varref : lngen.
Hint Rewrite close_typ_wrt_varref_open_typ_wrt_varref using solve [auto] : lngen.

Lemma close_dec_wrt_varref_open_dec_wrt_varref :
forall dec1 x1,
  x1 `notin` fv_dec dec1 ->
  close_dec_wrt_varref x1 (open_dec_wrt_varref dec1 (var_termvar_f x1)) = dec1.
Proof.
unfold close_dec_wrt_varref; unfold open_dec_wrt_varref; default_simp.
Qed.

Hint Resolve close_dec_wrt_varref_open_dec_wrt_varref : lngen.
Hint Rewrite close_dec_wrt_varref_open_dec_wrt_varref using solve [auto] : lngen.

Lemma close_def_wrt_varref_open_def_wrt_varref :
forall d1 x1,
  x1 `notin` fv_def d1 ->
  close_def_wrt_varref x1 (open_def_wrt_varref d1 (var_termvar_f x1)) = d1.
Proof.
unfold close_def_wrt_varref; unfold open_def_wrt_varref; default_simp.
Qed.

Hint Resolve close_def_wrt_varref_open_def_wrt_varref : lngen.
Hint Rewrite close_def_wrt_varref_open_def_wrt_varref using solve [auto] : lngen.

Lemma close_defs_wrt_varref_open_defs_wrt_varref :
forall defs1 x1,
  x1 `notin` fv_defs defs1 ->
  close_defs_wrt_varref x1 (open_defs_wrt_varref defs1 (var_termvar_f x1)) = defs1.
Proof.
unfold close_defs_wrt_varref; unfold open_defs_wrt_varref; default_simp.
Qed.

Hint Resolve close_defs_wrt_varref_open_defs_wrt_varref : lngen.
Hint Rewrite close_defs_wrt_varref_open_defs_wrt_varref using solve [auto] : lngen.

Lemma close_val_wrt_varref_open_val_wrt_varref :
forall val1 x1,
  x1 `notin` fv_val val1 ->
  close_val_wrt_varref x1 (open_val_wrt_varref val1 (var_termvar_f x1)) = val1.
Proof.
unfold close_val_wrt_varref; unfold open_val_wrt_varref; default_simp.
Qed.

Hint Resolve close_val_wrt_varref_open_val_wrt_varref : lngen.
Hint Rewrite close_val_wrt_varref_open_val_wrt_varref using solve [auto] : lngen.

Lemma close_trm_wrt_varref_open_trm_wrt_varref :
forall t1 x1,
  x1 `notin` fv_trm t1 ->
  close_trm_wrt_varref x1 (open_trm_wrt_varref t1 (var_termvar_f x1)) = t1.
Proof.
unfold close_trm_wrt_varref; unfold open_trm_wrt_varref; default_simp.
Qed.

Hint Resolve close_trm_wrt_varref_open_trm_wrt_varref : lngen.
Hint Rewrite close_trm_wrt_varref_open_trm_wrt_varref using solve [auto] : lngen.

(* begin hide *)

Lemma open_varref_wrt_varref_rec_close_varref_wrt_varref_rec_mutual :
(forall v1 x1 n1,
  open_varref_wrt_varref_rec n1 (var_termvar_f x1) (close_varref_wrt_varref_rec n1 x1 v1) = v1).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_varref_wrt_varref_rec_close_varref_wrt_varref_rec :
forall v1 x1 n1,
  open_varref_wrt_varref_rec n1 (var_termvar_f x1) (close_varref_wrt_varref_rec n1 x1 v1) = v1.
Proof.
pose proof open_varref_wrt_varref_rec_close_varref_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_varref_wrt_varref_rec_close_varref_wrt_varref_rec : lngen.
Hint Rewrite open_varref_wrt_varref_rec_close_varref_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_varref_rec_close_typ_wrt_varref_rec_open_dec_wrt_varref_rec_close_dec_wrt_varref_rec_mutual :
(forall T1 x1 n1,
  open_typ_wrt_varref_rec n1 (var_termvar_f x1) (close_typ_wrt_varref_rec n1 x1 T1) = T1) /\
(forall dec1 x1 n1,
  open_dec_wrt_varref_rec n1 (var_termvar_f x1) (close_dec_wrt_varref_rec n1 x1 dec1) = dec1).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_varref_rec_close_typ_wrt_varref_rec :
forall T1 x1 n1,
  open_typ_wrt_varref_rec n1 (var_termvar_f x1) (close_typ_wrt_varref_rec n1 x1 T1) = T1.
Proof.
pose proof open_typ_wrt_varref_rec_close_typ_wrt_varref_rec_open_dec_wrt_varref_rec_close_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_typ_wrt_varref_rec_close_typ_wrt_varref_rec : lngen.
Hint Rewrite open_typ_wrt_varref_rec_close_typ_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dec_wrt_varref_rec_close_dec_wrt_varref_rec :
forall dec1 x1 n1,
  open_dec_wrt_varref_rec n1 (var_termvar_f x1) (close_dec_wrt_varref_rec n1 x1 dec1) = dec1.
Proof.
pose proof open_typ_wrt_varref_rec_close_typ_wrt_varref_rec_open_dec_wrt_varref_rec_close_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_dec_wrt_varref_rec_close_dec_wrt_varref_rec : lngen.
Hint Rewrite open_dec_wrt_varref_rec_close_dec_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_def_wrt_varref_rec_close_def_wrt_varref_rec_open_defs_wrt_varref_rec_close_defs_wrt_varref_rec_open_val_wrt_varref_rec_close_val_wrt_varref_rec_open_trm_wrt_varref_rec_close_trm_wrt_varref_rec_mutual :
(forall d1 x1 n1,
  open_def_wrt_varref_rec n1 (var_termvar_f x1) (close_def_wrt_varref_rec n1 x1 d1) = d1) /\
(forall defs1 x1 n1,
  open_defs_wrt_varref_rec n1 (var_termvar_f x1) (close_defs_wrt_varref_rec n1 x1 defs1) = defs1) /\
(forall val1 x1 n1,
  open_val_wrt_varref_rec n1 (var_termvar_f x1) (close_val_wrt_varref_rec n1 x1 val1) = val1) /\
(forall t1 x1 n1,
  open_trm_wrt_varref_rec n1 (var_termvar_f x1) (close_trm_wrt_varref_rec n1 x1 t1) = t1).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_def_wrt_varref_rec_close_def_wrt_varref_rec :
forall d1 x1 n1,
  open_def_wrt_varref_rec n1 (var_termvar_f x1) (close_def_wrt_varref_rec n1 x1 d1) = d1.
Proof.
pose proof open_def_wrt_varref_rec_close_def_wrt_varref_rec_open_defs_wrt_varref_rec_close_defs_wrt_varref_rec_open_val_wrt_varref_rec_close_val_wrt_varref_rec_open_trm_wrt_varref_rec_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_def_wrt_varref_rec_close_def_wrt_varref_rec : lngen.
Hint Rewrite open_def_wrt_varref_rec_close_def_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_defs_wrt_varref_rec_close_defs_wrt_varref_rec :
forall defs1 x1 n1,
  open_defs_wrt_varref_rec n1 (var_termvar_f x1) (close_defs_wrt_varref_rec n1 x1 defs1) = defs1.
Proof.
pose proof open_def_wrt_varref_rec_close_def_wrt_varref_rec_open_defs_wrt_varref_rec_close_defs_wrt_varref_rec_open_val_wrt_varref_rec_close_val_wrt_varref_rec_open_trm_wrt_varref_rec_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_defs_wrt_varref_rec_close_defs_wrt_varref_rec : lngen.
Hint Rewrite open_defs_wrt_varref_rec_close_defs_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_val_wrt_varref_rec_close_val_wrt_varref_rec :
forall val1 x1 n1,
  open_val_wrt_varref_rec n1 (var_termvar_f x1) (close_val_wrt_varref_rec n1 x1 val1) = val1.
Proof.
pose proof open_def_wrt_varref_rec_close_def_wrt_varref_rec_open_defs_wrt_varref_rec_close_defs_wrt_varref_rec_open_val_wrt_varref_rec_close_val_wrt_varref_rec_open_trm_wrt_varref_rec_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_val_wrt_varref_rec_close_val_wrt_varref_rec : lngen.
Hint Rewrite open_val_wrt_varref_rec_close_val_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_trm_wrt_varref_rec_close_trm_wrt_varref_rec :
forall t1 x1 n1,
  open_trm_wrt_varref_rec n1 (var_termvar_f x1) (close_trm_wrt_varref_rec n1 x1 t1) = t1.
Proof.
pose proof open_def_wrt_varref_rec_close_def_wrt_varref_rec_open_defs_wrt_varref_rec_close_defs_wrt_varref_rec_open_val_wrt_varref_rec_close_val_wrt_varref_rec_open_trm_wrt_varref_rec_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_trm_wrt_varref_rec_close_trm_wrt_varref_rec : lngen.
Hint Rewrite open_trm_wrt_varref_rec_close_trm_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_varref_wrt_varref_close_varref_wrt_varref :
forall v1 x1,
  open_varref_wrt_varref (close_varref_wrt_varref x1 v1) (var_termvar_f x1) = v1.
Proof.
unfold close_varref_wrt_varref; unfold open_varref_wrt_varref; default_simp.
Qed.

Hint Resolve open_varref_wrt_varref_close_varref_wrt_varref : lngen.
Hint Rewrite open_varref_wrt_varref_close_varref_wrt_varref using solve [auto] : lngen.

Lemma open_typ_wrt_varref_close_typ_wrt_varref :
forall T1 x1,
  open_typ_wrt_varref (close_typ_wrt_varref x1 T1) (var_termvar_f x1) = T1.
Proof.
unfold close_typ_wrt_varref; unfold open_typ_wrt_varref; default_simp.
Qed.

Hint Resolve open_typ_wrt_varref_close_typ_wrt_varref : lngen.
Hint Rewrite open_typ_wrt_varref_close_typ_wrt_varref using solve [auto] : lngen.

Lemma open_dec_wrt_varref_close_dec_wrt_varref :
forall dec1 x1,
  open_dec_wrt_varref (close_dec_wrt_varref x1 dec1) (var_termvar_f x1) = dec1.
Proof.
unfold close_dec_wrt_varref; unfold open_dec_wrt_varref; default_simp.
Qed.

Hint Resolve open_dec_wrt_varref_close_dec_wrt_varref : lngen.
Hint Rewrite open_dec_wrt_varref_close_dec_wrt_varref using solve [auto] : lngen.

Lemma open_def_wrt_varref_close_def_wrt_varref :
forall d1 x1,
  open_def_wrt_varref (close_def_wrt_varref x1 d1) (var_termvar_f x1) = d1.
Proof.
unfold close_def_wrt_varref; unfold open_def_wrt_varref; default_simp.
Qed.

Hint Resolve open_def_wrt_varref_close_def_wrt_varref : lngen.
Hint Rewrite open_def_wrt_varref_close_def_wrt_varref using solve [auto] : lngen.

Lemma open_defs_wrt_varref_close_defs_wrt_varref :
forall defs1 x1,
  open_defs_wrt_varref (close_defs_wrt_varref x1 defs1) (var_termvar_f x1) = defs1.
Proof.
unfold close_defs_wrt_varref; unfold open_defs_wrt_varref; default_simp.
Qed.

Hint Resolve open_defs_wrt_varref_close_defs_wrt_varref : lngen.
Hint Rewrite open_defs_wrt_varref_close_defs_wrt_varref using solve [auto] : lngen.

Lemma open_val_wrt_varref_close_val_wrt_varref :
forall val1 x1,
  open_val_wrt_varref (close_val_wrt_varref x1 val1) (var_termvar_f x1) = val1.
Proof.
unfold close_val_wrt_varref; unfold open_val_wrt_varref; default_simp.
Qed.

Hint Resolve open_val_wrt_varref_close_val_wrt_varref : lngen.
Hint Rewrite open_val_wrt_varref_close_val_wrt_varref using solve [auto] : lngen.

Lemma open_trm_wrt_varref_close_trm_wrt_varref :
forall t1 x1,
  open_trm_wrt_varref (close_trm_wrt_varref x1 t1) (var_termvar_f x1) = t1.
Proof.
unfold close_trm_wrt_varref; unfold open_trm_wrt_varref; default_simp.
Qed.

Hint Resolve open_trm_wrt_varref_close_trm_wrt_varref : lngen.
Hint Rewrite open_trm_wrt_varref_close_trm_wrt_varref using solve [auto] : lngen.

(* begin hide *)

Lemma open_varref_wrt_varref_rec_inj_mutual :
(forall v2 v1 x1 n1,
  x1 `notin` fv_varref v2 ->
  x1 `notin` fv_varref v1 ->
  open_varref_wrt_varref_rec n1 (var_termvar_f x1) v2 = open_varref_wrt_varref_rec n1 (var_termvar_f x1) v1 ->
  v2 = v1).
Proof.
apply_mutual_ind varref_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_varref_wrt_varref_rec_inj :
forall v2 v1 x1 n1,
  x1 `notin` fv_varref v2 ->
  x1 `notin` fv_varref v1 ->
  open_varref_wrt_varref_rec n1 (var_termvar_f x1) v2 = open_varref_wrt_varref_rec n1 (var_termvar_f x1) v1 ->
  v2 = v1.
Proof.
pose proof open_varref_wrt_varref_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_varref_wrt_varref_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_varref_rec_inj_open_dec_wrt_varref_rec_inj_mutual :
(forall T2 T1 x1 n1,
  x1 `notin` fv_typ T2 ->
  x1 `notin` fv_typ T1 ->
  open_typ_wrt_varref_rec n1 (var_termvar_f x1) T2 = open_typ_wrt_varref_rec n1 (var_termvar_f x1) T1 ->
  T2 = T1) /\
(forall dec2 dec1 x1 n1,
  x1 `notin` fv_dec dec2 ->
  x1 `notin` fv_dec dec1 ->
  open_dec_wrt_varref_rec n1 (var_termvar_f x1) dec2 = open_dec_wrt_varref_rec n1 (var_termvar_f x1) dec1 ->
  dec2 = dec1).
Proof.
apply_mutual_ind typ_dec_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_varref_rec_inj :
forall T2 T1 x1 n1,
  x1 `notin` fv_typ T2 ->
  x1 `notin` fv_typ T1 ->
  open_typ_wrt_varref_rec n1 (var_termvar_f x1) T2 = open_typ_wrt_varref_rec n1 (var_termvar_f x1) T1 ->
  T2 = T1.
Proof.
pose proof open_typ_wrt_varref_rec_inj_open_dec_wrt_varref_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_typ_wrt_varref_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dec_wrt_varref_rec_inj :
forall dec2 dec1 x1 n1,
  x1 `notin` fv_dec dec2 ->
  x1 `notin` fv_dec dec1 ->
  open_dec_wrt_varref_rec n1 (var_termvar_f x1) dec2 = open_dec_wrt_varref_rec n1 (var_termvar_f x1) dec1 ->
  dec2 = dec1.
Proof.
pose proof open_typ_wrt_varref_rec_inj_open_dec_wrt_varref_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_dec_wrt_varref_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_def_wrt_varref_rec_inj_open_defs_wrt_varref_rec_inj_open_val_wrt_varref_rec_inj_open_trm_wrt_varref_rec_inj_mutual :
(forall d2 d1 x1 n1,
  x1 `notin` fv_def d2 ->
  x1 `notin` fv_def d1 ->
  open_def_wrt_varref_rec n1 (var_termvar_f x1) d2 = open_def_wrt_varref_rec n1 (var_termvar_f x1) d1 ->
  d2 = d1) /\
(forall defs2 defs1 x1 n1,
  x1 `notin` fv_defs defs2 ->
  x1 `notin` fv_defs defs1 ->
  open_defs_wrt_varref_rec n1 (var_termvar_f x1) defs2 = open_defs_wrt_varref_rec n1 (var_termvar_f x1) defs1 ->
  defs2 = defs1) /\
(forall val2 val1 x1 n1,
  x1 `notin` fv_val val2 ->
  x1 `notin` fv_val val1 ->
  open_val_wrt_varref_rec n1 (var_termvar_f x1) val2 = open_val_wrt_varref_rec n1 (var_termvar_f x1) val1 ->
  val2 = val1) /\
(forall t2 t1 x1 n1,
  x1 `notin` fv_trm t2 ->
  x1 `notin` fv_trm t1 ->
  open_trm_wrt_varref_rec n1 (var_termvar_f x1) t2 = open_trm_wrt_varref_rec n1 (var_termvar_f x1) t1 ->
  t2 = t1).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_def_wrt_varref_rec_inj :
forall d2 d1 x1 n1,
  x1 `notin` fv_def d2 ->
  x1 `notin` fv_def d1 ->
  open_def_wrt_varref_rec n1 (var_termvar_f x1) d2 = open_def_wrt_varref_rec n1 (var_termvar_f x1) d1 ->
  d2 = d1.
Proof.
pose proof open_def_wrt_varref_rec_inj_open_defs_wrt_varref_rec_inj_open_val_wrt_varref_rec_inj_open_trm_wrt_varref_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_def_wrt_varref_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_defs_wrt_varref_rec_inj :
forall defs2 defs1 x1 n1,
  x1 `notin` fv_defs defs2 ->
  x1 `notin` fv_defs defs1 ->
  open_defs_wrt_varref_rec n1 (var_termvar_f x1) defs2 = open_defs_wrt_varref_rec n1 (var_termvar_f x1) defs1 ->
  defs2 = defs1.
Proof.
pose proof open_def_wrt_varref_rec_inj_open_defs_wrt_varref_rec_inj_open_val_wrt_varref_rec_inj_open_trm_wrt_varref_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_defs_wrt_varref_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_val_wrt_varref_rec_inj :
forall val2 val1 x1 n1,
  x1 `notin` fv_val val2 ->
  x1 `notin` fv_val val1 ->
  open_val_wrt_varref_rec n1 (var_termvar_f x1) val2 = open_val_wrt_varref_rec n1 (var_termvar_f x1) val1 ->
  val2 = val1.
Proof.
pose proof open_def_wrt_varref_rec_inj_open_defs_wrt_varref_rec_inj_open_val_wrt_varref_rec_inj_open_trm_wrt_varref_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_val_wrt_varref_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_trm_wrt_varref_rec_inj :
forall t2 t1 x1 n1,
  x1 `notin` fv_trm t2 ->
  x1 `notin` fv_trm t1 ->
  open_trm_wrt_varref_rec n1 (var_termvar_f x1) t2 = open_trm_wrt_varref_rec n1 (var_termvar_f x1) t1 ->
  t2 = t1.
Proof.
pose proof open_def_wrt_varref_rec_inj_open_defs_wrt_varref_rec_inj_open_val_wrt_varref_rec_inj_open_trm_wrt_varref_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_trm_wrt_varref_rec_inj : lngen.

(* end hide *)

Lemma open_varref_wrt_varref_inj :
forall v2 v1 x1,
  x1 `notin` fv_varref v2 ->
  x1 `notin` fv_varref v1 ->
  open_varref_wrt_varref v2 (var_termvar_f x1) = open_varref_wrt_varref v1 (var_termvar_f x1) ->
  v2 = v1.
Proof.
unfold open_varref_wrt_varref; eauto with lngen.
Qed.

Hint Immediate open_varref_wrt_varref_inj : lngen.

Lemma open_typ_wrt_varref_inj :
forall T2 T1 x1,
  x1 `notin` fv_typ T2 ->
  x1 `notin` fv_typ T1 ->
  open_typ_wrt_varref T2 (var_termvar_f x1) = open_typ_wrt_varref T1 (var_termvar_f x1) ->
  T2 = T1.
Proof.
unfold open_typ_wrt_varref; eauto with lngen.
Qed.

Hint Immediate open_typ_wrt_varref_inj : lngen.

Lemma open_dec_wrt_varref_inj :
forall dec2 dec1 x1,
  x1 `notin` fv_dec dec2 ->
  x1 `notin` fv_dec dec1 ->
  open_dec_wrt_varref dec2 (var_termvar_f x1) = open_dec_wrt_varref dec1 (var_termvar_f x1) ->
  dec2 = dec1.
Proof.
unfold open_dec_wrt_varref; eauto with lngen.
Qed.

Hint Immediate open_dec_wrt_varref_inj : lngen.

Lemma open_def_wrt_varref_inj :
forall d2 d1 x1,
  x1 `notin` fv_def d2 ->
  x1 `notin` fv_def d1 ->
  open_def_wrt_varref d2 (var_termvar_f x1) = open_def_wrt_varref d1 (var_termvar_f x1) ->
  d2 = d1.
Proof.
unfold open_def_wrt_varref; eauto with lngen.
Qed.

Hint Immediate open_def_wrt_varref_inj : lngen.

Lemma open_defs_wrt_varref_inj :
forall defs2 defs1 x1,
  x1 `notin` fv_defs defs2 ->
  x1 `notin` fv_defs defs1 ->
  open_defs_wrt_varref defs2 (var_termvar_f x1) = open_defs_wrt_varref defs1 (var_termvar_f x1) ->
  defs2 = defs1.
Proof.
unfold open_defs_wrt_varref; eauto with lngen.
Qed.

Hint Immediate open_defs_wrt_varref_inj : lngen.

Lemma open_val_wrt_varref_inj :
forall val2 val1 x1,
  x1 `notin` fv_val val2 ->
  x1 `notin` fv_val val1 ->
  open_val_wrt_varref val2 (var_termvar_f x1) = open_val_wrt_varref val1 (var_termvar_f x1) ->
  val2 = val1.
Proof.
unfold open_val_wrt_varref; eauto with lngen.
Qed.

Hint Immediate open_val_wrt_varref_inj : lngen.

Lemma open_trm_wrt_varref_inj :
forall t2 t1 x1,
  x1 `notin` fv_trm t2 ->
  x1 `notin` fv_trm t1 ->
  open_trm_wrt_varref t2 (var_termvar_f x1) = open_trm_wrt_varref t1 (var_termvar_f x1) ->
  t2 = t1.
Proof.
unfold open_trm_wrt_varref; eauto with lngen.
Qed.

Hint Immediate open_trm_wrt_varref_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_varref_wrt_varref_of_lc_varref_mutual :
(forall v1,
  lc_varref v1 ->
  degree_varref_wrt_varref 0 v1).
Proof.
apply_mutual_ind lc_varref_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_varref_wrt_varref_of_lc_varref :
forall v1,
  lc_varref v1 ->
  degree_varref_wrt_varref 0 v1.
Proof.
pose proof degree_varref_wrt_varref_of_lc_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_varref_wrt_varref_of_lc_varref : lngen.

(* begin hide *)

Lemma degree_typ_wrt_varref_of_lc_typ_degree_dec_wrt_varref_of_lc_dec_mutual :
(forall T1,
  lc_typ T1 ->
  degree_typ_wrt_varref 0 T1) /\
(forall dec1,
  lc_dec dec1 ->
  degree_dec_wrt_varref 0 dec1).
Proof.
apply_mutual_ind lc_typ_lc_dec_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_typ_wrt_varref_of_lc_typ :
forall T1,
  lc_typ T1 ->
  degree_typ_wrt_varref 0 T1.
Proof.
pose proof degree_typ_wrt_varref_of_lc_typ_degree_dec_wrt_varref_of_lc_dec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_varref_of_lc_typ : lngen.

Lemma degree_dec_wrt_varref_of_lc_dec :
forall dec1,
  lc_dec dec1 ->
  degree_dec_wrt_varref 0 dec1.
Proof.
pose proof degree_typ_wrt_varref_of_lc_typ_degree_dec_wrt_varref_of_lc_dec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dec_wrt_varref_of_lc_dec : lngen.

(* begin hide *)

Lemma degree_def_wrt_varref_of_lc_def_degree_defs_wrt_varref_of_lc_defs_degree_val_wrt_varref_of_lc_val_degree_trm_wrt_varref_of_lc_trm_mutual :
(forall d1,
  lc_def d1 ->
  degree_def_wrt_varref 0 d1) /\
(forall defs1,
  lc_defs defs1 ->
  degree_defs_wrt_varref 0 defs1) /\
(forall val1,
  lc_val val1 ->
  degree_val_wrt_varref 0 val1) /\
(forall t1,
  lc_trm t1 ->
  degree_trm_wrt_varref 0 t1).
Proof.
apply_mutual_ind lc_def_lc_defs_lc_val_lc_trm_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_def_wrt_varref_of_lc_def :
forall d1,
  lc_def d1 ->
  degree_def_wrt_varref 0 d1.
Proof.
pose proof degree_def_wrt_varref_of_lc_def_degree_defs_wrt_varref_of_lc_defs_degree_val_wrt_varref_of_lc_val_degree_trm_wrt_varref_of_lc_trm_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_def_wrt_varref_of_lc_def : lngen.

Lemma degree_defs_wrt_varref_of_lc_defs :
forall defs1,
  lc_defs defs1 ->
  degree_defs_wrt_varref 0 defs1.
Proof.
pose proof degree_def_wrt_varref_of_lc_def_degree_defs_wrt_varref_of_lc_defs_degree_val_wrt_varref_of_lc_val_degree_trm_wrt_varref_of_lc_trm_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_defs_wrt_varref_of_lc_defs : lngen.

Lemma degree_val_wrt_varref_of_lc_val :
forall val1,
  lc_val val1 ->
  degree_val_wrt_varref 0 val1.
Proof.
pose proof degree_def_wrt_varref_of_lc_def_degree_defs_wrt_varref_of_lc_defs_degree_val_wrt_varref_of_lc_val_degree_trm_wrt_varref_of_lc_trm_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_val_wrt_varref_of_lc_val : lngen.

Lemma degree_trm_wrt_varref_of_lc_trm :
forall t1,
  lc_trm t1 ->
  degree_trm_wrt_varref 0 t1.
Proof.
pose proof degree_def_wrt_varref_of_lc_def_degree_defs_wrt_varref_of_lc_defs_degree_val_wrt_varref_of_lc_val_degree_trm_wrt_varref_of_lc_trm_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_trm_wrt_varref_of_lc_trm : lngen.

(* begin hide *)

Lemma lc_varref_of_degree_size_mutual :
forall i1,
(forall v1,
  size_varref v1 = i1 ->
  degree_varref_wrt_varref 0 v1 ->
  lc_varref v1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind varref_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_varref_of_degree :
forall v1,
  degree_varref_wrt_varref 0 v1 ->
  lc_varref v1.
Proof.
intros v1; intros;
pose proof (lc_varref_of_degree_size_mutual (size_varref v1));
intuition eauto.
Qed.

Hint Resolve lc_varref_of_degree : lngen.

(* begin hide *)

Lemma lc_typ_of_degree_lc_dec_of_degree_size_mutual :
forall i1,
(forall T1,
  size_typ T1 = i1 ->
  degree_typ_wrt_varref 0 T1 ->
  lc_typ T1) /\
(forall dec1,
  size_dec dec1 = i1 ->
  degree_dec_wrt_varref 0 dec1 ->
  lc_dec dec1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_dec_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_degree :
forall T1,
  degree_typ_wrt_varref 0 T1 ->
  lc_typ T1.
Proof.
intros T1; intros;
pose proof (lc_typ_of_degree_lc_dec_of_degree_size_mutual (size_typ T1));
intuition eauto.
Qed.

Hint Resolve lc_typ_of_degree : lngen.

Lemma lc_dec_of_degree :
forall dec1,
  degree_dec_wrt_varref 0 dec1 ->
  lc_dec dec1.
Proof.
intros dec1; intros;
pose proof (lc_typ_of_degree_lc_dec_of_degree_size_mutual (size_dec dec1));
intuition eauto.
Qed.

Hint Resolve lc_dec_of_degree : lngen.

(* begin hide *)

Lemma lc_def_of_degree_lc_defs_of_degree_lc_val_of_degree_lc_trm_of_degree_size_mutual :
forall i1,
(forall d1,
  size_def d1 = i1 ->
  degree_def_wrt_varref 0 d1 ->
  lc_def d1) /\
(forall defs1,
  size_defs defs1 = i1 ->
  degree_defs_wrt_varref 0 defs1 ->
  lc_defs defs1) /\
(forall val1,
  size_val val1 = i1 ->
  degree_val_wrt_varref 0 val1 ->
  lc_val val1) /\
(forall t1,
  size_trm t1 = i1 ->
  degree_trm_wrt_varref 0 t1 ->
  lc_trm t1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind def_defs_val_trm_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_def_of_degree :
forall d1,
  degree_def_wrt_varref 0 d1 ->
  lc_def d1.
Proof.
intros d1; intros;
pose proof (lc_def_of_degree_lc_defs_of_degree_lc_val_of_degree_lc_trm_of_degree_size_mutual (size_def d1));
intuition eauto.
Qed.

Hint Resolve lc_def_of_degree : lngen.

Lemma lc_defs_of_degree :
forall defs1,
  degree_defs_wrt_varref 0 defs1 ->
  lc_defs defs1.
Proof.
intros defs1; intros;
pose proof (lc_def_of_degree_lc_defs_of_degree_lc_val_of_degree_lc_trm_of_degree_size_mutual (size_defs defs1));
intuition eauto.
Qed.

Hint Resolve lc_defs_of_degree : lngen.

Lemma lc_val_of_degree :
forall val1,
  degree_val_wrt_varref 0 val1 ->
  lc_val val1.
Proof.
intros val1; intros;
pose proof (lc_def_of_degree_lc_defs_of_degree_lc_val_of_degree_lc_trm_of_degree_size_mutual (size_val val1));
intuition eauto.
Qed.

Hint Resolve lc_val_of_degree : lngen.

Lemma lc_trm_of_degree :
forall t1,
  degree_trm_wrt_varref 0 t1 ->
  lc_trm t1.
Proof.
intros t1; intros;
pose proof (lc_def_of_degree_lc_defs_of_degree_lc_val_of_degree_lc_trm_of_degree_size_mutual (size_trm t1));
intuition eauto.
Qed.

Hint Resolve lc_trm_of_degree : lngen.

Ltac varref_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_varref_wrt_varref_of_lc_varref in J1; clear H
          end).

Ltac typ_dec_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_typ_wrt_varref_of_lc_typ in J1; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_dec_wrt_varref_of_lc_dec in J1; clear H
          end).

Ltac def_defs_val_trm_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_def_wrt_varref_of_lc_def in J1; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_defs_wrt_varref_of_lc_defs in J1; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_val_wrt_varref_of_lc_val in J1; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_trm_wrt_varref_of_lc_trm in J1; clear H
          end).

Lemma lc_typ_all_exists :
forall x1 T1 T2,
  lc_typ T1 ->
  lc_typ (open_typ_wrt_varref T2 (var_termvar_f x1)) ->
  lc_typ (typ_all T1 T2).
Proof.
intros; typ_dec_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_typ_bnd_exists :
forall x1 T1,
  lc_typ (open_typ_wrt_varref T1 (var_termvar_f x1)) ->
  lc_typ (typ_bnd T1).
Proof.
intros; typ_dec_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_val_new_exists :
forall x1 T1 defs1,
  lc_typ T1 ->
  lc_defs (open_defs_wrt_varref defs1 (var_termvar_f x1)) ->
  lc_val (val_new T1 defs1).
Proof.
intros; def_defs_val_trm_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_val_lambda_exists :
forall x1 T1 t1,
  lc_typ T1 ->
  lc_trm (open_trm_wrt_varref t1 (var_termvar_f x1)) ->
  lc_val (val_lambda T1 t1).
Proof.
intros; def_defs_val_trm_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_trm_let_exists :
forall x1 t1 t2,
  lc_trm t1 ->
  lc_trm (open_trm_wrt_varref t2 (var_termvar_f x1)) ->
  lc_trm (trm_let t1 t2).
Proof.
intros; def_defs_val_trm_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_typ (typ_all _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_typ_all_exists x1).

Hint Extern 1 (lc_typ (typ_bnd _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_typ_bnd_exists x1).

Hint Extern 1 (lc_val (val_new _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_val_new_exists x1).

Hint Extern 1 (lc_val (val_lambda _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_val_lambda_exists x1).

Hint Extern 1 (lc_trm (trm_let _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_trm_let_exists x1).

Lemma lc_body_varref_wrt_varref :
forall v1 v2,
  body_varref_wrt_varref v1 ->
  lc_varref v2 ->
  lc_varref (open_varref_wrt_varref v1 v2).
Proof.
unfold body_varref_wrt_varref;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
varref_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_varref_wrt_varref : lngen.

Lemma lc_body_typ_wrt_varref :
forall T1 v1,
  body_typ_wrt_varref T1 ->
  lc_varref v1 ->
  lc_typ (open_typ_wrt_varref T1 v1).
Proof.
unfold body_typ_wrt_varref;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
typ_dec_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_typ_wrt_varref : lngen.

Lemma lc_body_dec_wrt_varref :
forall dec1 v1,
  body_dec_wrt_varref dec1 ->
  lc_varref v1 ->
  lc_dec (open_dec_wrt_varref dec1 v1).
Proof.
unfold body_dec_wrt_varref;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
typ_dec_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_dec_wrt_varref : lngen.

Lemma lc_body_def_wrt_varref :
forall d1 v1,
  body_def_wrt_varref d1 ->
  lc_varref v1 ->
  lc_def (open_def_wrt_varref d1 v1).
Proof.
unfold body_def_wrt_varref;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
def_defs_val_trm_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_def_wrt_varref : lngen.

Lemma lc_body_defs_wrt_varref :
forall defs1 v1,
  body_defs_wrt_varref defs1 ->
  lc_varref v1 ->
  lc_defs (open_defs_wrt_varref defs1 v1).
Proof.
unfold body_defs_wrt_varref;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
def_defs_val_trm_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_defs_wrt_varref : lngen.

Lemma lc_body_val_wrt_varref :
forall val1 v1,
  body_val_wrt_varref val1 ->
  lc_varref v1 ->
  lc_val (open_val_wrt_varref val1 v1).
Proof.
unfold body_val_wrt_varref;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
def_defs_val_trm_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_val_wrt_varref : lngen.

Lemma lc_body_trm_wrt_varref :
forall t1 v1,
  body_trm_wrt_varref t1 ->
  lc_varref v1 ->
  lc_trm (open_trm_wrt_varref t1 v1).
Proof.
unfold body_trm_wrt_varref;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
def_defs_val_trm_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_trm_wrt_varref : lngen.

Lemma lc_body_typ_all_2 :
forall T1 T2,
  lc_typ (typ_all T1 T2) ->
  body_typ_wrt_varref T2.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_typ_all_2 : lngen.

Lemma lc_body_typ_bnd_1 :
forall T1,
  lc_typ (typ_bnd T1) ->
  body_typ_wrt_varref T1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_typ_bnd_1 : lngen.

Lemma lc_body_val_new_2 :
forall T1 defs1,
  lc_val (val_new T1 defs1) ->
  body_defs_wrt_varref defs1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_val_new_2 : lngen.

Lemma lc_body_val_lambda_2 :
forall T1 t1,
  lc_val (val_lambda T1 t1) ->
  body_trm_wrt_varref t1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_val_lambda_2 : lngen.

Lemma lc_body_trm_let_2 :
forall t1 t2,
  lc_trm (trm_let t1 t2) ->
  body_trm_wrt_varref t2.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_trm_let_2 : lngen.

(* begin hide *)

Lemma lc_varref_unique_mutual :
(forall v1 (proof2 proof3 : lc_varref v1), proof2 = proof3).
Proof.
apply_mutual_ind lc_varref_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_varref_unique :
forall v1 (proof2 proof3 : lc_varref v1), proof2 = proof3.
Proof.
pose proof lc_varref_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_varref_unique : lngen.

(* begin hide *)

Lemma lc_typ_unique_lc_dec_unique_mutual :
(forall T1 (proof2 proof3 : lc_typ T1), proof2 = proof3) /\
(forall dec1 (proof2 proof3 : lc_dec dec1), proof2 = proof3).
Proof.
apply_mutual_ind lc_typ_lc_dec_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_typ_unique :
forall T1 (proof2 proof3 : lc_typ T1), proof2 = proof3.
Proof.
pose proof lc_typ_unique_lc_dec_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_typ_unique : lngen.

Lemma lc_dec_unique :
forall dec1 (proof2 proof3 : lc_dec dec1), proof2 = proof3.
Proof.
pose proof lc_typ_unique_lc_dec_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_dec_unique : lngen.

(* begin hide *)

Lemma lc_def_unique_lc_defs_unique_lc_val_unique_lc_trm_unique_mutual :
(forall d1 (proof2 proof3 : lc_def d1), proof2 = proof3) /\
(forall defs1 (proof2 proof3 : lc_defs defs1), proof2 = proof3) /\
(forall val1 (proof2 proof3 : lc_val val1), proof2 = proof3) /\
(forall t1 (proof2 proof3 : lc_trm t1), proof2 = proof3).
Proof.
apply_mutual_ind lc_def_lc_defs_lc_val_lc_trm_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_def_unique :
forall d1 (proof2 proof3 : lc_def d1), proof2 = proof3.
Proof.
pose proof lc_def_unique_lc_defs_unique_lc_val_unique_lc_trm_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_def_unique : lngen.

Lemma lc_defs_unique :
forall defs1 (proof2 proof3 : lc_defs defs1), proof2 = proof3.
Proof.
pose proof lc_def_unique_lc_defs_unique_lc_val_unique_lc_trm_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_defs_unique : lngen.

Lemma lc_val_unique :
forall val1 (proof2 proof3 : lc_val val1), proof2 = proof3.
Proof.
pose proof lc_def_unique_lc_defs_unique_lc_val_unique_lc_trm_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_val_unique : lngen.

Lemma lc_trm_unique :
forall t1 (proof2 proof3 : lc_trm t1), proof2 = proof3.
Proof.
pose proof lc_def_unique_lc_defs_unique_lc_val_unique_lc_trm_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_trm_unique : lngen.

(* begin hide *)

Lemma lc_varref_of_lc_set_varref_mutual :
(forall v1, lc_set_varref v1 -> lc_varref v1).
Proof.
apply_mutual_ind lc_set_varref_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_varref_of_lc_set_varref :
forall v1, lc_set_varref v1 -> lc_varref v1.
Proof.
pose proof lc_varref_of_lc_set_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_varref_of_lc_set_varref : lngen.

(* begin hide *)

Lemma lc_typ_of_lc_set_typ_lc_dec_of_lc_set_dec_mutual :
(forall T1, lc_set_typ T1 -> lc_typ T1) /\
(forall dec1, lc_set_dec dec1 -> lc_dec dec1).
Proof.
apply_mutual_ind lc_set_typ_lc_set_dec_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_lc_set_typ :
forall T1, lc_set_typ T1 -> lc_typ T1.
Proof.
pose proof lc_typ_of_lc_set_typ_lc_dec_of_lc_set_dec_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_typ_of_lc_set_typ : lngen.

Lemma lc_dec_of_lc_set_dec :
forall dec1, lc_set_dec dec1 -> lc_dec dec1.
Proof.
pose proof lc_typ_of_lc_set_typ_lc_dec_of_lc_set_dec_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_dec_of_lc_set_dec : lngen.

(* begin hide *)

Lemma lc_def_of_lc_set_def_lc_defs_of_lc_set_defs_lc_val_of_lc_set_val_lc_trm_of_lc_set_trm_mutual :
(forall d1, lc_set_def d1 -> lc_def d1) /\
(forall defs1, lc_set_defs defs1 -> lc_defs defs1) /\
(forall val1, lc_set_val val1 -> lc_val val1) /\
(forall t1, lc_set_trm t1 -> lc_trm t1).
Proof.
apply_mutual_ind lc_set_def_lc_set_defs_lc_set_val_lc_set_trm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_def_of_lc_set_def :
forall d1, lc_set_def d1 -> lc_def d1.
Proof.
pose proof lc_def_of_lc_set_def_lc_defs_of_lc_set_defs_lc_val_of_lc_set_val_lc_trm_of_lc_set_trm_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_def_of_lc_set_def : lngen.

Lemma lc_defs_of_lc_set_defs :
forall defs1, lc_set_defs defs1 -> lc_defs defs1.
Proof.
pose proof lc_def_of_lc_set_def_lc_defs_of_lc_set_defs_lc_val_of_lc_set_val_lc_trm_of_lc_set_trm_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_defs_of_lc_set_defs : lngen.

Lemma lc_val_of_lc_set_val :
forall val1, lc_set_val val1 -> lc_val val1.
Proof.
pose proof lc_def_of_lc_set_def_lc_defs_of_lc_set_defs_lc_val_of_lc_set_val_lc_trm_of_lc_set_trm_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_val_of_lc_set_val : lngen.

Lemma lc_trm_of_lc_set_trm :
forall t1, lc_set_trm t1 -> lc_trm t1.
Proof.
pose proof lc_def_of_lc_set_def_lc_defs_of_lc_set_defs_lc_val_of_lc_set_val_lc_trm_of_lc_set_trm_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_trm_of_lc_set_trm : lngen.

(* begin hide *)

Lemma lc_set_varref_of_lc_varref_size_mutual :
forall i1,
(forall v1,
  size_varref v1 = i1 ->
  lc_varref v1 ->
  lc_set_varref v1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind varref_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_varref_of_lc_varref];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_varref_of_lc_varref :
forall v1,
  lc_varref v1 ->
  lc_set_varref v1.
Proof.
intros v1; intros;
pose proof (lc_set_varref_of_lc_varref_size_mutual (size_varref v1));
intuition eauto.
Qed.

Hint Resolve lc_set_varref_of_lc_varref : lngen.

(* begin hide *)

Lemma lc_set_typ_of_lc_typ_lc_set_dec_of_lc_dec_size_mutual :
forall i1,
(forall T1,
  size_typ T1 = i1 ->
  lc_typ T1 ->
  lc_set_typ T1) *
(forall dec1,
  size_dec dec1 = i1 ->
  lc_dec dec1 ->
  lc_set_dec dec1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_dec_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_dec_of_lc_dec
 | apply lc_set_varref_of_lc_varref
 | apply lc_set_typ_of_lc_typ
 | apply lc_set_dec_of_lc_dec
 | apply lc_set_varref_of_lc_varref];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_typ_of_lc_typ :
forall T1,
  lc_typ T1 ->
  lc_set_typ T1.
Proof.
intros T1; intros;
pose proof (lc_set_typ_of_lc_typ_lc_set_dec_of_lc_dec_size_mutual (size_typ T1));
intuition eauto.
Qed.

Hint Resolve lc_set_typ_of_lc_typ : lngen.

Lemma lc_set_dec_of_lc_dec :
forall dec1,
  lc_dec dec1 ->
  lc_set_dec dec1.
Proof.
intros dec1; intros;
pose proof (lc_set_typ_of_lc_typ_lc_set_dec_of_lc_dec_size_mutual (size_dec dec1));
intuition eauto.
Qed.

Hint Resolve lc_set_dec_of_lc_dec : lngen.

(* begin hide *)

Lemma lc_set_def_of_lc_def_lc_set_defs_of_lc_defs_lc_set_val_of_lc_val_lc_set_trm_of_lc_trm_size_mutual :
forall i1,
(forall d1,
  size_def d1 = i1 ->
  lc_def d1 ->
  lc_set_def d1) *
(forall defs1,
  size_defs defs1 = i1 ->
  lc_defs defs1 ->
  lc_set_defs defs1) *
(forall val1,
  size_val val1 = i1 ->
  lc_val val1 ->
  lc_set_val val1) *
(forall t1,
  size_trm t1 = i1 ->
  lc_trm t1 ->
  lc_set_trm t1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind def_defs_val_trm_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_def_of_lc_def
 | apply lc_set_dec_of_lc_dec
 | apply lc_set_defs_of_lc_defs
 | apply lc_set_trm_of_lc_trm
 | apply lc_set_varref_of_lc_varref
 | apply lc_set_val_of_lc_val
 | apply lc_set_typ_of_lc_typ
 | apply lc_set_def_of_lc_def
 | apply lc_set_dec_of_lc_dec
 | apply lc_set_defs_of_lc_defs
 | apply lc_set_trm_of_lc_trm
 | apply lc_set_varref_of_lc_varref
 | apply lc_set_val_of_lc_val
 | apply lc_set_typ_of_lc_typ
 | apply lc_set_def_of_lc_def
 | apply lc_set_dec_of_lc_dec
 | apply lc_set_defs_of_lc_defs
 | apply lc_set_trm_of_lc_trm
 | apply lc_set_varref_of_lc_varref
 | apply lc_set_val_of_lc_val
 | apply lc_set_typ_of_lc_typ
 | apply lc_set_def_of_lc_def
 | apply lc_set_dec_of_lc_dec
 | apply lc_set_defs_of_lc_defs
 | apply lc_set_trm_of_lc_trm
 | apply lc_set_varref_of_lc_varref
 | apply lc_set_val_of_lc_val];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_def_of_lc_def :
forall d1,
  lc_def d1 ->
  lc_set_def d1.
Proof.
intros d1; intros;
pose proof (lc_set_def_of_lc_def_lc_set_defs_of_lc_defs_lc_set_val_of_lc_val_lc_set_trm_of_lc_trm_size_mutual (size_def d1));
intuition eauto.
Qed.

Hint Resolve lc_set_def_of_lc_def : lngen.

Lemma lc_set_defs_of_lc_defs :
forall defs1,
  lc_defs defs1 ->
  lc_set_defs defs1.
Proof.
intros defs1; intros;
pose proof (lc_set_def_of_lc_def_lc_set_defs_of_lc_defs_lc_set_val_of_lc_val_lc_set_trm_of_lc_trm_size_mutual (size_defs defs1));
intuition eauto.
Qed.

Hint Resolve lc_set_defs_of_lc_defs : lngen.

Lemma lc_set_val_of_lc_val :
forall val1,
  lc_val val1 ->
  lc_set_val val1.
Proof.
intros val1; intros;
pose proof (lc_set_def_of_lc_def_lc_set_defs_of_lc_defs_lc_set_val_of_lc_val_lc_set_trm_of_lc_trm_size_mutual (size_val val1));
intuition eauto.
Qed.

Hint Resolve lc_set_val_of_lc_val : lngen.

Lemma lc_set_trm_of_lc_trm :
forall t1,
  lc_trm t1 ->
  lc_set_trm t1.
Proof.
intros t1; intros;
pose proof (lc_set_def_of_lc_def_lc_set_defs_of_lc_defs_lc_set_val_of_lc_val_lc_set_trm_of_lc_trm_size_mutual (size_trm t1));
intuition eauto.
Qed.

Hint Resolve lc_set_trm_of_lc_trm : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_varref_wrt_varref_rec_degree_varref_wrt_varref_mutual :
(forall v1 x1 n1,
  degree_varref_wrt_varref n1 v1 ->
  x1 `notin` fv_varref v1 ->
  close_varref_wrt_varref_rec n1 x1 v1 = v1).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_varref_wrt_varref_rec_degree_varref_wrt_varref :
forall v1 x1 n1,
  degree_varref_wrt_varref n1 v1 ->
  x1 `notin` fv_varref v1 ->
  close_varref_wrt_varref_rec n1 x1 v1 = v1.
Proof.
pose proof close_varref_wrt_varref_rec_degree_varref_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve close_varref_wrt_varref_rec_degree_varref_wrt_varref : lngen.
Hint Rewrite close_varref_wrt_varref_rec_degree_varref_wrt_varref using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_varref_rec_degree_typ_wrt_varref_close_dec_wrt_varref_rec_degree_dec_wrt_varref_mutual :
(forall T1 x1 n1,
  degree_typ_wrt_varref n1 T1 ->
  x1 `notin` fv_typ T1 ->
  close_typ_wrt_varref_rec n1 x1 T1 = T1) /\
(forall dec1 x1 n1,
  degree_dec_wrt_varref n1 dec1 ->
  x1 `notin` fv_dec dec1 ->
  close_dec_wrt_varref_rec n1 x1 dec1 = dec1).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_varref_rec_degree_typ_wrt_varref :
forall T1 x1 n1,
  degree_typ_wrt_varref n1 T1 ->
  x1 `notin` fv_typ T1 ->
  close_typ_wrt_varref_rec n1 x1 T1 = T1.
Proof.
pose proof close_typ_wrt_varref_rec_degree_typ_wrt_varref_close_dec_wrt_varref_rec_degree_dec_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve close_typ_wrt_varref_rec_degree_typ_wrt_varref : lngen.
Hint Rewrite close_typ_wrt_varref_rec_degree_typ_wrt_varref using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dec_wrt_varref_rec_degree_dec_wrt_varref :
forall dec1 x1 n1,
  degree_dec_wrt_varref n1 dec1 ->
  x1 `notin` fv_dec dec1 ->
  close_dec_wrt_varref_rec n1 x1 dec1 = dec1.
Proof.
pose proof close_typ_wrt_varref_rec_degree_typ_wrt_varref_close_dec_wrt_varref_rec_degree_dec_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve close_dec_wrt_varref_rec_degree_dec_wrt_varref : lngen.
Hint Rewrite close_dec_wrt_varref_rec_degree_dec_wrt_varref using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_def_wrt_varref_rec_degree_def_wrt_varref_close_defs_wrt_varref_rec_degree_defs_wrt_varref_close_val_wrt_varref_rec_degree_val_wrt_varref_close_trm_wrt_varref_rec_degree_trm_wrt_varref_mutual :
(forall d1 x1 n1,
  degree_def_wrt_varref n1 d1 ->
  x1 `notin` fv_def d1 ->
  close_def_wrt_varref_rec n1 x1 d1 = d1) /\
(forall defs1 x1 n1,
  degree_defs_wrt_varref n1 defs1 ->
  x1 `notin` fv_defs defs1 ->
  close_defs_wrt_varref_rec n1 x1 defs1 = defs1) /\
(forall val1 x1 n1,
  degree_val_wrt_varref n1 val1 ->
  x1 `notin` fv_val val1 ->
  close_val_wrt_varref_rec n1 x1 val1 = val1) /\
(forall t1 x1 n1,
  degree_trm_wrt_varref n1 t1 ->
  x1 `notin` fv_trm t1 ->
  close_trm_wrt_varref_rec n1 x1 t1 = t1).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_def_wrt_varref_rec_degree_def_wrt_varref :
forall d1 x1 n1,
  degree_def_wrt_varref n1 d1 ->
  x1 `notin` fv_def d1 ->
  close_def_wrt_varref_rec n1 x1 d1 = d1.
Proof.
pose proof close_def_wrt_varref_rec_degree_def_wrt_varref_close_defs_wrt_varref_rec_degree_defs_wrt_varref_close_val_wrt_varref_rec_degree_val_wrt_varref_close_trm_wrt_varref_rec_degree_trm_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve close_def_wrt_varref_rec_degree_def_wrt_varref : lngen.
Hint Rewrite close_def_wrt_varref_rec_degree_def_wrt_varref using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_defs_wrt_varref_rec_degree_defs_wrt_varref :
forall defs1 x1 n1,
  degree_defs_wrt_varref n1 defs1 ->
  x1 `notin` fv_defs defs1 ->
  close_defs_wrt_varref_rec n1 x1 defs1 = defs1.
Proof.
pose proof close_def_wrt_varref_rec_degree_def_wrt_varref_close_defs_wrt_varref_rec_degree_defs_wrt_varref_close_val_wrt_varref_rec_degree_val_wrt_varref_close_trm_wrt_varref_rec_degree_trm_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve close_defs_wrt_varref_rec_degree_defs_wrt_varref : lngen.
Hint Rewrite close_defs_wrt_varref_rec_degree_defs_wrt_varref using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_val_wrt_varref_rec_degree_val_wrt_varref :
forall val1 x1 n1,
  degree_val_wrt_varref n1 val1 ->
  x1 `notin` fv_val val1 ->
  close_val_wrt_varref_rec n1 x1 val1 = val1.
Proof.
pose proof close_def_wrt_varref_rec_degree_def_wrt_varref_close_defs_wrt_varref_rec_degree_defs_wrt_varref_close_val_wrt_varref_rec_degree_val_wrt_varref_close_trm_wrt_varref_rec_degree_trm_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve close_val_wrt_varref_rec_degree_val_wrt_varref : lngen.
Hint Rewrite close_val_wrt_varref_rec_degree_val_wrt_varref using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_trm_wrt_varref_rec_degree_trm_wrt_varref :
forall t1 x1 n1,
  degree_trm_wrt_varref n1 t1 ->
  x1 `notin` fv_trm t1 ->
  close_trm_wrt_varref_rec n1 x1 t1 = t1.
Proof.
pose proof close_def_wrt_varref_rec_degree_def_wrt_varref_close_defs_wrt_varref_rec_degree_defs_wrt_varref_close_val_wrt_varref_rec_degree_val_wrt_varref_close_trm_wrt_varref_rec_degree_trm_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve close_trm_wrt_varref_rec_degree_trm_wrt_varref : lngen.
Hint Rewrite close_trm_wrt_varref_rec_degree_trm_wrt_varref using solve [auto] : lngen.

(* end hide *)

Lemma close_varref_wrt_varref_lc_varref :
forall v1 x1,
  lc_varref v1 ->
  x1 `notin` fv_varref v1 ->
  close_varref_wrt_varref x1 v1 = v1.
Proof.
unfold close_varref_wrt_varref; default_simp.
Qed.

Hint Resolve close_varref_wrt_varref_lc_varref : lngen.
Hint Rewrite close_varref_wrt_varref_lc_varref using solve [auto] : lngen.

Lemma close_typ_wrt_varref_lc_typ :
forall T1 x1,
  lc_typ T1 ->
  x1 `notin` fv_typ T1 ->
  close_typ_wrt_varref x1 T1 = T1.
Proof.
unfold close_typ_wrt_varref; default_simp.
Qed.

Hint Resolve close_typ_wrt_varref_lc_typ : lngen.
Hint Rewrite close_typ_wrt_varref_lc_typ using solve [auto] : lngen.

Lemma close_dec_wrt_varref_lc_dec :
forall dec1 x1,
  lc_dec dec1 ->
  x1 `notin` fv_dec dec1 ->
  close_dec_wrt_varref x1 dec1 = dec1.
Proof.
unfold close_dec_wrt_varref; default_simp.
Qed.

Hint Resolve close_dec_wrt_varref_lc_dec : lngen.
Hint Rewrite close_dec_wrt_varref_lc_dec using solve [auto] : lngen.

Lemma close_def_wrt_varref_lc_def :
forall d1 x1,
  lc_def d1 ->
  x1 `notin` fv_def d1 ->
  close_def_wrt_varref x1 d1 = d1.
Proof.
unfold close_def_wrt_varref; default_simp.
Qed.

Hint Resolve close_def_wrt_varref_lc_def : lngen.
Hint Rewrite close_def_wrt_varref_lc_def using solve [auto] : lngen.

Lemma close_defs_wrt_varref_lc_defs :
forall defs1 x1,
  lc_defs defs1 ->
  x1 `notin` fv_defs defs1 ->
  close_defs_wrt_varref x1 defs1 = defs1.
Proof.
unfold close_defs_wrt_varref; default_simp.
Qed.

Hint Resolve close_defs_wrt_varref_lc_defs : lngen.
Hint Rewrite close_defs_wrt_varref_lc_defs using solve [auto] : lngen.

Lemma close_val_wrt_varref_lc_val :
forall val1 x1,
  lc_val val1 ->
  x1 `notin` fv_val val1 ->
  close_val_wrt_varref x1 val1 = val1.
Proof.
unfold close_val_wrt_varref; default_simp.
Qed.

Hint Resolve close_val_wrt_varref_lc_val : lngen.
Hint Rewrite close_val_wrt_varref_lc_val using solve [auto] : lngen.

Lemma close_trm_wrt_varref_lc_trm :
forall t1 x1,
  lc_trm t1 ->
  x1 `notin` fv_trm t1 ->
  close_trm_wrt_varref x1 t1 = t1.
Proof.
unfold close_trm_wrt_varref; default_simp.
Qed.

Hint Resolve close_trm_wrt_varref_lc_trm : lngen.
Hint Rewrite close_trm_wrt_varref_lc_trm using solve [auto] : lngen.

(* begin hide *)

Lemma open_varref_wrt_varref_rec_degree_varref_wrt_varref_mutual :
(forall v2 v1 n1,
  degree_varref_wrt_varref n1 v2 ->
  open_varref_wrt_varref_rec n1 v1 v2 = v2).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_varref_wrt_varref_rec_degree_varref_wrt_varref :
forall v2 v1 n1,
  degree_varref_wrt_varref n1 v2 ->
  open_varref_wrt_varref_rec n1 v1 v2 = v2.
Proof.
pose proof open_varref_wrt_varref_rec_degree_varref_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve open_varref_wrt_varref_rec_degree_varref_wrt_varref : lngen.
Hint Rewrite open_varref_wrt_varref_rec_degree_varref_wrt_varref using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_varref_rec_degree_typ_wrt_varref_open_dec_wrt_varref_rec_degree_dec_wrt_varref_mutual :
(forall T1 v1 n1,
  degree_typ_wrt_varref n1 T1 ->
  open_typ_wrt_varref_rec n1 v1 T1 = T1) /\
(forall dec1 v1 n1,
  degree_dec_wrt_varref n1 dec1 ->
  open_dec_wrt_varref_rec n1 v1 dec1 = dec1).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_varref_rec_degree_typ_wrt_varref :
forall T1 v1 n1,
  degree_typ_wrt_varref n1 T1 ->
  open_typ_wrt_varref_rec n1 v1 T1 = T1.
Proof.
pose proof open_typ_wrt_varref_rec_degree_typ_wrt_varref_open_dec_wrt_varref_rec_degree_dec_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve open_typ_wrt_varref_rec_degree_typ_wrt_varref : lngen.
Hint Rewrite open_typ_wrt_varref_rec_degree_typ_wrt_varref using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dec_wrt_varref_rec_degree_dec_wrt_varref :
forall dec1 v1 n1,
  degree_dec_wrt_varref n1 dec1 ->
  open_dec_wrt_varref_rec n1 v1 dec1 = dec1.
Proof.
pose proof open_typ_wrt_varref_rec_degree_typ_wrt_varref_open_dec_wrt_varref_rec_degree_dec_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve open_dec_wrt_varref_rec_degree_dec_wrt_varref : lngen.
Hint Rewrite open_dec_wrt_varref_rec_degree_dec_wrt_varref using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_def_wrt_varref_rec_degree_def_wrt_varref_open_defs_wrt_varref_rec_degree_defs_wrt_varref_open_val_wrt_varref_rec_degree_val_wrt_varref_open_trm_wrt_varref_rec_degree_trm_wrt_varref_mutual :
(forall d1 v1 n1,
  degree_def_wrt_varref n1 d1 ->
  open_def_wrt_varref_rec n1 v1 d1 = d1) /\
(forall defs1 v1 n1,
  degree_defs_wrt_varref n1 defs1 ->
  open_defs_wrt_varref_rec n1 v1 defs1 = defs1) /\
(forall val1 v1 n1,
  degree_val_wrt_varref n1 val1 ->
  open_val_wrt_varref_rec n1 v1 val1 = val1) /\
(forall t1 v1 n1,
  degree_trm_wrt_varref n1 t1 ->
  open_trm_wrt_varref_rec n1 v1 t1 = t1).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_def_wrt_varref_rec_degree_def_wrt_varref :
forall d1 v1 n1,
  degree_def_wrt_varref n1 d1 ->
  open_def_wrt_varref_rec n1 v1 d1 = d1.
Proof.
pose proof open_def_wrt_varref_rec_degree_def_wrt_varref_open_defs_wrt_varref_rec_degree_defs_wrt_varref_open_val_wrt_varref_rec_degree_val_wrt_varref_open_trm_wrt_varref_rec_degree_trm_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve open_def_wrt_varref_rec_degree_def_wrt_varref : lngen.
Hint Rewrite open_def_wrt_varref_rec_degree_def_wrt_varref using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_defs_wrt_varref_rec_degree_defs_wrt_varref :
forall defs1 v1 n1,
  degree_defs_wrt_varref n1 defs1 ->
  open_defs_wrt_varref_rec n1 v1 defs1 = defs1.
Proof.
pose proof open_def_wrt_varref_rec_degree_def_wrt_varref_open_defs_wrt_varref_rec_degree_defs_wrt_varref_open_val_wrt_varref_rec_degree_val_wrt_varref_open_trm_wrt_varref_rec_degree_trm_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve open_defs_wrt_varref_rec_degree_defs_wrt_varref : lngen.
Hint Rewrite open_defs_wrt_varref_rec_degree_defs_wrt_varref using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_val_wrt_varref_rec_degree_val_wrt_varref :
forall val1 v1 n1,
  degree_val_wrt_varref n1 val1 ->
  open_val_wrt_varref_rec n1 v1 val1 = val1.
Proof.
pose proof open_def_wrt_varref_rec_degree_def_wrt_varref_open_defs_wrt_varref_rec_degree_defs_wrt_varref_open_val_wrt_varref_rec_degree_val_wrt_varref_open_trm_wrt_varref_rec_degree_trm_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve open_val_wrt_varref_rec_degree_val_wrt_varref : lngen.
Hint Rewrite open_val_wrt_varref_rec_degree_val_wrt_varref using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_trm_wrt_varref_rec_degree_trm_wrt_varref :
forall t1 v1 n1,
  degree_trm_wrt_varref n1 t1 ->
  open_trm_wrt_varref_rec n1 v1 t1 = t1.
Proof.
pose proof open_def_wrt_varref_rec_degree_def_wrt_varref_open_defs_wrt_varref_rec_degree_defs_wrt_varref_open_val_wrt_varref_rec_degree_val_wrt_varref_open_trm_wrt_varref_rec_degree_trm_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve open_trm_wrt_varref_rec_degree_trm_wrt_varref : lngen.
Hint Rewrite open_trm_wrt_varref_rec_degree_trm_wrt_varref using solve [auto] : lngen.

(* end hide *)

Lemma open_varref_wrt_varref_lc_varref :
forall v2 v1,
  lc_varref v2 ->
  open_varref_wrt_varref v2 v1 = v2.
Proof.
unfold open_varref_wrt_varref; default_simp.
Qed.

Hint Resolve open_varref_wrt_varref_lc_varref : lngen.
Hint Rewrite open_varref_wrt_varref_lc_varref using solve [auto] : lngen.

Lemma open_typ_wrt_varref_lc_typ :
forall T1 v1,
  lc_typ T1 ->
  open_typ_wrt_varref T1 v1 = T1.
Proof.
unfold open_typ_wrt_varref; default_simp.
Qed.

Hint Resolve open_typ_wrt_varref_lc_typ : lngen.
Hint Rewrite open_typ_wrt_varref_lc_typ using solve [auto] : lngen.

Lemma open_dec_wrt_varref_lc_dec :
forall dec1 v1,
  lc_dec dec1 ->
  open_dec_wrt_varref dec1 v1 = dec1.
Proof.
unfold open_dec_wrt_varref; default_simp.
Qed.

Hint Resolve open_dec_wrt_varref_lc_dec : lngen.
Hint Rewrite open_dec_wrt_varref_lc_dec using solve [auto] : lngen.

Lemma open_def_wrt_varref_lc_def :
forall d1 v1,
  lc_def d1 ->
  open_def_wrt_varref d1 v1 = d1.
Proof.
unfold open_def_wrt_varref; default_simp.
Qed.

Hint Resolve open_def_wrt_varref_lc_def : lngen.
Hint Rewrite open_def_wrt_varref_lc_def using solve [auto] : lngen.

Lemma open_defs_wrt_varref_lc_defs :
forall defs1 v1,
  lc_defs defs1 ->
  open_defs_wrt_varref defs1 v1 = defs1.
Proof.
unfold open_defs_wrt_varref; default_simp.
Qed.

Hint Resolve open_defs_wrt_varref_lc_defs : lngen.
Hint Rewrite open_defs_wrt_varref_lc_defs using solve [auto] : lngen.

Lemma open_val_wrt_varref_lc_val :
forall val1 v1,
  lc_val val1 ->
  open_val_wrt_varref val1 v1 = val1.
Proof.
unfold open_val_wrt_varref; default_simp.
Qed.

Hint Resolve open_val_wrt_varref_lc_val : lngen.
Hint Rewrite open_val_wrt_varref_lc_val using solve [auto] : lngen.

Lemma open_trm_wrt_varref_lc_trm :
forall t1 v1,
  lc_trm t1 ->
  open_trm_wrt_varref t1 v1 = t1.
Proof.
unfold open_trm_wrt_varref; default_simp.
Qed.

Hint Resolve open_trm_wrt_varref_lc_trm : lngen.
Hint Rewrite open_trm_wrt_varref_lc_trm using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_varref_close_varref_wrt_varref_rec_mutual :
(forall v1 x1 n1,
  fv_varref (close_varref_wrt_varref_rec n1 x1 v1) [=] remove x1 (fv_varref v1)).
Proof.
apply_mutual_ind varref_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_varref_close_varref_wrt_varref_rec :
forall v1 x1 n1,
  fv_varref (close_varref_wrt_varref_rec n1 x1 v1) [=] remove x1 (fv_varref v1).
Proof.
pose proof fv_varref_close_varref_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_varref_close_varref_wrt_varref_rec : lngen.
Hint Rewrite fv_varref_close_varref_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_typ_close_typ_wrt_varref_rec_fv_dec_close_dec_wrt_varref_rec_mutual :
(forall T1 x1 n1,
  fv_typ (close_typ_wrt_varref_rec n1 x1 T1) [=] remove x1 (fv_typ T1)) /\
(forall dec1 x1 n1,
  fv_dec (close_dec_wrt_varref_rec n1 x1 dec1) [=] remove x1 (fv_dec dec1)).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_typ_close_typ_wrt_varref_rec :
forall T1 x1 n1,
  fv_typ (close_typ_wrt_varref_rec n1 x1 T1) [=] remove x1 (fv_typ T1).
Proof.
pose proof fv_typ_close_typ_wrt_varref_rec_fv_dec_close_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_close_typ_wrt_varref_rec : lngen.
Hint Rewrite fv_typ_close_typ_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_dec_close_dec_wrt_varref_rec :
forall dec1 x1 n1,
  fv_dec (close_dec_wrt_varref_rec n1 x1 dec1) [=] remove x1 (fv_dec dec1).
Proof.
pose proof fv_typ_close_typ_wrt_varref_rec_fv_dec_close_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dec_close_dec_wrt_varref_rec : lngen.
Hint Rewrite fv_dec_close_dec_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_def_close_def_wrt_varref_rec_fv_defs_close_defs_wrt_varref_rec_fv_val_close_val_wrt_varref_rec_fv_trm_close_trm_wrt_varref_rec_mutual :
(forall d1 x1 n1,
  fv_def (close_def_wrt_varref_rec n1 x1 d1) [=] remove x1 (fv_def d1)) /\
(forall defs1 x1 n1,
  fv_defs (close_defs_wrt_varref_rec n1 x1 defs1) [=] remove x1 (fv_defs defs1)) /\
(forall val1 x1 n1,
  fv_val (close_val_wrt_varref_rec n1 x1 val1) [=] remove x1 (fv_val val1)) /\
(forall t1 x1 n1,
  fv_trm (close_trm_wrt_varref_rec n1 x1 t1) [=] remove x1 (fv_trm t1)).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_def_close_def_wrt_varref_rec :
forall d1 x1 n1,
  fv_def (close_def_wrt_varref_rec n1 x1 d1) [=] remove x1 (fv_def d1).
Proof.
pose proof fv_def_close_def_wrt_varref_rec_fv_defs_close_defs_wrt_varref_rec_fv_val_close_val_wrt_varref_rec_fv_trm_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_def_close_def_wrt_varref_rec : lngen.
Hint Rewrite fv_def_close_def_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_defs_close_defs_wrt_varref_rec :
forall defs1 x1 n1,
  fv_defs (close_defs_wrt_varref_rec n1 x1 defs1) [=] remove x1 (fv_defs defs1).
Proof.
pose proof fv_def_close_def_wrt_varref_rec_fv_defs_close_defs_wrt_varref_rec_fv_val_close_val_wrt_varref_rec_fv_trm_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_defs_close_defs_wrt_varref_rec : lngen.
Hint Rewrite fv_defs_close_defs_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_val_close_val_wrt_varref_rec :
forall val1 x1 n1,
  fv_val (close_val_wrt_varref_rec n1 x1 val1) [=] remove x1 (fv_val val1).
Proof.
pose proof fv_def_close_def_wrt_varref_rec_fv_defs_close_defs_wrt_varref_rec_fv_val_close_val_wrt_varref_rec_fv_trm_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_val_close_val_wrt_varref_rec : lngen.
Hint Rewrite fv_val_close_val_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_trm_close_trm_wrt_varref_rec :
forall t1 x1 n1,
  fv_trm (close_trm_wrt_varref_rec n1 x1 t1) [=] remove x1 (fv_trm t1).
Proof.
pose proof fv_def_close_def_wrt_varref_rec_fv_defs_close_defs_wrt_varref_rec_fv_val_close_val_wrt_varref_rec_fv_trm_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_trm_close_trm_wrt_varref_rec : lngen.
Hint Rewrite fv_trm_close_trm_wrt_varref_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_varref_close_varref_wrt_varref :
forall v1 x1,
  fv_varref (close_varref_wrt_varref x1 v1) [=] remove x1 (fv_varref v1).
Proof.
unfold close_varref_wrt_varref; default_simp.
Qed.

Hint Resolve fv_varref_close_varref_wrt_varref : lngen.
Hint Rewrite fv_varref_close_varref_wrt_varref using solve [auto] : lngen.

Lemma fv_typ_close_typ_wrt_varref :
forall T1 x1,
  fv_typ (close_typ_wrt_varref x1 T1) [=] remove x1 (fv_typ T1).
Proof.
unfold close_typ_wrt_varref; default_simp.
Qed.

Hint Resolve fv_typ_close_typ_wrt_varref : lngen.
Hint Rewrite fv_typ_close_typ_wrt_varref using solve [auto] : lngen.

Lemma fv_dec_close_dec_wrt_varref :
forall dec1 x1,
  fv_dec (close_dec_wrt_varref x1 dec1) [=] remove x1 (fv_dec dec1).
Proof.
unfold close_dec_wrt_varref; default_simp.
Qed.

Hint Resolve fv_dec_close_dec_wrt_varref : lngen.
Hint Rewrite fv_dec_close_dec_wrt_varref using solve [auto] : lngen.

Lemma fv_def_close_def_wrt_varref :
forall d1 x1,
  fv_def (close_def_wrt_varref x1 d1) [=] remove x1 (fv_def d1).
Proof.
unfold close_def_wrt_varref; default_simp.
Qed.

Hint Resolve fv_def_close_def_wrt_varref : lngen.
Hint Rewrite fv_def_close_def_wrt_varref using solve [auto] : lngen.

Lemma fv_defs_close_defs_wrt_varref :
forall defs1 x1,
  fv_defs (close_defs_wrt_varref x1 defs1) [=] remove x1 (fv_defs defs1).
Proof.
unfold close_defs_wrt_varref; default_simp.
Qed.

Hint Resolve fv_defs_close_defs_wrt_varref : lngen.
Hint Rewrite fv_defs_close_defs_wrt_varref using solve [auto] : lngen.

Lemma fv_val_close_val_wrt_varref :
forall val1 x1,
  fv_val (close_val_wrt_varref x1 val1) [=] remove x1 (fv_val val1).
Proof.
unfold close_val_wrt_varref; default_simp.
Qed.

Hint Resolve fv_val_close_val_wrt_varref : lngen.
Hint Rewrite fv_val_close_val_wrt_varref using solve [auto] : lngen.

Lemma fv_trm_close_trm_wrt_varref :
forall t1 x1,
  fv_trm (close_trm_wrt_varref x1 t1) [=] remove x1 (fv_trm t1).
Proof.
unfold close_trm_wrt_varref; default_simp.
Qed.

Hint Resolve fv_trm_close_trm_wrt_varref : lngen.
Hint Rewrite fv_trm_close_trm_wrt_varref using solve [auto] : lngen.

(* begin hide *)

Lemma fv_varref_open_varref_wrt_varref_rec_lower_mutual :
(forall v1 v2 n1,
  fv_varref v1 [<=] fv_varref (open_varref_wrt_varref_rec n1 v2 v1)).
Proof.
apply_mutual_ind varref_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_varref_open_varref_wrt_varref_rec_lower :
forall v1 v2 n1,
  fv_varref v1 [<=] fv_varref (open_varref_wrt_varref_rec n1 v2 v1).
Proof.
pose proof fv_varref_open_varref_wrt_varref_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_varref_open_varref_wrt_varref_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_typ_open_typ_wrt_varref_rec_lower_fv_dec_open_dec_wrt_varref_rec_lower_mutual :
(forall T1 v1 n1,
  fv_typ T1 [<=] fv_typ (open_typ_wrt_varref_rec n1 v1 T1)) /\
(forall dec1 v1 n1,
  fv_dec dec1 [<=] fv_dec (open_dec_wrt_varref_rec n1 v1 dec1)).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_typ_open_typ_wrt_varref_rec_lower :
forall T1 v1 n1,
  fv_typ T1 [<=] fv_typ (open_typ_wrt_varref_rec n1 v1 T1).
Proof.
pose proof fv_typ_open_typ_wrt_varref_rec_lower_fv_dec_open_dec_wrt_varref_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_open_typ_wrt_varref_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_dec_open_dec_wrt_varref_rec_lower :
forall dec1 v1 n1,
  fv_dec dec1 [<=] fv_dec (open_dec_wrt_varref_rec n1 v1 dec1).
Proof.
pose proof fv_typ_open_typ_wrt_varref_rec_lower_fv_dec_open_dec_wrt_varref_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dec_open_dec_wrt_varref_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_def_open_def_wrt_varref_rec_lower_fv_defs_open_defs_wrt_varref_rec_lower_fv_val_open_val_wrt_varref_rec_lower_fv_trm_open_trm_wrt_varref_rec_lower_mutual :
(forall d1 v1 n1,
  fv_def d1 [<=] fv_def (open_def_wrt_varref_rec n1 v1 d1)) /\
(forall defs1 v1 n1,
  fv_defs defs1 [<=] fv_defs (open_defs_wrt_varref_rec n1 v1 defs1)) /\
(forall val1 v1 n1,
  fv_val val1 [<=] fv_val (open_val_wrt_varref_rec n1 v1 val1)) /\
(forall t1 v1 n1,
  fv_trm t1 [<=] fv_trm (open_trm_wrt_varref_rec n1 v1 t1)).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_def_open_def_wrt_varref_rec_lower :
forall d1 v1 n1,
  fv_def d1 [<=] fv_def (open_def_wrt_varref_rec n1 v1 d1).
Proof.
pose proof fv_def_open_def_wrt_varref_rec_lower_fv_defs_open_defs_wrt_varref_rec_lower_fv_val_open_val_wrt_varref_rec_lower_fv_trm_open_trm_wrt_varref_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_def_open_def_wrt_varref_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_defs_open_defs_wrt_varref_rec_lower :
forall defs1 v1 n1,
  fv_defs defs1 [<=] fv_defs (open_defs_wrt_varref_rec n1 v1 defs1).
Proof.
pose proof fv_def_open_def_wrt_varref_rec_lower_fv_defs_open_defs_wrt_varref_rec_lower_fv_val_open_val_wrt_varref_rec_lower_fv_trm_open_trm_wrt_varref_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_defs_open_defs_wrt_varref_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_val_open_val_wrt_varref_rec_lower :
forall val1 v1 n1,
  fv_val val1 [<=] fv_val (open_val_wrt_varref_rec n1 v1 val1).
Proof.
pose proof fv_def_open_def_wrt_varref_rec_lower_fv_defs_open_defs_wrt_varref_rec_lower_fv_val_open_val_wrt_varref_rec_lower_fv_trm_open_trm_wrt_varref_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_val_open_val_wrt_varref_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_trm_open_trm_wrt_varref_rec_lower :
forall t1 v1 n1,
  fv_trm t1 [<=] fv_trm (open_trm_wrt_varref_rec n1 v1 t1).
Proof.
pose proof fv_def_open_def_wrt_varref_rec_lower_fv_defs_open_defs_wrt_varref_rec_lower_fv_val_open_val_wrt_varref_rec_lower_fv_trm_open_trm_wrt_varref_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_trm_open_trm_wrt_varref_rec_lower : lngen.

(* end hide *)

Lemma fv_varref_open_varref_wrt_varref_lower :
forall v1 v2,
  fv_varref v1 [<=] fv_varref (open_varref_wrt_varref v1 v2).
Proof.
unfold open_varref_wrt_varref; default_simp.
Qed.

Hint Resolve fv_varref_open_varref_wrt_varref_lower : lngen.

Lemma fv_typ_open_typ_wrt_varref_lower :
forall T1 v1,
  fv_typ T1 [<=] fv_typ (open_typ_wrt_varref T1 v1).
Proof.
unfold open_typ_wrt_varref; default_simp.
Qed.

Hint Resolve fv_typ_open_typ_wrt_varref_lower : lngen.

Lemma fv_dec_open_dec_wrt_varref_lower :
forall dec1 v1,
  fv_dec dec1 [<=] fv_dec (open_dec_wrt_varref dec1 v1).
Proof.
unfold open_dec_wrt_varref; default_simp.
Qed.

Hint Resolve fv_dec_open_dec_wrt_varref_lower : lngen.

Lemma fv_def_open_def_wrt_varref_lower :
forall d1 v1,
  fv_def d1 [<=] fv_def (open_def_wrt_varref d1 v1).
Proof.
unfold open_def_wrt_varref; default_simp.
Qed.

Hint Resolve fv_def_open_def_wrt_varref_lower : lngen.

Lemma fv_defs_open_defs_wrt_varref_lower :
forall defs1 v1,
  fv_defs defs1 [<=] fv_defs (open_defs_wrt_varref defs1 v1).
Proof.
unfold open_defs_wrt_varref; default_simp.
Qed.

Hint Resolve fv_defs_open_defs_wrt_varref_lower : lngen.

Lemma fv_val_open_val_wrt_varref_lower :
forall val1 v1,
  fv_val val1 [<=] fv_val (open_val_wrt_varref val1 v1).
Proof.
unfold open_val_wrt_varref; default_simp.
Qed.

Hint Resolve fv_val_open_val_wrt_varref_lower : lngen.

Lemma fv_trm_open_trm_wrt_varref_lower :
forall t1 v1,
  fv_trm t1 [<=] fv_trm (open_trm_wrt_varref t1 v1).
Proof.
unfold open_trm_wrt_varref; default_simp.
Qed.

Hint Resolve fv_trm_open_trm_wrt_varref_lower : lngen.

(* begin hide *)

Lemma fv_varref_open_varref_wrt_varref_rec_upper_mutual :
(forall v1 v2 n1,
  fv_varref (open_varref_wrt_varref_rec n1 v2 v1) [<=] fv_varref v2 `union` fv_varref v1).
Proof.
apply_mutual_ind varref_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_varref_open_varref_wrt_varref_rec_upper :
forall v1 v2 n1,
  fv_varref (open_varref_wrt_varref_rec n1 v2 v1) [<=] fv_varref v2 `union` fv_varref v1.
Proof.
pose proof fv_varref_open_varref_wrt_varref_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_varref_open_varref_wrt_varref_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_typ_open_typ_wrt_varref_rec_upper_fv_dec_open_dec_wrt_varref_rec_upper_mutual :
(forall T1 v1 n1,
  fv_typ (open_typ_wrt_varref_rec n1 v1 T1) [<=] fv_varref v1 `union` fv_typ T1) /\
(forall dec1 v1 n1,
  fv_dec (open_dec_wrt_varref_rec n1 v1 dec1) [<=] fv_varref v1 `union` fv_dec dec1).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_typ_open_typ_wrt_varref_rec_upper :
forall T1 v1 n1,
  fv_typ (open_typ_wrt_varref_rec n1 v1 T1) [<=] fv_varref v1 `union` fv_typ T1.
Proof.
pose proof fv_typ_open_typ_wrt_varref_rec_upper_fv_dec_open_dec_wrt_varref_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_open_typ_wrt_varref_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_dec_open_dec_wrt_varref_rec_upper :
forall dec1 v1 n1,
  fv_dec (open_dec_wrt_varref_rec n1 v1 dec1) [<=] fv_varref v1 `union` fv_dec dec1.
Proof.
pose proof fv_typ_open_typ_wrt_varref_rec_upper_fv_dec_open_dec_wrt_varref_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dec_open_dec_wrt_varref_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_def_open_def_wrt_varref_rec_upper_fv_defs_open_defs_wrt_varref_rec_upper_fv_val_open_val_wrt_varref_rec_upper_fv_trm_open_trm_wrt_varref_rec_upper_mutual :
(forall d1 v1 n1,
  fv_def (open_def_wrt_varref_rec n1 v1 d1) [<=] fv_varref v1 `union` fv_def d1) /\
(forall defs1 v1 n1,
  fv_defs (open_defs_wrt_varref_rec n1 v1 defs1) [<=] fv_varref v1 `union` fv_defs defs1) /\
(forall val1 v1 n1,
  fv_val (open_val_wrt_varref_rec n1 v1 val1) [<=] fv_varref v1 `union` fv_val val1) /\
(forall t1 v1 n1,
  fv_trm (open_trm_wrt_varref_rec n1 v1 t1) [<=] fv_varref v1 `union` fv_trm t1).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_def_open_def_wrt_varref_rec_upper :
forall d1 v1 n1,
  fv_def (open_def_wrt_varref_rec n1 v1 d1) [<=] fv_varref v1 `union` fv_def d1.
Proof.
pose proof fv_def_open_def_wrt_varref_rec_upper_fv_defs_open_defs_wrt_varref_rec_upper_fv_val_open_val_wrt_varref_rec_upper_fv_trm_open_trm_wrt_varref_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_def_open_def_wrt_varref_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_defs_open_defs_wrt_varref_rec_upper :
forall defs1 v1 n1,
  fv_defs (open_defs_wrt_varref_rec n1 v1 defs1) [<=] fv_varref v1 `union` fv_defs defs1.
Proof.
pose proof fv_def_open_def_wrt_varref_rec_upper_fv_defs_open_defs_wrt_varref_rec_upper_fv_val_open_val_wrt_varref_rec_upper_fv_trm_open_trm_wrt_varref_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_defs_open_defs_wrt_varref_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_val_open_val_wrt_varref_rec_upper :
forall val1 v1 n1,
  fv_val (open_val_wrt_varref_rec n1 v1 val1) [<=] fv_varref v1 `union` fv_val val1.
Proof.
pose proof fv_def_open_def_wrt_varref_rec_upper_fv_defs_open_defs_wrt_varref_rec_upper_fv_val_open_val_wrt_varref_rec_upper_fv_trm_open_trm_wrt_varref_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_val_open_val_wrt_varref_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_trm_open_trm_wrt_varref_rec_upper :
forall t1 v1 n1,
  fv_trm (open_trm_wrt_varref_rec n1 v1 t1) [<=] fv_varref v1 `union` fv_trm t1.
Proof.
pose proof fv_def_open_def_wrt_varref_rec_upper_fv_defs_open_defs_wrt_varref_rec_upper_fv_val_open_val_wrt_varref_rec_upper_fv_trm_open_trm_wrt_varref_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_trm_open_trm_wrt_varref_rec_upper : lngen.

(* end hide *)

Lemma fv_varref_open_varref_wrt_varref_upper :
forall v1 v2,
  fv_varref (open_varref_wrt_varref v1 v2) [<=] fv_varref v2 `union` fv_varref v1.
Proof.
unfold open_varref_wrt_varref; default_simp.
Qed.

Hint Resolve fv_varref_open_varref_wrt_varref_upper : lngen.

Lemma fv_typ_open_typ_wrt_varref_upper :
forall T1 v1,
  fv_typ (open_typ_wrt_varref T1 v1) [<=] fv_varref v1 `union` fv_typ T1.
Proof.
unfold open_typ_wrt_varref; default_simp.
Qed.

Hint Resolve fv_typ_open_typ_wrt_varref_upper : lngen.

Lemma fv_dec_open_dec_wrt_varref_upper :
forall dec1 v1,
  fv_dec (open_dec_wrt_varref dec1 v1) [<=] fv_varref v1 `union` fv_dec dec1.
Proof.
unfold open_dec_wrt_varref; default_simp.
Qed.

Hint Resolve fv_dec_open_dec_wrt_varref_upper : lngen.

Lemma fv_def_open_def_wrt_varref_upper :
forall d1 v1,
  fv_def (open_def_wrt_varref d1 v1) [<=] fv_varref v1 `union` fv_def d1.
Proof.
unfold open_def_wrt_varref; default_simp.
Qed.

Hint Resolve fv_def_open_def_wrt_varref_upper : lngen.

Lemma fv_defs_open_defs_wrt_varref_upper :
forall defs1 v1,
  fv_defs (open_defs_wrt_varref defs1 v1) [<=] fv_varref v1 `union` fv_defs defs1.
Proof.
unfold open_defs_wrt_varref; default_simp.
Qed.

Hint Resolve fv_defs_open_defs_wrt_varref_upper : lngen.

Lemma fv_val_open_val_wrt_varref_upper :
forall val1 v1,
  fv_val (open_val_wrt_varref val1 v1) [<=] fv_varref v1 `union` fv_val val1.
Proof.
unfold open_val_wrt_varref; default_simp.
Qed.

Hint Resolve fv_val_open_val_wrt_varref_upper : lngen.

Lemma fv_trm_open_trm_wrt_varref_upper :
forall t1 v1,
  fv_trm (open_trm_wrt_varref t1 v1) [<=] fv_varref v1 `union` fv_trm t1.
Proof.
unfold open_trm_wrt_varref; default_simp.
Qed.

Hint Resolve fv_trm_open_trm_wrt_varref_upper : lngen.

(* begin hide *)

Lemma fv_varref_subst_varref_fresh_mutual :
(forall v1 v2 x1,
  x1 `notin` fv_varref v1 ->
  fv_varref (subst_varref v2 x1 v1) [=] fv_varref v1).
Proof.
apply_mutual_ind varref_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_varref_subst_varref_fresh :
forall v1 v2 x1,
  x1 `notin` fv_varref v1 ->
  fv_varref (subst_varref v2 x1 v1) [=] fv_varref v1.
Proof.
pose proof fv_varref_subst_varref_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_varref_subst_varref_fresh : lngen.
Hint Rewrite fv_varref_subst_varref_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_typ_subst_typ_fresh_fv_dec_subst_dec_fresh_mutual :
(forall T1 v1 x1,
  x1 `notin` fv_typ T1 ->
  fv_typ (subst_typ v1 x1 T1) [=] fv_typ T1) /\
(forall dec1 v1 x1,
  x1 `notin` fv_dec dec1 ->
  fv_dec (subst_dec v1 x1 dec1) [=] fv_dec dec1).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_subst_typ_fresh :
forall T1 v1 x1,
  x1 `notin` fv_typ T1 ->
  fv_typ (subst_typ v1 x1 T1) [=] fv_typ T1.
Proof.
pose proof fv_typ_subst_typ_fresh_fv_dec_subst_dec_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_subst_typ_fresh : lngen.
Hint Rewrite fv_typ_subst_typ_fresh using solve [auto] : lngen.

Lemma fv_dec_subst_dec_fresh :
forall dec1 v1 x1,
  x1 `notin` fv_dec dec1 ->
  fv_dec (subst_dec v1 x1 dec1) [=] fv_dec dec1.
Proof.
pose proof fv_typ_subst_typ_fresh_fv_dec_subst_dec_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dec_subst_dec_fresh : lngen.
Hint Rewrite fv_dec_subst_dec_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_def_subst_def_fresh_fv_defs_subst_defs_fresh_fv_val_subst_val_fresh_fv_trm_subst_trm_fresh_mutual :
(forall d1 v1 x1,
  x1 `notin` fv_def d1 ->
  fv_def (subst_def v1 x1 d1) [=] fv_def d1) /\
(forall defs1 v1 x1,
  x1 `notin` fv_defs defs1 ->
  fv_defs (subst_defs v1 x1 defs1) [=] fv_defs defs1) /\
(forall val1 v1 x1,
  x1 `notin` fv_val val1 ->
  fv_val (subst_val v1 x1 val1) [=] fv_val val1) /\
(forall t1 v1 x1,
  x1 `notin` fv_trm t1 ->
  fv_trm (subst_trm v1 x1 t1) [=] fv_trm t1).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_def_subst_def_fresh :
forall d1 v1 x1,
  x1 `notin` fv_def d1 ->
  fv_def (subst_def v1 x1 d1) [=] fv_def d1.
Proof.
pose proof fv_def_subst_def_fresh_fv_defs_subst_defs_fresh_fv_val_subst_val_fresh_fv_trm_subst_trm_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_def_subst_def_fresh : lngen.
Hint Rewrite fv_def_subst_def_fresh using solve [auto] : lngen.

Lemma fv_defs_subst_defs_fresh :
forall defs1 v1 x1,
  x1 `notin` fv_defs defs1 ->
  fv_defs (subst_defs v1 x1 defs1) [=] fv_defs defs1.
Proof.
pose proof fv_def_subst_def_fresh_fv_defs_subst_defs_fresh_fv_val_subst_val_fresh_fv_trm_subst_trm_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_defs_subst_defs_fresh : lngen.
Hint Rewrite fv_defs_subst_defs_fresh using solve [auto] : lngen.

Lemma fv_val_subst_val_fresh :
forall val1 v1 x1,
  x1 `notin` fv_val val1 ->
  fv_val (subst_val v1 x1 val1) [=] fv_val val1.
Proof.
pose proof fv_def_subst_def_fresh_fv_defs_subst_defs_fresh_fv_val_subst_val_fresh_fv_trm_subst_trm_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_val_subst_val_fresh : lngen.
Hint Rewrite fv_val_subst_val_fresh using solve [auto] : lngen.

Lemma fv_trm_subst_trm_fresh :
forall t1 v1 x1,
  x1 `notin` fv_trm t1 ->
  fv_trm (subst_trm v1 x1 t1) [=] fv_trm t1.
Proof.
pose proof fv_def_subst_def_fresh_fv_defs_subst_defs_fresh_fv_val_subst_val_fresh_fv_trm_subst_trm_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_trm_subst_trm_fresh : lngen.
Hint Rewrite fv_trm_subst_trm_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_varref_subst_varref_lower_mutual :
(forall v1 v2 x1,
  remove x1 (fv_varref v1) [<=] fv_varref (subst_varref v2 x1 v1)).
Proof.
apply_mutual_ind varref_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_varref_subst_varref_lower :
forall v1 v2 x1,
  remove x1 (fv_varref v1) [<=] fv_varref (subst_varref v2 x1 v1).
Proof.
pose proof fv_varref_subst_varref_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_varref_subst_varref_lower : lngen.

(* begin hide *)

Lemma fv_typ_subst_typ_lower_fv_dec_subst_dec_lower_mutual :
(forall T1 v1 x1,
  remove x1 (fv_typ T1) [<=] fv_typ (subst_typ v1 x1 T1)) /\
(forall dec1 v1 x1,
  remove x1 (fv_dec dec1) [<=] fv_dec (subst_dec v1 x1 dec1)).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_subst_typ_lower :
forall T1 v1 x1,
  remove x1 (fv_typ T1) [<=] fv_typ (subst_typ v1 x1 T1).
Proof.
pose proof fv_typ_subst_typ_lower_fv_dec_subst_dec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_subst_typ_lower : lngen.

Lemma fv_dec_subst_dec_lower :
forall dec1 v1 x1,
  remove x1 (fv_dec dec1) [<=] fv_dec (subst_dec v1 x1 dec1).
Proof.
pose proof fv_typ_subst_typ_lower_fv_dec_subst_dec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dec_subst_dec_lower : lngen.

(* begin hide *)

Lemma fv_def_subst_def_lower_fv_defs_subst_defs_lower_fv_val_subst_val_lower_fv_trm_subst_trm_lower_mutual :
(forall d1 v1 x1,
  remove x1 (fv_def d1) [<=] fv_def (subst_def v1 x1 d1)) /\
(forall defs1 v1 x1,
  remove x1 (fv_defs defs1) [<=] fv_defs (subst_defs v1 x1 defs1)) /\
(forall val1 v1 x1,
  remove x1 (fv_val val1) [<=] fv_val (subst_val v1 x1 val1)) /\
(forall t1 v1 x1,
  remove x1 (fv_trm t1) [<=] fv_trm (subst_trm v1 x1 t1)).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_def_subst_def_lower :
forall d1 v1 x1,
  remove x1 (fv_def d1) [<=] fv_def (subst_def v1 x1 d1).
Proof.
pose proof fv_def_subst_def_lower_fv_defs_subst_defs_lower_fv_val_subst_val_lower_fv_trm_subst_trm_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_def_subst_def_lower : lngen.

Lemma fv_defs_subst_defs_lower :
forall defs1 v1 x1,
  remove x1 (fv_defs defs1) [<=] fv_defs (subst_defs v1 x1 defs1).
Proof.
pose proof fv_def_subst_def_lower_fv_defs_subst_defs_lower_fv_val_subst_val_lower_fv_trm_subst_trm_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_defs_subst_defs_lower : lngen.

Lemma fv_val_subst_val_lower :
forall val1 v1 x1,
  remove x1 (fv_val val1) [<=] fv_val (subst_val v1 x1 val1).
Proof.
pose proof fv_def_subst_def_lower_fv_defs_subst_defs_lower_fv_val_subst_val_lower_fv_trm_subst_trm_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_val_subst_val_lower : lngen.

Lemma fv_trm_subst_trm_lower :
forall t1 v1 x1,
  remove x1 (fv_trm t1) [<=] fv_trm (subst_trm v1 x1 t1).
Proof.
pose proof fv_def_subst_def_lower_fv_defs_subst_defs_lower_fv_val_subst_val_lower_fv_trm_subst_trm_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_trm_subst_trm_lower : lngen.

(* begin hide *)

Lemma fv_varref_subst_varref_notin_mutual :
(forall v1 v2 x1 x2,
  x2 `notin` fv_varref v1 ->
  x2 `notin` fv_varref v2 ->
  x2 `notin` fv_varref (subst_varref v2 x1 v1)).
Proof.
apply_mutual_ind varref_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_varref_subst_varref_notin :
forall v1 v2 x1 x2,
  x2 `notin` fv_varref v1 ->
  x2 `notin` fv_varref v2 ->
  x2 `notin` fv_varref (subst_varref v2 x1 v1).
Proof.
pose proof fv_varref_subst_varref_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_varref_subst_varref_notin : lngen.

(* begin hide *)

Lemma fv_typ_subst_typ_notin_fv_dec_subst_dec_notin_mutual :
(forall T1 v1 x1 x2,
  x2 `notin` fv_typ T1 ->
  x2 `notin` fv_varref v1 ->
  x2 `notin` fv_typ (subst_typ v1 x1 T1)) /\
(forall dec1 v1 x1 x2,
  x2 `notin` fv_dec dec1 ->
  x2 `notin` fv_varref v1 ->
  x2 `notin` fv_dec (subst_dec v1 x1 dec1)).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_subst_typ_notin :
forall T1 v1 x1 x2,
  x2 `notin` fv_typ T1 ->
  x2 `notin` fv_varref v1 ->
  x2 `notin` fv_typ (subst_typ v1 x1 T1).
Proof.
pose proof fv_typ_subst_typ_notin_fv_dec_subst_dec_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_subst_typ_notin : lngen.

Lemma fv_dec_subst_dec_notin :
forall dec1 v1 x1 x2,
  x2 `notin` fv_dec dec1 ->
  x2 `notin` fv_varref v1 ->
  x2 `notin` fv_dec (subst_dec v1 x1 dec1).
Proof.
pose proof fv_typ_subst_typ_notin_fv_dec_subst_dec_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dec_subst_dec_notin : lngen.

(* begin hide *)

Lemma fv_def_subst_def_notin_fv_defs_subst_defs_notin_fv_val_subst_val_notin_fv_trm_subst_trm_notin_mutual :
(forall d1 v1 x1 x2,
  x2 `notin` fv_def d1 ->
  x2 `notin` fv_varref v1 ->
  x2 `notin` fv_def (subst_def v1 x1 d1)) /\
(forall defs1 v1 x1 x2,
  x2 `notin` fv_defs defs1 ->
  x2 `notin` fv_varref v1 ->
  x2 `notin` fv_defs (subst_defs v1 x1 defs1)) /\
(forall val1 v1 x1 x2,
  x2 `notin` fv_val val1 ->
  x2 `notin` fv_varref v1 ->
  x2 `notin` fv_val (subst_val v1 x1 val1)) /\
(forall t1 v1 x1 x2,
  x2 `notin` fv_trm t1 ->
  x2 `notin` fv_varref v1 ->
  x2 `notin` fv_trm (subst_trm v1 x1 t1)).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_def_subst_def_notin :
forall d1 v1 x1 x2,
  x2 `notin` fv_def d1 ->
  x2 `notin` fv_varref v1 ->
  x2 `notin` fv_def (subst_def v1 x1 d1).
Proof.
pose proof fv_def_subst_def_notin_fv_defs_subst_defs_notin_fv_val_subst_val_notin_fv_trm_subst_trm_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_def_subst_def_notin : lngen.

Lemma fv_defs_subst_defs_notin :
forall defs1 v1 x1 x2,
  x2 `notin` fv_defs defs1 ->
  x2 `notin` fv_varref v1 ->
  x2 `notin` fv_defs (subst_defs v1 x1 defs1).
Proof.
pose proof fv_def_subst_def_notin_fv_defs_subst_defs_notin_fv_val_subst_val_notin_fv_trm_subst_trm_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_defs_subst_defs_notin : lngen.

Lemma fv_val_subst_val_notin :
forall val1 v1 x1 x2,
  x2 `notin` fv_val val1 ->
  x2 `notin` fv_varref v1 ->
  x2 `notin` fv_val (subst_val v1 x1 val1).
Proof.
pose proof fv_def_subst_def_notin_fv_defs_subst_defs_notin_fv_val_subst_val_notin_fv_trm_subst_trm_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_val_subst_val_notin : lngen.

Lemma fv_trm_subst_trm_notin :
forall t1 v1 x1 x2,
  x2 `notin` fv_trm t1 ->
  x2 `notin` fv_varref v1 ->
  x2 `notin` fv_trm (subst_trm v1 x1 t1).
Proof.
pose proof fv_def_subst_def_notin_fv_defs_subst_defs_notin_fv_val_subst_val_notin_fv_trm_subst_trm_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_trm_subst_trm_notin : lngen.

(* begin hide *)

Lemma fv_varref_subst_varref_upper_mutual :
(forall v1 v2 x1,
  fv_varref (subst_varref v2 x1 v1) [<=] fv_varref v2 `union` remove x1 (fv_varref v1)).
Proof.
apply_mutual_ind varref_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_varref_subst_varref_upper :
forall v1 v2 x1,
  fv_varref (subst_varref v2 x1 v1) [<=] fv_varref v2 `union` remove x1 (fv_varref v1).
Proof.
pose proof fv_varref_subst_varref_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_varref_subst_varref_upper : lngen.

(* begin hide *)

Lemma fv_typ_subst_typ_upper_fv_dec_subst_dec_upper_mutual :
(forall T1 v1 x1,
  fv_typ (subst_typ v1 x1 T1) [<=] fv_varref v1 `union` remove x1 (fv_typ T1)) /\
(forall dec1 v1 x1,
  fv_dec (subst_dec v1 x1 dec1) [<=] fv_varref v1 `union` remove x1 (fv_dec dec1)).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_typ_subst_typ_upper :
forall T1 v1 x1,
  fv_typ (subst_typ v1 x1 T1) [<=] fv_varref v1 `union` remove x1 (fv_typ T1).
Proof.
pose proof fv_typ_subst_typ_upper_fv_dec_subst_dec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_typ_subst_typ_upper : lngen.

Lemma fv_dec_subst_dec_upper :
forall dec1 v1 x1,
  fv_dec (subst_dec v1 x1 dec1) [<=] fv_varref v1 `union` remove x1 (fv_dec dec1).
Proof.
pose proof fv_typ_subst_typ_upper_fv_dec_subst_dec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dec_subst_dec_upper : lngen.

(* begin hide *)

Lemma fv_def_subst_def_upper_fv_defs_subst_defs_upper_fv_val_subst_val_upper_fv_trm_subst_trm_upper_mutual :
(forall d1 v1 x1,
  fv_def (subst_def v1 x1 d1) [<=] fv_varref v1 `union` remove x1 (fv_def d1)) /\
(forall defs1 v1 x1,
  fv_defs (subst_defs v1 x1 defs1) [<=] fv_varref v1 `union` remove x1 (fv_defs defs1)) /\
(forall val1 v1 x1,
  fv_val (subst_val v1 x1 val1) [<=] fv_varref v1 `union` remove x1 (fv_val val1)) /\
(forall t1 v1 x1,
  fv_trm (subst_trm v1 x1 t1) [<=] fv_varref v1 `union` remove x1 (fv_trm t1)).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_def_subst_def_upper :
forall d1 v1 x1,
  fv_def (subst_def v1 x1 d1) [<=] fv_varref v1 `union` remove x1 (fv_def d1).
Proof.
pose proof fv_def_subst_def_upper_fv_defs_subst_defs_upper_fv_val_subst_val_upper_fv_trm_subst_trm_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_def_subst_def_upper : lngen.

Lemma fv_defs_subst_defs_upper :
forall defs1 v1 x1,
  fv_defs (subst_defs v1 x1 defs1) [<=] fv_varref v1 `union` remove x1 (fv_defs defs1).
Proof.
pose proof fv_def_subst_def_upper_fv_defs_subst_defs_upper_fv_val_subst_val_upper_fv_trm_subst_trm_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_defs_subst_defs_upper : lngen.

Lemma fv_val_subst_val_upper :
forall val1 v1 x1,
  fv_val (subst_val v1 x1 val1) [<=] fv_varref v1 `union` remove x1 (fv_val val1).
Proof.
pose proof fv_def_subst_def_upper_fv_defs_subst_defs_upper_fv_val_subst_val_upper_fv_trm_subst_trm_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_val_subst_val_upper : lngen.

Lemma fv_trm_subst_trm_upper :
forall t1 v1 x1,
  fv_trm (subst_trm v1 x1 t1) [<=] fv_varref v1 `union` remove x1 (fv_trm t1).
Proof.
pose proof fv_def_subst_def_upper_fv_defs_subst_defs_upper_fv_val_subst_val_upper_fv_trm_subst_trm_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_trm_subst_trm_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_varref_close_varref_wrt_varref_rec_mutual :
(forall v2 v1 x1 x2 n1,
  degree_varref_wrt_varref n1 v1 ->
  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_varref v1 x1 (close_varref_wrt_varref_rec n1 x2 v2) = close_varref_wrt_varref_rec n1 x2 (subst_varref v1 x1 v2)).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_varref_close_varref_wrt_varref_rec :
forall v2 v1 x1 x2 n1,
  degree_varref_wrt_varref n1 v1 ->
  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_varref v1 x1 (close_varref_wrt_varref_rec n1 x2 v2) = close_varref_wrt_varref_rec n1 x2 (subst_varref v1 x1 v2).
Proof.
pose proof subst_varref_close_varref_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_varref_close_varref_wrt_varref_rec : lngen.

(* begin hide *)

Lemma subst_typ_close_typ_wrt_varref_rec_subst_dec_close_dec_wrt_varref_rec_mutual :
(forall T1 v1 x1 x2 n1,
  degree_varref_wrt_varref n1 v1 ->
  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_typ v1 x1 (close_typ_wrt_varref_rec n1 x2 T1) = close_typ_wrt_varref_rec n1 x2 (subst_typ v1 x1 T1)) /\
(forall dec1 v1 x1 x2 n1,
  degree_varref_wrt_varref n1 v1 ->
  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_dec v1 x1 (close_dec_wrt_varref_rec n1 x2 dec1) = close_dec_wrt_varref_rec n1 x2 (subst_dec v1 x1 dec1)).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_close_typ_wrt_varref_rec :
forall T1 v1 x1 x2 n1,
  degree_varref_wrt_varref n1 v1 ->
  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_typ v1 x1 (close_typ_wrt_varref_rec n1 x2 T1) = close_typ_wrt_varref_rec n1 x2 (subst_typ v1 x1 T1).
Proof.
pose proof subst_typ_close_typ_wrt_varref_rec_subst_dec_close_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_close_typ_wrt_varref_rec : lngen.

Lemma subst_dec_close_dec_wrt_varref_rec :
forall dec1 v1 x1 x2 n1,
  degree_varref_wrt_varref n1 v1 ->
  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_dec v1 x1 (close_dec_wrt_varref_rec n1 x2 dec1) = close_dec_wrt_varref_rec n1 x2 (subst_dec v1 x1 dec1).
Proof.
pose proof subst_typ_close_typ_wrt_varref_rec_subst_dec_close_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dec_close_dec_wrt_varref_rec : lngen.

(* begin hide *)

Lemma subst_def_close_def_wrt_varref_rec_subst_defs_close_defs_wrt_varref_rec_subst_val_close_val_wrt_varref_rec_subst_trm_close_trm_wrt_varref_rec_mutual :
(forall d1 v1 x1 x2 n1,
  degree_varref_wrt_varref n1 v1 ->
  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_def v1 x1 (close_def_wrt_varref_rec n1 x2 d1) = close_def_wrt_varref_rec n1 x2 (subst_def v1 x1 d1)) /\
(forall defs1 v1 x1 x2 n1,
  degree_varref_wrt_varref n1 v1 ->
  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_defs v1 x1 (close_defs_wrt_varref_rec n1 x2 defs1) = close_defs_wrt_varref_rec n1 x2 (subst_defs v1 x1 defs1)) /\
(forall val1 v1 x1 x2 n1,
  degree_varref_wrt_varref n1 v1 ->
  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_val v1 x1 (close_val_wrt_varref_rec n1 x2 val1) = close_val_wrt_varref_rec n1 x2 (subst_val v1 x1 val1)) /\
(forall t1 v1 x1 x2 n1,
  degree_varref_wrt_varref n1 v1 ->
  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_trm v1 x1 (close_trm_wrt_varref_rec n1 x2 t1) = close_trm_wrt_varref_rec n1 x2 (subst_trm v1 x1 t1)).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_def_close_def_wrt_varref_rec :
forall d1 v1 x1 x2 n1,
  degree_varref_wrt_varref n1 v1 ->
  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_def v1 x1 (close_def_wrt_varref_rec n1 x2 d1) = close_def_wrt_varref_rec n1 x2 (subst_def v1 x1 d1).
Proof.
pose proof subst_def_close_def_wrt_varref_rec_subst_defs_close_defs_wrt_varref_rec_subst_val_close_val_wrt_varref_rec_subst_trm_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_def_close_def_wrt_varref_rec : lngen.

Lemma subst_defs_close_defs_wrt_varref_rec :
forall defs1 v1 x1 x2 n1,
  degree_varref_wrt_varref n1 v1 ->
  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_defs v1 x1 (close_defs_wrt_varref_rec n1 x2 defs1) = close_defs_wrt_varref_rec n1 x2 (subst_defs v1 x1 defs1).
Proof.
pose proof subst_def_close_def_wrt_varref_rec_subst_defs_close_defs_wrt_varref_rec_subst_val_close_val_wrt_varref_rec_subst_trm_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_defs_close_defs_wrt_varref_rec : lngen.

Lemma subst_val_close_val_wrt_varref_rec :
forall val1 v1 x1 x2 n1,
  degree_varref_wrt_varref n1 v1 ->
  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_val v1 x1 (close_val_wrt_varref_rec n1 x2 val1) = close_val_wrt_varref_rec n1 x2 (subst_val v1 x1 val1).
Proof.
pose proof subst_def_close_def_wrt_varref_rec_subst_defs_close_defs_wrt_varref_rec_subst_val_close_val_wrt_varref_rec_subst_trm_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_val_close_val_wrt_varref_rec : lngen.

Lemma subst_trm_close_trm_wrt_varref_rec :
forall t1 v1 x1 x2 n1,
  degree_varref_wrt_varref n1 v1 ->
  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_trm v1 x1 (close_trm_wrt_varref_rec n1 x2 t1) = close_trm_wrt_varref_rec n1 x2 (subst_trm v1 x1 t1).
Proof.
pose proof subst_def_close_def_wrt_varref_rec_subst_defs_close_defs_wrt_varref_rec_subst_val_close_val_wrt_varref_rec_subst_trm_close_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_trm_close_trm_wrt_varref_rec : lngen.

Lemma subst_varref_close_varref_wrt_varref :
forall v2 v1 x1 x2,
  lc_varref v1 ->  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_varref v1 x1 (close_varref_wrt_varref x2 v2) = close_varref_wrt_varref x2 (subst_varref v1 x1 v2).
Proof.
unfold close_varref_wrt_varref; default_simp.
Qed.

Hint Resolve subst_varref_close_varref_wrt_varref : lngen.

Lemma subst_typ_close_typ_wrt_varref :
forall T1 v1 x1 x2,
  lc_varref v1 ->  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_typ v1 x1 (close_typ_wrt_varref x2 T1) = close_typ_wrt_varref x2 (subst_typ v1 x1 T1).
Proof.
unfold close_typ_wrt_varref; default_simp.
Qed.

Hint Resolve subst_typ_close_typ_wrt_varref : lngen.

Lemma subst_dec_close_dec_wrt_varref :
forall dec1 v1 x1 x2,
  lc_varref v1 ->  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_dec v1 x1 (close_dec_wrt_varref x2 dec1) = close_dec_wrt_varref x2 (subst_dec v1 x1 dec1).
Proof.
unfold close_dec_wrt_varref; default_simp.
Qed.

Hint Resolve subst_dec_close_dec_wrt_varref : lngen.

Lemma subst_def_close_def_wrt_varref :
forall d1 v1 x1 x2,
  lc_varref v1 ->  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_def v1 x1 (close_def_wrt_varref x2 d1) = close_def_wrt_varref x2 (subst_def v1 x1 d1).
Proof.
unfold close_def_wrt_varref; default_simp.
Qed.

Hint Resolve subst_def_close_def_wrt_varref : lngen.

Lemma subst_defs_close_defs_wrt_varref :
forall defs1 v1 x1 x2,
  lc_varref v1 ->  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_defs v1 x1 (close_defs_wrt_varref x2 defs1) = close_defs_wrt_varref x2 (subst_defs v1 x1 defs1).
Proof.
unfold close_defs_wrt_varref; default_simp.
Qed.

Hint Resolve subst_defs_close_defs_wrt_varref : lngen.

Lemma subst_val_close_val_wrt_varref :
forall val1 v1 x1 x2,
  lc_varref v1 ->  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_val v1 x1 (close_val_wrt_varref x2 val1) = close_val_wrt_varref x2 (subst_val v1 x1 val1).
Proof.
unfold close_val_wrt_varref; default_simp.
Qed.

Hint Resolve subst_val_close_val_wrt_varref : lngen.

Lemma subst_trm_close_trm_wrt_varref :
forall t1 v1 x1 x2,
  lc_varref v1 ->  x1 <> x2 ->
  x2 `notin` fv_varref v1 ->
  subst_trm v1 x1 (close_trm_wrt_varref x2 t1) = close_trm_wrt_varref x2 (subst_trm v1 x1 t1).
Proof.
unfold close_trm_wrt_varref; default_simp.
Qed.

Hint Resolve subst_trm_close_trm_wrt_varref : lngen.

(* begin hide *)

Lemma subst_varref_degree_varref_wrt_varref_mutual :
(forall v1 v2 x1 n1,
  degree_varref_wrt_varref n1 v1 ->
  degree_varref_wrt_varref n1 v2 ->
  degree_varref_wrt_varref n1 (subst_varref v2 x1 v1)).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_varref_degree_varref_wrt_varref :
forall v1 v2 x1 n1,
  degree_varref_wrt_varref n1 v1 ->
  degree_varref_wrt_varref n1 v2 ->
  degree_varref_wrt_varref n1 (subst_varref v2 x1 v1).
Proof.
pose proof subst_varref_degree_varref_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_varref_degree_varref_wrt_varref : lngen.

(* begin hide *)

Lemma subst_typ_degree_typ_wrt_varref_subst_dec_degree_dec_wrt_varref_mutual :
(forall T1 v1 x1 n1,
  degree_typ_wrt_varref n1 T1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_typ_wrt_varref n1 (subst_typ v1 x1 T1)) /\
(forall dec1 v1 x1 n1,
  degree_dec_wrt_varref n1 dec1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_dec_wrt_varref n1 (subst_dec v1 x1 dec1)).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_degree_typ_wrt_varref :
forall T1 v1 x1 n1,
  degree_typ_wrt_varref n1 T1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_typ_wrt_varref n1 (subst_typ v1 x1 T1).
Proof.
pose proof subst_typ_degree_typ_wrt_varref_subst_dec_degree_dec_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_degree_typ_wrt_varref : lngen.

Lemma subst_dec_degree_dec_wrt_varref :
forall dec1 v1 x1 n1,
  degree_dec_wrt_varref n1 dec1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_dec_wrt_varref n1 (subst_dec v1 x1 dec1).
Proof.
pose proof subst_typ_degree_typ_wrt_varref_subst_dec_degree_dec_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dec_degree_dec_wrt_varref : lngen.

(* begin hide *)

Lemma subst_def_degree_def_wrt_varref_subst_defs_degree_defs_wrt_varref_subst_val_degree_val_wrt_varref_subst_trm_degree_trm_wrt_varref_mutual :
(forall d1 v1 x1 n1,
  degree_def_wrt_varref n1 d1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_def_wrt_varref n1 (subst_def v1 x1 d1)) /\
(forall defs1 v1 x1 n1,
  degree_defs_wrt_varref n1 defs1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_defs_wrt_varref n1 (subst_defs v1 x1 defs1)) /\
(forall val1 v1 x1 n1,
  degree_val_wrt_varref n1 val1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_val_wrt_varref n1 (subst_val v1 x1 val1)) /\
(forall t1 v1 x1 n1,
  degree_trm_wrt_varref n1 t1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_trm_wrt_varref n1 (subst_trm v1 x1 t1)).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_def_degree_def_wrt_varref :
forall d1 v1 x1 n1,
  degree_def_wrt_varref n1 d1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_def_wrt_varref n1 (subst_def v1 x1 d1).
Proof.
pose proof subst_def_degree_def_wrt_varref_subst_defs_degree_defs_wrt_varref_subst_val_degree_val_wrt_varref_subst_trm_degree_trm_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_def_degree_def_wrt_varref : lngen.

Lemma subst_defs_degree_defs_wrt_varref :
forall defs1 v1 x1 n1,
  degree_defs_wrt_varref n1 defs1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_defs_wrt_varref n1 (subst_defs v1 x1 defs1).
Proof.
pose proof subst_def_degree_def_wrt_varref_subst_defs_degree_defs_wrt_varref_subst_val_degree_val_wrt_varref_subst_trm_degree_trm_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_defs_degree_defs_wrt_varref : lngen.

Lemma subst_val_degree_val_wrt_varref :
forall val1 v1 x1 n1,
  degree_val_wrt_varref n1 val1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_val_wrt_varref n1 (subst_val v1 x1 val1).
Proof.
pose proof subst_def_degree_def_wrt_varref_subst_defs_degree_defs_wrt_varref_subst_val_degree_val_wrt_varref_subst_trm_degree_trm_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_val_degree_val_wrt_varref : lngen.

Lemma subst_trm_degree_trm_wrt_varref :
forall t1 v1 x1 n1,
  degree_trm_wrt_varref n1 t1 ->
  degree_varref_wrt_varref n1 v1 ->
  degree_trm_wrt_varref n1 (subst_trm v1 x1 t1).
Proof.
pose proof subst_def_degree_def_wrt_varref_subst_defs_degree_defs_wrt_varref_subst_val_degree_val_wrt_varref_subst_trm_degree_trm_wrt_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_trm_degree_trm_wrt_varref : lngen.

(* begin hide *)

Lemma subst_varref_fresh_eq_mutual :
(forall v2 v1 x1,
  x1 `notin` fv_varref v2 ->
  subst_varref v1 x1 v2 = v2).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_varref_fresh_eq :
forall v2 v1 x1,
  x1 `notin` fv_varref v2 ->
  subst_varref v1 x1 v2 = v2.
Proof.
pose proof subst_varref_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_varref_fresh_eq : lngen.
Hint Rewrite subst_varref_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_fresh_eq_subst_dec_fresh_eq_mutual :
(forall T1 v1 x1,
  x1 `notin` fv_typ T1 ->
  subst_typ v1 x1 T1 = T1) /\
(forall dec1 v1 x1,
  x1 `notin` fv_dec dec1 ->
  subst_dec v1 x1 dec1 = dec1).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_fresh_eq :
forall T1 v1 x1,
  x1 `notin` fv_typ T1 ->
  subst_typ v1 x1 T1 = T1.
Proof.
pose proof subst_typ_fresh_eq_subst_dec_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_fresh_eq : lngen.
Hint Rewrite subst_typ_fresh_eq using solve [auto] : lngen.

Lemma subst_dec_fresh_eq :
forall dec1 v1 x1,
  x1 `notin` fv_dec dec1 ->
  subst_dec v1 x1 dec1 = dec1.
Proof.
pose proof subst_typ_fresh_eq_subst_dec_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dec_fresh_eq : lngen.
Hint Rewrite subst_dec_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_def_fresh_eq_subst_defs_fresh_eq_subst_val_fresh_eq_subst_trm_fresh_eq_mutual :
(forall d1 v1 x1,
  x1 `notin` fv_def d1 ->
  subst_def v1 x1 d1 = d1) /\
(forall defs1 v1 x1,
  x1 `notin` fv_defs defs1 ->
  subst_defs v1 x1 defs1 = defs1) /\
(forall val1 v1 x1,
  x1 `notin` fv_val val1 ->
  subst_val v1 x1 val1 = val1) /\
(forall t1 v1 x1,
  x1 `notin` fv_trm t1 ->
  subst_trm v1 x1 t1 = t1).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_def_fresh_eq :
forall d1 v1 x1,
  x1 `notin` fv_def d1 ->
  subst_def v1 x1 d1 = d1.
Proof.
pose proof subst_def_fresh_eq_subst_defs_fresh_eq_subst_val_fresh_eq_subst_trm_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_def_fresh_eq : lngen.
Hint Rewrite subst_def_fresh_eq using solve [auto] : lngen.

Lemma subst_defs_fresh_eq :
forall defs1 v1 x1,
  x1 `notin` fv_defs defs1 ->
  subst_defs v1 x1 defs1 = defs1.
Proof.
pose proof subst_def_fresh_eq_subst_defs_fresh_eq_subst_val_fresh_eq_subst_trm_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_defs_fresh_eq : lngen.
Hint Rewrite subst_defs_fresh_eq using solve [auto] : lngen.

Lemma subst_val_fresh_eq :
forall val1 v1 x1,
  x1 `notin` fv_val val1 ->
  subst_val v1 x1 val1 = val1.
Proof.
pose proof subst_def_fresh_eq_subst_defs_fresh_eq_subst_val_fresh_eq_subst_trm_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_val_fresh_eq : lngen.
Hint Rewrite subst_val_fresh_eq using solve [auto] : lngen.

Lemma subst_trm_fresh_eq :
forall t1 v1 x1,
  x1 `notin` fv_trm t1 ->
  subst_trm v1 x1 t1 = t1.
Proof.
pose proof subst_def_fresh_eq_subst_defs_fresh_eq_subst_val_fresh_eq_subst_trm_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_trm_fresh_eq : lngen.
Hint Rewrite subst_trm_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_varref_fresh_same_mutual :
(forall v2 v1 x1,
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_varref (subst_varref v1 x1 v2)).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_varref_fresh_same :
forall v2 v1 x1,
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_varref (subst_varref v1 x1 v2).
Proof.
pose proof subst_varref_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_varref_fresh_same : lngen.

(* begin hide *)

Lemma subst_typ_fresh_same_subst_dec_fresh_same_mutual :
(forall T1 v1 x1,
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_typ (subst_typ v1 x1 T1)) /\
(forall dec1 v1 x1,
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_dec (subst_dec v1 x1 dec1)).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_fresh_same :
forall T1 v1 x1,
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_typ (subst_typ v1 x1 T1).
Proof.
pose proof subst_typ_fresh_same_subst_dec_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_fresh_same : lngen.

Lemma subst_dec_fresh_same :
forall dec1 v1 x1,
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_dec (subst_dec v1 x1 dec1).
Proof.
pose proof subst_typ_fresh_same_subst_dec_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dec_fresh_same : lngen.

(* begin hide *)

Lemma subst_def_fresh_same_subst_defs_fresh_same_subst_val_fresh_same_subst_trm_fresh_same_mutual :
(forall d1 v1 x1,
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_def (subst_def v1 x1 d1)) /\
(forall defs1 v1 x1,
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_defs (subst_defs v1 x1 defs1)) /\
(forall val1 v1 x1,
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_val (subst_val v1 x1 val1)) /\
(forall t1 v1 x1,
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_trm (subst_trm v1 x1 t1)).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_def_fresh_same :
forall d1 v1 x1,
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_def (subst_def v1 x1 d1).
Proof.
pose proof subst_def_fresh_same_subst_defs_fresh_same_subst_val_fresh_same_subst_trm_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_def_fresh_same : lngen.

Lemma subst_defs_fresh_same :
forall defs1 v1 x1,
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_defs (subst_defs v1 x1 defs1).
Proof.
pose proof subst_def_fresh_same_subst_defs_fresh_same_subst_val_fresh_same_subst_trm_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_defs_fresh_same : lngen.

Lemma subst_val_fresh_same :
forall val1 v1 x1,
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_val (subst_val v1 x1 val1).
Proof.
pose proof subst_def_fresh_same_subst_defs_fresh_same_subst_val_fresh_same_subst_trm_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_val_fresh_same : lngen.

Lemma subst_trm_fresh_same :
forall t1 v1 x1,
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_trm (subst_trm v1 x1 t1).
Proof.
pose proof subst_def_fresh_same_subst_defs_fresh_same_subst_val_fresh_same_subst_trm_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_trm_fresh_same : lngen.

(* begin hide *)

Lemma subst_varref_fresh_mutual :
(forall v2 v1 x1 x2,
  x1 `notin` fv_varref v2 ->
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_varref (subst_varref v1 x2 v2)).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_varref_fresh :
forall v2 v1 x1 x2,
  x1 `notin` fv_varref v2 ->
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_varref (subst_varref v1 x2 v2).
Proof.
pose proof subst_varref_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_varref_fresh : lngen.

(* begin hide *)

Lemma subst_typ_fresh_subst_dec_fresh_mutual :
(forall T1 v1 x1 x2,
  x1 `notin` fv_typ T1 ->
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_typ (subst_typ v1 x2 T1)) /\
(forall dec1 v1 x1 x2,
  x1 `notin` fv_dec dec1 ->
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_dec (subst_dec v1 x2 dec1)).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_fresh :
forall T1 v1 x1 x2,
  x1 `notin` fv_typ T1 ->
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_typ (subst_typ v1 x2 T1).
Proof.
pose proof subst_typ_fresh_subst_dec_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_fresh : lngen.

Lemma subst_dec_fresh :
forall dec1 v1 x1 x2,
  x1 `notin` fv_dec dec1 ->
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_dec (subst_dec v1 x2 dec1).
Proof.
pose proof subst_typ_fresh_subst_dec_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dec_fresh : lngen.

(* begin hide *)

Lemma subst_def_fresh_subst_defs_fresh_subst_val_fresh_subst_trm_fresh_mutual :
(forall d1 v1 x1 x2,
  x1 `notin` fv_def d1 ->
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_def (subst_def v1 x2 d1)) /\
(forall defs1 v1 x1 x2,
  x1 `notin` fv_defs defs1 ->
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_defs (subst_defs v1 x2 defs1)) /\
(forall val1 v1 x1 x2,
  x1 `notin` fv_val val1 ->
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_val (subst_val v1 x2 val1)) /\
(forall t1 v1 x1 x2,
  x1 `notin` fv_trm t1 ->
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_trm (subst_trm v1 x2 t1)).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_def_fresh :
forall d1 v1 x1 x2,
  x1 `notin` fv_def d1 ->
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_def (subst_def v1 x2 d1).
Proof.
pose proof subst_def_fresh_subst_defs_fresh_subst_val_fresh_subst_trm_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_def_fresh : lngen.

Lemma subst_defs_fresh :
forall defs1 v1 x1 x2,
  x1 `notin` fv_defs defs1 ->
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_defs (subst_defs v1 x2 defs1).
Proof.
pose proof subst_def_fresh_subst_defs_fresh_subst_val_fresh_subst_trm_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_defs_fresh : lngen.

Lemma subst_val_fresh :
forall val1 v1 x1 x2,
  x1 `notin` fv_val val1 ->
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_val (subst_val v1 x2 val1).
Proof.
pose proof subst_def_fresh_subst_defs_fresh_subst_val_fresh_subst_trm_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_val_fresh : lngen.

Lemma subst_trm_fresh :
forall t1 v1 x1 x2,
  x1 `notin` fv_trm t1 ->
  x1 `notin` fv_varref v1 ->
  x1 `notin` fv_trm (subst_trm v1 x2 t1).
Proof.
pose proof subst_def_fresh_subst_defs_fresh_subst_val_fresh_subst_trm_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_trm_fresh : lngen.

Lemma subst_varref_lc_varref :
forall v1 v2 x1,
  lc_varref v1 ->
  lc_varref v2 ->
  lc_varref (subst_varref v2 x1 v1).
Proof.
default_simp.
Qed.

Hint Resolve subst_varref_lc_varref : lngen.

Lemma subst_typ_lc_typ :
forall T1 v1 x1,
  lc_typ T1 ->
  lc_varref v1 ->
  lc_typ (subst_typ v1 x1 T1).
Proof.
default_simp.
Qed.

Hint Resolve subst_typ_lc_typ : lngen.

Lemma subst_dec_lc_dec :
forall dec1 v1 x1,
  lc_dec dec1 ->
  lc_varref v1 ->
  lc_dec (subst_dec v1 x1 dec1).
Proof.
default_simp.
Qed.

Hint Resolve subst_dec_lc_dec : lngen.

Lemma subst_def_lc_def :
forall d1 v1 x1,
  lc_def d1 ->
  lc_varref v1 ->
  lc_def (subst_def v1 x1 d1).
Proof.
default_simp.
Qed.

Hint Resolve subst_def_lc_def : lngen.

Lemma subst_defs_lc_defs :
forall defs1 v1 x1,
  lc_defs defs1 ->
  lc_varref v1 ->
  lc_defs (subst_defs v1 x1 defs1).
Proof.
default_simp.
Qed.

Hint Resolve subst_defs_lc_defs : lngen.

Lemma subst_val_lc_val :
forall val1 v1 x1,
  lc_val val1 ->
  lc_varref v1 ->
  lc_val (subst_val v1 x1 val1).
Proof.
default_simp.
Qed.

Hint Resolve subst_val_lc_val : lngen.

Lemma subst_trm_lc_trm :
forall t1 v1 x1,
  lc_trm t1 ->
  lc_varref v1 ->
  lc_trm (subst_trm v1 x1 t1).
Proof.
default_simp.
Qed.

Hint Resolve subst_trm_lc_trm : lngen.

(* begin hide *)

Lemma subst_varref_open_varref_wrt_varref_rec_mutual :
(forall v3 v1 v2 x1 n1,
  lc_varref v1 ->
  subst_varref v1 x1 (open_varref_wrt_varref_rec n1 v2 v3) = open_varref_wrt_varref_rec n1 (subst_varref v1 x1 v2) (subst_varref v1 x1 v3)).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_varref_open_varref_wrt_varref_rec :
forall v3 v1 v2 x1 n1,
  lc_varref v1 ->
  subst_varref v1 x1 (open_varref_wrt_varref_rec n1 v2 v3) = open_varref_wrt_varref_rec n1 (subst_varref v1 x1 v2) (subst_varref v1 x1 v3).
Proof.
pose proof subst_varref_open_varref_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_varref_open_varref_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_open_typ_wrt_varref_rec_subst_dec_open_dec_wrt_varref_rec_mutual :
(forall T1 v1 v2 x1 n1,
  lc_varref v1 ->
  subst_typ v1 x1 (open_typ_wrt_varref_rec n1 v2 T1) = open_typ_wrt_varref_rec n1 (subst_varref v1 x1 v2) (subst_typ v1 x1 T1)) /\
(forall dec1 v1 v2 x1 n1,
  lc_varref v1 ->
  subst_dec v1 x1 (open_dec_wrt_varref_rec n1 v2 dec1) = open_dec_wrt_varref_rec n1 (subst_varref v1 x1 v2) (subst_dec v1 x1 dec1)).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_open_typ_wrt_varref_rec :
forall T1 v1 v2 x1 n1,
  lc_varref v1 ->
  subst_typ v1 x1 (open_typ_wrt_varref_rec n1 v2 T1) = open_typ_wrt_varref_rec n1 (subst_varref v1 x1 v2) (subst_typ v1 x1 T1).
Proof.
pose proof subst_typ_open_typ_wrt_varref_rec_subst_dec_open_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_open_typ_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_dec_open_dec_wrt_varref_rec :
forall dec1 v1 v2 x1 n1,
  lc_varref v1 ->
  subst_dec v1 x1 (open_dec_wrt_varref_rec n1 v2 dec1) = open_dec_wrt_varref_rec n1 (subst_varref v1 x1 v2) (subst_dec v1 x1 dec1).
Proof.
pose proof subst_typ_open_typ_wrt_varref_rec_subst_dec_open_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dec_open_dec_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_def_open_def_wrt_varref_rec_subst_defs_open_defs_wrt_varref_rec_subst_val_open_val_wrt_varref_rec_subst_trm_open_trm_wrt_varref_rec_mutual :
(forall d1 v1 v2 x1 n1,
  lc_varref v1 ->
  subst_def v1 x1 (open_def_wrt_varref_rec n1 v2 d1) = open_def_wrt_varref_rec n1 (subst_varref v1 x1 v2) (subst_def v1 x1 d1)) /\
(forall defs1 v1 v2 x1 n1,
  lc_varref v1 ->
  subst_defs v1 x1 (open_defs_wrt_varref_rec n1 v2 defs1) = open_defs_wrt_varref_rec n1 (subst_varref v1 x1 v2) (subst_defs v1 x1 defs1)) /\
(forall val1 v1 v2 x1 n1,
  lc_varref v1 ->
  subst_val v1 x1 (open_val_wrt_varref_rec n1 v2 val1) = open_val_wrt_varref_rec n1 (subst_varref v1 x1 v2) (subst_val v1 x1 val1)) /\
(forall t1 v1 v2 x1 n1,
  lc_varref v1 ->
  subst_trm v1 x1 (open_trm_wrt_varref_rec n1 v2 t1) = open_trm_wrt_varref_rec n1 (subst_varref v1 x1 v2) (subst_trm v1 x1 t1)).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_def_open_def_wrt_varref_rec :
forall d1 v1 v2 x1 n1,
  lc_varref v1 ->
  subst_def v1 x1 (open_def_wrt_varref_rec n1 v2 d1) = open_def_wrt_varref_rec n1 (subst_varref v1 x1 v2) (subst_def v1 x1 d1).
Proof.
pose proof subst_def_open_def_wrt_varref_rec_subst_defs_open_defs_wrt_varref_rec_subst_val_open_val_wrt_varref_rec_subst_trm_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_def_open_def_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_defs_open_defs_wrt_varref_rec :
forall defs1 v1 v2 x1 n1,
  lc_varref v1 ->
  subst_defs v1 x1 (open_defs_wrt_varref_rec n1 v2 defs1) = open_defs_wrt_varref_rec n1 (subst_varref v1 x1 v2) (subst_defs v1 x1 defs1).
Proof.
pose proof subst_def_open_def_wrt_varref_rec_subst_defs_open_defs_wrt_varref_rec_subst_val_open_val_wrt_varref_rec_subst_trm_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_defs_open_defs_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_val_open_val_wrt_varref_rec :
forall val1 v1 v2 x1 n1,
  lc_varref v1 ->
  subst_val v1 x1 (open_val_wrt_varref_rec n1 v2 val1) = open_val_wrt_varref_rec n1 (subst_varref v1 x1 v2) (subst_val v1 x1 val1).
Proof.
pose proof subst_def_open_def_wrt_varref_rec_subst_defs_open_defs_wrt_varref_rec_subst_val_open_val_wrt_varref_rec_subst_trm_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_val_open_val_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_trm_open_trm_wrt_varref_rec :
forall t1 v1 v2 x1 n1,
  lc_varref v1 ->
  subst_trm v1 x1 (open_trm_wrt_varref_rec n1 v2 t1) = open_trm_wrt_varref_rec n1 (subst_varref v1 x1 v2) (subst_trm v1 x1 t1).
Proof.
pose proof subst_def_open_def_wrt_varref_rec_subst_defs_open_defs_wrt_varref_rec_subst_val_open_val_wrt_varref_rec_subst_trm_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_trm_open_trm_wrt_varref_rec : lngen.

(* end hide *)

Lemma subst_varref_open_varref_wrt_varref :
forall v3 v1 v2 x1,
  lc_varref v1 ->
  subst_varref v1 x1 (open_varref_wrt_varref v3 v2) = open_varref_wrt_varref (subst_varref v1 x1 v3) (subst_varref v1 x1 v2).
Proof.
unfold open_varref_wrt_varref; default_simp.
Qed.

Hint Resolve subst_varref_open_varref_wrt_varref : lngen.

Lemma subst_typ_open_typ_wrt_varref :
forall T1 v1 v2 x1,
  lc_varref v1 ->
  subst_typ v1 x1 (open_typ_wrt_varref T1 v2) = open_typ_wrt_varref (subst_typ v1 x1 T1) (subst_varref v1 x1 v2).
Proof.
unfold open_typ_wrt_varref; default_simp.
Qed.

Hint Resolve subst_typ_open_typ_wrt_varref : lngen.

Lemma subst_dec_open_dec_wrt_varref :
forall dec1 v1 v2 x1,
  lc_varref v1 ->
  subst_dec v1 x1 (open_dec_wrt_varref dec1 v2) = open_dec_wrt_varref (subst_dec v1 x1 dec1) (subst_varref v1 x1 v2).
Proof.
unfold open_dec_wrt_varref; default_simp.
Qed.

Hint Resolve subst_dec_open_dec_wrt_varref : lngen.

Lemma subst_def_open_def_wrt_varref :
forall d1 v1 v2 x1,
  lc_varref v1 ->
  subst_def v1 x1 (open_def_wrt_varref d1 v2) = open_def_wrt_varref (subst_def v1 x1 d1) (subst_varref v1 x1 v2).
Proof.
unfold open_def_wrt_varref; default_simp.
Qed.

Hint Resolve subst_def_open_def_wrt_varref : lngen.

Lemma subst_defs_open_defs_wrt_varref :
forall defs1 v1 v2 x1,
  lc_varref v1 ->
  subst_defs v1 x1 (open_defs_wrt_varref defs1 v2) = open_defs_wrt_varref (subst_defs v1 x1 defs1) (subst_varref v1 x1 v2).
Proof.
unfold open_defs_wrt_varref; default_simp.
Qed.

Hint Resolve subst_defs_open_defs_wrt_varref : lngen.

Lemma subst_val_open_val_wrt_varref :
forall val1 v1 v2 x1,
  lc_varref v1 ->
  subst_val v1 x1 (open_val_wrt_varref val1 v2) = open_val_wrt_varref (subst_val v1 x1 val1) (subst_varref v1 x1 v2).
Proof.
unfold open_val_wrt_varref; default_simp.
Qed.

Hint Resolve subst_val_open_val_wrt_varref : lngen.

Lemma subst_trm_open_trm_wrt_varref :
forall t1 v1 v2 x1,
  lc_varref v1 ->
  subst_trm v1 x1 (open_trm_wrt_varref t1 v2) = open_trm_wrt_varref (subst_trm v1 x1 t1) (subst_varref v1 x1 v2).
Proof.
unfold open_trm_wrt_varref; default_simp.
Qed.

Hint Resolve subst_trm_open_trm_wrt_varref : lngen.

Lemma subst_varref_open_varref_wrt_varref_var :
forall v2 v1 x1 x2,
  x1 <> x2 ->
  lc_varref v1 ->
  open_varref_wrt_varref (subst_varref v1 x1 v2) (var_termvar_f x2) = subst_varref v1 x1 (open_varref_wrt_varref v2 (var_termvar_f x2)).
Proof.
intros; rewrite subst_varref_open_varref_wrt_varref; default_simp.
Qed.

Hint Resolve subst_varref_open_varref_wrt_varref_var : lngen.

Lemma subst_typ_open_typ_wrt_varref_var :
forall T1 v1 x1 x2,
  x1 <> x2 ->
  lc_varref v1 ->
  open_typ_wrt_varref (subst_typ v1 x1 T1) (var_termvar_f x2) = subst_typ v1 x1 (open_typ_wrt_varref T1 (var_termvar_f x2)).
Proof.
intros; rewrite subst_typ_open_typ_wrt_varref; default_simp.
Qed.

Hint Resolve subst_typ_open_typ_wrt_varref_var : lngen.

Lemma subst_dec_open_dec_wrt_varref_var :
forall dec1 v1 x1 x2,
  x1 <> x2 ->
  lc_varref v1 ->
  open_dec_wrt_varref (subst_dec v1 x1 dec1) (var_termvar_f x2) = subst_dec v1 x1 (open_dec_wrt_varref dec1 (var_termvar_f x2)).
Proof.
intros; rewrite subst_dec_open_dec_wrt_varref; default_simp.
Qed.

Hint Resolve subst_dec_open_dec_wrt_varref_var : lngen.

Lemma subst_def_open_def_wrt_varref_var :
forall d1 v1 x1 x2,
  x1 <> x2 ->
  lc_varref v1 ->
  open_def_wrt_varref (subst_def v1 x1 d1) (var_termvar_f x2) = subst_def v1 x1 (open_def_wrt_varref d1 (var_termvar_f x2)).
Proof.
intros; rewrite subst_def_open_def_wrt_varref; default_simp.
Qed.

Hint Resolve subst_def_open_def_wrt_varref_var : lngen.

Lemma subst_defs_open_defs_wrt_varref_var :
forall defs1 v1 x1 x2,
  x1 <> x2 ->
  lc_varref v1 ->
  open_defs_wrt_varref (subst_defs v1 x1 defs1) (var_termvar_f x2) = subst_defs v1 x1 (open_defs_wrt_varref defs1 (var_termvar_f x2)).
Proof.
intros; rewrite subst_defs_open_defs_wrt_varref; default_simp.
Qed.

Hint Resolve subst_defs_open_defs_wrt_varref_var : lngen.

Lemma subst_val_open_val_wrt_varref_var :
forall val1 v1 x1 x2,
  x1 <> x2 ->
  lc_varref v1 ->
  open_val_wrt_varref (subst_val v1 x1 val1) (var_termvar_f x2) = subst_val v1 x1 (open_val_wrt_varref val1 (var_termvar_f x2)).
Proof.
intros; rewrite subst_val_open_val_wrt_varref; default_simp.
Qed.

Hint Resolve subst_val_open_val_wrt_varref_var : lngen.

Lemma subst_trm_open_trm_wrt_varref_var :
forall t1 v1 x1 x2,
  x1 <> x2 ->
  lc_varref v1 ->
  open_trm_wrt_varref (subst_trm v1 x1 t1) (var_termvar_f x2) = subst_trm v1 x1 (open_trm_wrt_varref t1 (var_termvar_f x2)).
Proof.
intros; rewrite subst_trm_open_trm_wrt_varref; default_simp.
Qed.

Hint Resolve subst_trm_open_trm_wrt_varref_var : lngen.

(* begin hide *)

Lemma subst_varref_spec_rec_mutual :
(forall v1 v2 x1 n1,
  subst_varref v2 x1 v1 = open_varref_wrt_varref_rec n1 v2 (close_varref_wrt_varref_rec n1 x1 v1)).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_varref_spec_rec :
forall v1 v2 x1 n1,
  subst_varref v2 x1 v1 = open_varref_wrt_varref_rec n1 v2 (close_varref_wrt_varref_rec n1 x1 v1).
Proof.
pose proof subst_varref_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_varref_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_spec_rec_subst_dec_spec_rec_mutual :
(forall T1 v1 x1 n1,
  subst_typ v1 x1 T1 = open_typ_wrt_varref_rec n1 v1 (close_typ_wrt_varref_rec n1 x1 T1)) /\
(forall dec1 v1 x1 n1,
  subst_dec v1 x1 dec1 = open_dec_wrt_varref_rec n1 v1 (close_dec_wrt_varref_rec n1 x1 dec1)).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_spec_rec :
forall T1 v1 x1 n1,
  subst_typ v1 x1 T1 = open_typ_wrt_varref_rec n1 v1 (close_typ_wrt_varref_rec n1 x1 T1).
Proof.
pose proof subst_typ_spec_rec_subst_dec_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_dec_spec_rec :
forall dec1 v1 x1 n1,
  subst_dec v1 x1 dec1 = open_dec_wrt_varref_rec n1 v1 (close_dec_wrt_varref_rec n1 x1 dec1).
Proof.
pose proof subst_typ_spec_rec_subst_dec_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dec_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_def_spec_rec_subst_defs_spec_rec_subst_val_spec_rec_subst_trm_spec_rec_mutual :
(forall d1 v1 x1 n1,
  subst_def v1 x1 d1 = open_def_wrt_varref_rec n1 v1 (close_def_wrt_varref_rec n1 x1 d1)) /\
(forall defs1 v1 x1 n1,
  subst_defs v1 x1 defs1 = open_defs_wrt_varref_rec n1 v1 (close_defs_wrt_varref_rec n1 x1 defs1)) /\
(forall val1 v1 x1 n1,
  subst_val v1 x1 val1 = open_val_wrt_varref_rec n1 v1 (close_val_wrt_varref_rec n1 x1 val1)) /\
(forall t1 v1 x1 n1,
  subst_trm v1 x1 t1 = open_trm_wrt_varref_rec n1 v1 (close_trm_wrt_varref_rec n1 x1 t1)).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_def_spec_rec :
forall d1 v1 x1 n1,
  subst_def v1 x1 d1 = open_def_wrt_varref_rec n1 v1 (close_def_wrt_varref_rec n1 x1 d1).
Proof.
pose proof subst_def_spec_rec_subst_defs_spec_rec_subst_val_spec_rec_subst_trm_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_def_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_defs_spec_rec :
forall defs1 v1 x1 n1,
  subst_defs v1 x1 defs1 = open_defs_wrt_varref_rec n1 v1 (close_defs_wrt_varref_rec n1 x1 defs1).
Proof.
pose proof subst_def_spec_rec_subst_defs_spec_rec_subst_val_spec_rec_subst_trm_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_defs_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_val_spec_rec :
forall val1 v1 x1 n1,
  subst_val v1 x1 val1 = open_val_wrt_varref_rec n1 v1 (close_val_wrt_varref_rec n1 x1 val1).
Proof.
pose proof subst_def_spec_rec_subst_defs_spec_rec_subst_val_spec_rec_subst_trm_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_val_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_trm_spec_rec :
forall t1 v1 x1 n1,
  subst_trm v1 x1 t1 = open_trm_wrt_varref_rec n1 v1 (close_trm_wrt_varref_rec n1 x1 t1).
Proof.
pose proof subst_def_spec_rec_subst_defs_spec_rec_subst_val_spec_rec_subst_trm_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_trm_spec_rec : lngen.

(* end hide *)

Lemma subst_varref_spec :
forall v1 v2 x1,
  subst_varref v2 x1 v1 = open_varref_wrt_varref (close_varref_wrt_varref x1 v1) v2.
Proof.
unfold close_varref_wrt_varref; unfold open_varref_wrt_varref; default_simp.
Qed.

Hint Resolve subst_varref_spec : lngen.

Lemma subst_typ_spec :
forall T1 v1 x1,
  subst_typ v1 x1 T1 = open_typ_wrt_varref (close_typ_wrt_varref x1 T1) v1.
Proof.
unfold close_typ_wrt_varref; unfold open_typ_wrt_varref; default_simp.
Qed.

Hint Resolve subst_typ_spec : lngen.

Lemma subst_dec_spec :
forall dec1 v1 x1,
  subst_dec v1 x1 dec1 = open_dec_wrt_varref (close_dec_wrt_varref x1 dec1) v1.
Proof.
unfold close_dec_wrt_varref; unfold open_dec_wrt_varref; default_simp.
Qed.

Hint Resolve subst_dec_spec : lngen.

Lemma subst_def_spec :
forall d1 v1 x1,
  subst_def v1 x1 d1 = open_def_wrt_varref (close_def_wrt_varref x1 d1) v1.
Proof.
unfold close_def_wrt_varref; unfold open_def_wrt_varref; default_simp.
Qed.

Hint Resolve subst_def_spec : lngen.

Lemma subst_defs_spec :
forall defs1 v1 x1,
  subst_defs v1 x1 defs1 = open_defs_wrt_varref (close_defs_wrt_varref x1 defs1) v1.
Proof.
unfold close_defs_wrt_varref; unfold open_defs_wrt_varref; default_simp.
Qed.

Hint Resolve subst_defs_spec : lngen.

Lemma subst_val_spec :
forall val1 v1 x1,
  subst_val v1 x1 val1 = open_val_wrt_varref (close_val_wrt_varref x1 val1) v1.
Proof.
unfold close_val_wrt_varref; unfold open_val_wrt_varref; default_simp.
Qed.

Hint Resolve subst_val_spec : lngen.

Lemma subst_trm_spec :
forall t1 v1 x1,
  subst_trm v1 x1 t1 = open_trm_wrt_varref (close_trm_wrt_varref x1 t1) v1.
Proof.
unfold close_trm_wrt_varref; unfold open_trm_wrt_varref; default_simp.
Qed.

Hint Resolve subst_trm_spec : lngen.

(* begin hide *)

Lemma subst_varref_subst_varref_mutual :
(forall v1 v2 v3 x2 x1,
  x2 `notin` fv_varref v2 ->
  x2 <> x1 ->
  subst_varref v2 x1 (subst_varref v3 x2 v1) = subst_varref (subst_varref v2 x1 v3) x2 (subst_varref v2 x1 v1)).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_varref_subst_varref :
forall v1 v2 v3 x2 x1,
  x2 `notin` fv_varref v2 ->
  x2 <> x1 ->
  subst_varref v2 x1 (subst_varref v3 x2 v1) = subst_varref (subst_varref v2 x1 v3) x2 (subst_varref v2 x1 v1).
Proof.
pose proof subst_varref_subst_varref_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_varref_subst_varref : lngen.

(* begin hide *)

Lemma subst_typ_subst_typ_subst_dec_subst_dec_mutual :
(forall T1 v1 v2 x2 x1,
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  subst_typ v1 x1 (subst_typ v2 x2 T1) = subst_typ (subst_varref v1 x1 v2) x2 (subst_typ v1 x1 T1)) /\
(forall dec1 v1 v2 x2 x1,
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  subst_dec v1 x1 (subst_dec v2 x2 dec1) = subst_dec (subst_varref v1 x1 v2) x2 (subst_dec v1 x1 dec1)).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_subst_typ :
forall T1 v1 v2 x2 x1,
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  subst_typ v1 x1 (subst_typ v2 x2 T1) = subst_typ (subst_varref v1 x1 v2) x2 (subst_typ v1 x1 T1).
Proof.
pose proof subst_typ_subst_typ_subst_dec_subst_dec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_subst_typ : lngen.

Lemma subst_dec_subst_dec :
forall dec1 v1 v2 x2 x1,
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  subst_dec v1 x1 (subst_dec v2 x2 dec1) = subst_dec (subst_varref v1 x1 v2) x2 (subst_dec v1 x1 dec1).
Proof.
pose proof subst_typ_subst_typ_subst_dec_subst_dec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dec_subst_dec : lngen.

(* begin hide *)

Lemma subst_def_subst_def_subst_defs_subst_defs_subst_val_subst_val_subst_trm_subst_trm_mutual :
(forall d1 v1 v2 x2 x1,
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  subst_def v1 x1 (subst_def v2 x2 d1) = subst_def (subst_varref v1 x1 v2) x2 (subst_def v1 x1 d1)) /\
(forall defs1 v1 v2 x2 x1,
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  subst_defs v1 x1 (subst_defs v2 x2 defs1) = subst_defs (subst_varref v1 x1 v2) x2 (subst_defs v1 x1 defs1)) /\
(forall val1 v1 v2 x2 x1,
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  subst_val v1 x1 (subst_val v2 x2 val1) = subst_val (subst_varref v1 x1 v2) x2 (subst_val v1 x1 val1)) /\
(forall t1 v1 v2 x2 x1,
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  subst_trm v1 x1 (subst_trm v2 x2 t1) = subst_trm (subst_varref v1 x1 v2) x2 (subst_trm v1 x1 t1)).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_def_subst_def :
forall d1 v1 v2 x2 x1,
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  subst_def v1 x1 (subst_def v2 x2 d1) = subst_def (subst_varref v1 x1 v2) x2 (subst_def v1 x1 d1).
Proof.
pose proof subst_def_subst_def_subst_defs_subst_defs_subst_val_subst_val_subst_trm_subst_trm_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_def_subst_def : lngen.

Lemma subst_defs_subst_defs :
forall defs1 v1 v2 x2 x1,
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  subst_defs v1 x1 (subst_defs v2 x2 defs1) = subst_defs (subst_varref v1 x1 v2) x2 (subst_defs v1 x1 defs1).
Proof.
pose proof subst_def_subst_def_subst_defs_subst_defs_subst_val_subst_val_subst_trm_subst_trm_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_defs_subst_defs : lngen.

Lemma subst_val_subst_val :
forall val1 v1 v2 x2 x1,
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  subst_val v1 x1 (subst_val v2 x2 val1) = subst_val (subst_varref v1 x1 v2) x2 (subst_val v1 x1 val1).
Proof.
pose proof subst_def_subst_def_subst_defs_subst_defs_subst_val_subst_val_subst_trm_subst_trm_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_val_subst_val : lngen.

Lemma subst_trm_subst_trm :
forall t1 v1 v2 x2 x1,
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  subst_trm v1 x1 (subst_trm v2 x2 t1) = subst_trm (subst_varref v1 x1 v2) x2 (subst_trm v1 x1 t1).
Proof.
pose proof subst_def_subst_def_subst_defs_subst_defs_subst_val_subst_val_subst_trm_subst_trm_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_trm_subst_trm : lngen.

(* begin hide *)

Lemma subst_varref_close_varref_wrt_varref_rec_open_varref_wrt_varref_rec_mutual :
(forall v2 v1 x1 x2 n1,
  x2 `notin` fv_varref v2 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  degree_varref_wrt_varref n1 v1 ->
  subst_varref v1 x1 v2 = close_varref_wrt_varref_rec n1 x2 (subst_varref v1 x1 (open_varref_wrt_varref_rec n1 (var_termvar_f x2) v2))).
Proof.
apply_mutual_ind varref_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_varref_close_varref_wrt_varref_rec_open_varref_wrt_varref_rec :
forall v2 v1 x1 x2 n1,
  x2 `notin` fv_varref v2 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  degree_varref_wrt_varref n1 v1 ->
  subst_varref v1 x1 v2 = close_varref_wrt_varref_rec n1 x2 (subst_varref v1 x1 (open_varref_wrt_varref_rec n1 (var_termvar_f x2) v2)).
Proof.
pose proof subst_varref_close_varref_wrt_varref_rec_open_varref_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_varref_close_varref_wrt_varref_rec_open_varref_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_close_typ_wrt_varref_rec_open_typ_wrt_varref_rec_subst_dec_close_dec_wrt_varref_rec_open_dec_wrt_varref_rec_mutual :
(forall T1 v1 x1 x2 n1,
  x2 `notin` fv_typ T1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  degree_varref_wrt_varref n1 v1 ->
  subst_typ v1 x1 T1 = close_typ_wrt_varref_rec n1 x2 (subst_typ v1 x1 (open_typ_wrt_varref_rec n1 (var_termvar_f x2) T1))) *
(forall dec1 v1 x1 x2 n1,
  x2 `notin` fv_dec dec1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  degree_varref_wrt_varref n1 v1 ->
  subst_dec v1 x1 dec1 = close_dec_wrt_varref_rec n1 x2 (subst_dec v1 x1 (open_dec_wrt_varref_rec n1 (var_termvar_f x2) dec1))).
Proof.
apply_mutual_ind typ_dec_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_close_typ_wrt_varref_rec_open_typ_wrt_varref_rec :
forall T1 v1 x1 x2 n1,
  x2 `notin` fv_typ T1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  degree_varref_wrt_varref n1 v1 ->
  subst_typ v1 x1 T1 = close_typ_wrt_varref_rec n1 x2 (subst_typ v1 x1 (open_typ_wrt_varref_rec n1 (var_termvar_f x2) T1)).
Proof.
pose proof subst_typ_close_typ_wrt_varref_rec_open_typ_wrt_varref_rec_subst_dec_close_dec_wrt_varref_rec_open_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_close_typ_wrt_varref_rec_open_typ_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_dec_close_dec_wrt_varref_rec_open_dec_wrt_varref_rec :
forall dec1 v1 x1 x2 n1,
  x2 `notin` fv_dec dec1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  degree_varref_wrt_varref n1 v1 ->
  subst_dec v1 x1 dec1 = close_dec_wrt_varref_rec n1 x2 (subst_dec v1 x1 (open_dec_wrt_varref_rec n1 (var_termvar_f x2) dec1)).
Proof.
pose proof subst_typ_close_typ_wrt_varref_rec_open_typ_wrt_varref_rec_subst_dec_close_dec_wrt_varref_rec_open_dec_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dec_close_dec_wrt_varref_rec_open_dec_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_def_close_def_wrt_varref_rec_open_def_wrt_varref_rec_subst_defs_close_defs_wrt_varref_rec_open_defs_wrt_varref_rec_subst_val_close_val_wrt_varref_rec_open_val_wrt_varref_rec_subst_trm_close_trm_wrt_varref_rec_open_trm_wrt_varref_rec_mutual :
(forall d1 v1 x1 x2 n1,
  x2 `notin` fv_def d1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  degree_varref_wrt_varref n1 v1 ->
  subst_def v1 x1 d1 = close_def_wrt_varref_rec n1 x2 (subst_def v1 x1 (open_def_wrt_varref_rec n1 (var_termvar_f x2) d1))) *
(forall defs1 v1 x1 x2 n1,
  x2 `notin` fv_defs defs1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  degree_varref_wrt_varref n1 v1 ->
  subst_defs v1 x1 defs1 = close_defs_wrt_varref_rec n1 x2 (subst_defs v1 x1 (open_defs_wrt_varref_rec n1 (var_termvar_f x2) defs1))) *
(forall val1 v1 x1 x2 n1,
  x2 `notin` fv_val val1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  degree_varref_wrt_varref n1 v1 ->
  subst_val v1 x1 val1 = close_val_wrt_varref_rec n1 x2 (subst_val v1 x1 (open_val_wrt_varref_rec n1 (var_termvar_f x2) val1))) *
(forall t1 v1 x1 x2 n1,
  x2 `notin` fv_trm t1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  degree_varref_wrt_varref n1 v1 ->
  subst_trm v1 x1 t1 = close_trm_wrt_varref_rec n1 x2 (subst_trm v1 x1 (open_trm_wrt_varref_rec n1 (var_termvar_f x2) t1))).
Proof.
apply_mutual_ind def_defs_val_trm_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_def_close_def_wrt_varref_rec_open_def_wrt_varref_rec :
forall d1 v1 x1 x2 n1,
  x2 `notin` fv_def d1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  degree_varref_wrt_varref n1 v1 ->
  subst_def v1 x1 d1 = close_def_wrt_varref_rec n1 x2 (subst_def v1 x1 (open_def_wrt_varref_rec n1 (var_termvar_f x2) d1)).
Proof.
pose proof subst_def_close_def_wrt_varref_rec_open_def_wrt_varref_rec_subst_defs_close_defs_wrt_varref_rec_open_defs_wrt_varref_rec_subst_val_close_val_wrt_varref_rec_open_val_wrt_varref_rec_subst_trm_close_trm_wrt_varref_rec_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_def_close_def_wrt_varref_rec_open_def_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_defs_close_defs_wrt_varref_rec_open_defs_wrt_varref_rec :
forall defs1 v1 x1 x2 n1,
  x2 `notin` fv_defs defs1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  degree_varref_wrt_varref n1 v1 ->
  subst_defs v1 x1 defs1 = close_defs_wrt_varref_rec n1 x2 (subst_defs v1 x1 (open_defs_wrt_varref_rec n1 (var_termvar_f x2) defs1)).
Proof.
pose proof subst_def_close_def_wrt_varref_rec_open_def_wrt_varref_rec_subst_defs_close_defs_wrt_varref_rec_open_defs_wrt_varref_rec_subst_val_close_val_wrt_varref_rec_open_val_wrt_varref_rec_subst_trm_close_trm_wrt_varref_rec_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_defs_close_defs_wrt_varref_rec_open_defs_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_val_close_val_wrt_varref_rec_open_val_wrt_varref_rec :
forall val1 v1 x1 x2 n1,
  x2 `notin` fv_val val1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  degree_varref_wrt_varref n1 v1 ->
  subst_val v1 x1 val1 = close_val_wrt_varref_rec n1 x2 (subst_val v1 x1 (open_val_wrt_varref_rec n1 (var_termvar_f x2) val1)).
Proof.
pose proof subst_def_close_def_wrt_varref_rec_open_def_wrt_varref_rec_subst_defs_close_defs_wrt_varref_rec_open_defs_wrt_varref_rec_subst_val_close_val_wrt_varref_rec_open_val_wrt_varref_rec_subst_trm_close_trm_wrt_varref_rec_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_val_close_val_wrt_varref_rec_open_val_wrt_varref_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_trm_close_trm_wrt_varref_rec_open_trm_wrt_varref_rec :
forall t1 v1 x1 x2 n1,
  x2 `notin` fv_trm t1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  degree_varref_wrt_varref n1 v1 ->
  subst_trm v1 x1 t1 = close_trm_wrt_varref_rec n1 x2 (subst_trm v1 x1 (open_trm_wrt_varref_rec n1 (var_termvar_f x2) t1)).
Proof.
pose proof subst_def_close_def_wrt_varref_rec_open_def_wrt_varref_rec_subst_defs_close_defs_wrt_varref_rec_open_defs_wrt_varref_rec_subst_val_close_val_wrt_varref_rec_open_val_wrt_varref_rec_subst_trm_close_trm_wrt_varref_rec_open_trm_wrt_varref_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_trm_close_trm_wrt_varref_rec_open_trm_wrt_varref_rec : lngen.

(* end hide *)

Lemma subst_varref_close_varref_wrt_varref_open_varref_wrt_varref :
forall v2 v1 x1 x2,
  x2 `notin` fv_varref v2 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  lc_varref v1 ->
  subst_varref v1 x1 v2 = close_varref_wrt_varref x2 (subst_varref v1 x1 (open_varref_wrt_varref v2 (var_termvar_f x2))).
Proof.
unfold close_varref_wrt_varref; unfold open_varref_wrt_varref; default_simp.
Qed.

Hint Resolve subst_varref_close_varref_wrt_varref_open_varref_wrt_varref : lngen.

Lemma subst_typ_close_typ_wrt_varref_open_typ_wrt_varref :
forall T1 v1 x1 x2,
  x2 `notin` fv_typ T1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  lc_varref v1 ->
  subst_typ v1 x1 T1 = close_typ_wrt_varref x2 (subst_typ v1 x1 (open_typ_wrt_varref T1 (var_termvar_f x2))).
Proof.
unfold close_typ_wrt_varref; unfold open_typ_wrt_varref; default_simp.
Qed.

Hint Resolve subst_typ_close_typ_wrt_varref_open_typ_wrt_varref : lngen.

Lemma subst_dec_close_dec_wrt_varref_open_dec_wrt_varref :
forall dec1 v1 x1 x2,
  x2 `notin` fv_dec dec1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  lc_varref v1 ->
  subst_dec v1 x1 dec1 = close_dec_wrt_varref x2 (subst_dec v1 x1 (open_dec_wrt_varref dec1 (var_termvar_f x2))).
Proof.
unfold close_dec_wrt_varref; unfold open_dec_wrt_varref; default_simp.
Qed.

Hint Resolve subst_dec_close_dec_wrt_varref_open_dec_wrt_varref : lngen.

Lemma subst_def_close_def_wrt_varref_open_def_wrt_varref :
forall d1 v1 x1 x2,
  x2 `notin` fv_def d1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  lc_varref v1 ->
  subst_def v1 x1 d1 = close_def_wrt_varref x2 (subst_def v1 x1 (open_def_wrt_varref d1 (var_termvar_f x2))).
Proof.
unfold close_def_wrt_varref; unfold open_def_wrt_varref; default_simp.
Qed.

Hint Resolve subst_def_close_def_wrt_varref_open_def_wrt_varref : lngen.

Lemma subst_defs_close_defs_wrt_varref_open_defs_wrt_varref :
forall defs1 v1 x1 x2,
  x2 `notin` fv_defs defs1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  lc_varref v1 ->
  subst_defs v1 x1 defs1 = close_defs_wrt_varref x2 (subst_defs v1 x1 (open_defs_wrt_varref defs1 (var_termvar_f x2))).
Proof.
unfold close_defs_wrt_varref; unfold open_defs_wrt_varref; default_simp.
Qed.

Hint Resolve subst_defs_close_defs_wrt_varref_open_defs_wrt_varref : lngen.

Lemma subst_val_close_val_wrt_varref_open_val_wrt_varref :
forall val1 v1 x1 x2,
  x2 `notin` fv_val val1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  lc_varref v1 ->
  subst_val v1 x1 val1 = close_val_wrt_varref x2 (subst_val v1 x1 (open_val_wrt_varref val1 (var_termvar_f x2))).
Proof.
unfold close_val_wrt_varref; unfold open_val_wrt_varref; default_simp.
Qed.

Hint Resolve subst_val_close_val_wrt_varref_open_val_wrt_varref : lngen.

Lemma subst_trm_close_trm_wrt_varref_open_trm_wrt_varref :
forall t1 v1 x1 x2,
  x2 `notin` fv_trm t1 ->
  x2 `notin` fv_varref v1 ->
  x2 <> x1 ->
  lc_varref v1 ->
  subst_trm v1 x1 t1 = close_trm_wrt_varref x2 (subst_trm v1 x1 (open_trm_wrt_varref t1 (var_termvar_f x2))).
Proof.
unfold close_trm_wrt_varref; unfold open_trm_wrt_varref; default_simp.
Qed.

Hint Resolve subst_trm_close_trm_wrt_varref_open_trm_wrt_varref : lngen.

Lemma subst_typ_typ_all :
forall x2 T1 T2 v1 x1,
  lc_varref v1 ->
  x2 `notin` fv_varref v1 `union` fv_typ T2 `union` singleton x1 ->
  subst_typ v1 x1 (typ_all T1 T2) = typ_all (subst_typ v1 x1 T1) (close_typ_wrt_varref x2 (subst_typ v1 x1 (open_typ_wrt_varref T2 (var_termvar_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_typ_typ_all : lngen.

Lemma subst_typ_typ_bnd :
forall x2 T1 v1 x1,
  lc_varref v1 ->
  x2 `notin` fv_varref v1 `union` fv_typ T1 `union` singleton x1 ->
  subst_typ v1 x1 (typ_bnd T1) = typ_bnd (close_typ_wrt_varref x2 (subst_typ v1 x1 (open_typ_wrt_varref T1 (var_termvar_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_typ_typ_bnd : lngen.

Lemma subst_val_val_new :
forall x2 T1 defs1 v1 x1,
  lc_varref v1 ->
  x2 `notin` fv_varref v1 `union` fv_defs defs1 `union` singleton x1 ->
  subst_val v1 x1 (val_new T1 defs1) = val_new (subst_typ v1 x1 T1) (close_defs_wrt_varref x2 (subst_defs v1 x1 (open_defs_wrt_varref defs1 (var_termvar_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_val_val_new : lngen.

Lemma subst_val_val_lambda :
forall x2 T1 t1 v1 x1,
  lc_varref v1 ->
  x2 `notin` fv_varref v1 `union` fv_trm t1 `union` singleton x1 ->
  subst_val v1 x1 (val_lambda T1 t1) = val_lambda (subst_typ v1 x1 T1) (close_trm_wrt_varref x2 (subst_trm v1 x1 (open_trm_wrt_varref t1 (var_termvar_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_val_val_lambda : lngen.

Lemma subst_trm_trm_let :
forall x2 t1 t2 v1 x1,
  lc_varref v1 ->
  x2 `notin` fv_varref v1 `union` fv_trm t2 `union` singleton x1 ->
  subst_trm v1 x1 (trm_let t1 t2) = trm_let (subst_trm v1 x1 t1) (close_trm_wrt_varref x2 (subst_trm v1 x1 (open_trm_wrt_varref t2 (var_termvar_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_trm_trm_let : lngen.

(* begin hide *)

Lemma subst_varref_intro_rec_mutual :
(forall v1 x1 v2 n1,
  x1 `notin` fv_varref v1 ->
  open_varref_wrt_varref_rec n1 v2 v1 = subst_varref v2 x1 (open_varref_wrt_varref_rec n1 (var_termvar_f x1) v1)).
Proof.
apply_mutual_ind varref_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_varref_intro_rec :
forall v1 x1 v2 n1,
  x1 `notin` fv_varref v1 ->
  open_varref_wrt_varref_rec n1 v2 v1 = subst_varref v2 x1 (open_varref_wrt_varref_rec n1 (var_termvar_f x1) v1).
Proof.
pose proof subst_varref_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_varref_intro_rec : lngen.
Hint Rewrite subst_varref_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_intro_rec_subst_dec_intro_rec_mutual :
(forall T1 x1 v1 n1,
  x1 `notin` fv_typ T1 ->
  open_typ_wrt_varref_rec n1 v1 T1 = subst_typ v1 x1 (open_typ_wrt_varref_rec n1 (var_termvar_f x1) T1)) /\
(forall dec1 x1 v1 n1,
  x1 `notin` fv_dec dec1 ->
  open_dec_wrt_varref_rec n1 v1 dec1 = subst_dec v1 x1 (open_dec_wrt_varref_rec n1 (var_termvar_f x1) dec1)).
Proof.
apply_mutual_ind typ_dec_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_intro_rec :
forall T1 x1 v1 n1,
  x1 `notin` fv_typ T1 ->
  open_typ_wrt_varref_rec n1 v1 T1 = subst_typ v1 x1 (open_typ_wrt_varref_rec n1 (var_termvar_f x1) T1).
Proof.
pose proof subst_typ_intro_rec_subst_dec_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_typ_intro_rec : lngen.
Hint Rewrite subst_typ_intro_rec using solve [auto] : lngen.

Lemma subst_dec_intro_rec :
forall dec1 x1 v1 n1,
  x1 `notin` fv_dec dec1 ->
  open_dec_wrt_varref_rec n1 v1 dec1 = subst_dec v1 x1 (open_dec_wrt_varref_rec n1 (var_termvar_f x1) dec1).
Proof.
pose proof subst_typ_intro_rec_subst_dec_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dec_intro_rec : lngen.
Hint Rewrite subst_dec_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_def_intro_rec_subst_defs_intro_rec_subst_val_intro_rec_subst_trm_intro_rec_mutual :
(forall d1 x1 v1 n1,
  x1 `notin` fv_def d1 ->
  open_def_wrt_varref_rec n1 v1 d1 = subst_def v1 x1 (open_def_wrt_varref_rec n1 (var_termvar_f x1) d1)) /\
(forall defs1 x1 v1 n1,
  x1 `notin` fv_defs defs1 ->
  open_defs_wrt_varref_rec n1 v1 defs1 = subst_defs v1 x1 (open_defs_wrt_varref_rec n1 (var_termvar_f x1) defs1)) /\
(forall val1 x1 v1 n1,
  x1 `notin` fv_val val1 ->
  open_val_wrt_varref_rec n1 v1 val1 = subst_val v1 x1 (open_val_wrt_varref_rec n1 (var_termvar_f x1) val1)) /\
(forall t1 x1 v1 n1,
  x1 `notin` fv_trm t1 ->
  open_trm_wrt_varref_rec n1 v1 t1 = subst_trm v1 x1 (open_trm_wrt_varref_rec n1 (var_termvar_f x1) t1)).
Proof.
apply_mutual_ind def_defs_val_trm_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_def_intro_rec :
forall d1 x1 v1 n1,
  x1 `notin` fv_def d1 ->
  open_def_wrt_varref_rec n1 v1 d1 = subst_def v1 x1 (open_def_wrt_varref_rec n1 (var_termvar_f x1) d1).
Proof.
pose proof subst_def_intro_rec_subst_defs_intro_rec_subst_val_intro_rec_subst_trm_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_def_intro_rec : lngen.
Hint Rewrite subst_def_intro_rec using solve [auto] : lngen.

Lemma subst_defs_intro_rec :
forall defs1 x1 v1 n1,
  x1 `notin` fv_defs defs1 ->
  open_defs_wrt_varref_rec n1 v1 defs1 = subst_defs v1 x1 (open_defs_wrt_varref_rec n1 (var_termvar_f x1) defs1).
Proof.
pose proof subst_def_intro_rec_subst_defs_intro_rec_subst_val_intro_rec_subst_trm_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_defs_intro_rec : lngen.
Hint Rewrite subst_defs_intro_rec using solve [auto] : lngen.

Lemma subst_val_intro_rec :
forall val1 x1 v1 n1,
  x1 `notin` fv_val val1 ->
  open_val_wrt_varref_rec n1 v1 val1 = subst_val v1 x1 (open_val_wrt_varref_rec n1 (var_termvar_f x1) val1).
Proof.
pose proof subst_def_intro_rec_subst_defs_intro_rec_subst_val_intro_rec_subst_trm_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_val_intro_rec : lngen.
Hint Rewrite subst_val_intro_rec using solve [auto] : lngen.

Lemma subst_trm_intro_rec :
forall t1 x1 v1 n1,
  x1 `notin` fv_trm t1 ->
  open_trm_wrt_varref_rec n1 v1 t1 = subst_trm v1 x1 (open_trm_wrt_varref_rec n1 (var_termvar_f x1) t1).
Proof.
pose proof subst_def_intro_rec_subst_defs_intro_rec_subst_val_intro_rec_subst_trm_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_trm_intro_rec : lngen.
Hint Rewrite subst_trm_intro_rec using solve [auto] : lngen.

Lemma subst_varref_intro :
forall x1 v1 v2,
  x1 `notin` fv_varref v1 ->
  open_varref_wrt_varref v1 v2 = subst_varref v2 x1 (open_varref_wrt_varref v1 (var_termvar_f x1)).
Proof.
unfold open_varref_wrt_varref; default_simp.
Qed.

Hint Resolve subst_varref_intro : lngen.

Lemma subst_typ_intro :
forall x1 T1 v1,
  x1 `notin` fv_typ T1 ->
  open_typ_wrt_varref T1 v1 = subst_typ v1 x1 (open_typ_wrt_varref T1 (var_termvar_f x1)).
Proof.
unfold open_typ_wrt_varref; default_simp.
Qed.

Hint Resolve subst_typ_intro : lngen.

Lemma subst_dec_intro :
forall x1 dec1 v1,
  x1 `notin` fv_dec dec1 ->
  open_dec_wrt_varref dec1 v1 = subst_dec v1 x1 (open_dec_wrt_varref dec1 (var_termvar_f x1)).
Proof.
unfold open_dec_wrt_varref; default_simp.
Qed.

Hint Resolve subst_dec_intro : lngen.

Lemma subst_def_intro :
forall x1 d1 v1,
  x1 `notin` fv_def d1 ->
  open_def_wrt_varref d1 v1 = subst_def v1 x1 (open_def_wrt_varref d1 (var_termvar_f x1)).
Proof.
unfold open_def_wrt_varref; default_simp.
Qed.

Hint Resolve subst_def_intro : lngen.

Lemma subst_defs_intro :
forall x1 defs1 v1,
  x1 `notin` fv_defs defs1 ->
  open_defs_wrt_varref defs1 v1 = subst_defs v1 x1 (open_defs_wrt_varref defs1 (var_termvar_f x1)).
Proof.
unfold open_defs_wrt_varref; default_simp.
Qed.

Hint Resolve subst_defs_intro : lngen.

Lemma subst_val_intro :
forall x1 val1 v1,
  x1 `notin` fv_val val1 ->
  open_val_wrt_varref val1 v1 = subst_val v1 x1 (open_val_wrt_varref val1 (var_termvar_f x1)).
Proof.
unfold open_val_wrt_varref; default_simp.
Qed.

Hint Resolve subst_val_intro : lngen.

Lemma subst_trm_intro :
forall x1 t1 v1,
  x1 `notin` fv_trm t1 ->
  open_trm_wrt_varref t1 v1 = subst_trm v1 x1 (open_trm_wrt_varref t1 (var_termvar_f x1)).
Proof.
unfold open_trm_wrt_varref; default_simp.
Qed.

Hint Resolve subst_trm_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
