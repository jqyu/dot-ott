(* generated by Ott 0.27, locally-nameless lngen from: DOT.ott *)
Require Import Metalib.Metatheory.
(** syntax *)
Definition termvar := var.
Definition trmlabel := nat.
Definition typlabel := nat.

Inductive varref : Set := 
 | var_termvar_b (_:nat)
 | var_termvar_f (x:termvar).

Inductive typ : Set := 
 | typ_all (T1:typ) (T2:typ)
 | typ_bnd (T:typ)
 | typ_dec (dec5:dec)
 | typ_sel (v:varref) (A:typlabel)
 | typ_and (T1:typ) (T2:typ)
 | typ_top : typ
 | typ_bot : typ
with dec : Set := 
 | dec_trm (a:trmlabel) (T:typ)
 | dec_typ (A:typlabel) (T1:typ) (T2:typ).

Inductive trm : Set := 
 | trm_var (v:varref)
 | trm_val (val5:val)
 | trm_sel (v:varref) (a:trmlabel)
 | trm_app (v1:varref) (v2:varref)
 | trm_let (t1:trm) (t2:trm)
with val : Set := 
 | val_new (T:typ) (defs5:defs)
 | val_lambda (T:typ) (t:trm)
with defs : Set := 
 | defs_nil : defs
 | defs_cons (d:def) (defs5:defs)
with def : Set := 
 | def_trm (a:trmlabel) (t:trm)
 | def_typ (A:typlabel) (T:typ).

Definition ctx : Set := list (atom*typ).

Definition stack : Set := list (atom*trm).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Definition open_varref_wrt_varref_rec (k:nat) (v5:varref) (v_6:varref) : varref :=
  match v_6 with
  | (var_termvar_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => var_termvar_b nat
        | inleft (right _) => v5
        | inright _ => var_termvar_b (nat - 1)
      end
  | (var_termvar_f x) => var_termvar_f x
end.

Fixpoint open_dec_wrt_varref_rec (k:nat) (v5:varref) (dec5:dec) : dec :=
  match dec5 with
  | (dec_trm a T) => dec_trm a (open_typ_wrt_varref_rec k v5 T)
  | (dec_typ A T1 T2) => dec_typ A (open_typ_wrt_varref_rec k v5 T1) (open_typ_wrt_varref_rec k v5 T2)
end
with open_typ_wrt_varref_rec (k:nat) (v5:varref) (T_5:typ) {struct T_5}: typ :=
  match T_5 with
  | (typ_all T1 T2) => typ_all (open_typ_wrt_varref_rec k v5 T1) (open_typ_wrt_varref_rec (S k) v5 T2)
  | (typ_bnd T) => typ_bnd (open_typ_wrt_varref_rec (S k) v5 T)
  | (typ_dec dec5) => typ_dec (open_dec_wrt_varref_rec k v5 dec5)
  | (typ_sel v A) => typ_sel (open_varref_wrt_varref_rec k v5 v) A
  | (typ_and T1 T2) => typ_and (open_typ_wrt_varref_rec k v5 T1) (open_typ_wrt_varref_rec k v5 T2)
  | typ_top => typ_top 
  | typ_bot => typ_bot 
end.

Fixpoint open_def_wrt_varref_rec (k:nat) (v5:varref) (d5:def) : def :=
  match d5 with
  | (def_trm a t) => def_trm a (open_trm_wrt_varref_rec k v5 t)
  | (def_typ A T) => def_typ A (open_typ_wrt_varref_rec k v5 T)
end
with open_defs_wrt_varref_rec (k:nat) (v5:varref) (defs_6:defs) {struct defs_6}: defs :=
  match defs_6 with
  | defs_nil => defs_nil 
  | (defs_cons d defs5) => defs_cons (open_def_wrt_varref_rec k v5 d) (open_defs_wrt_varref_rec k v5 defs5)
end
with open_val_wrt_varref_rec (k:nat) (v5:varref) (val5:val) : val :=
  match val5 with
  | (val_new T defs5) => val_new (open_typ_wrt_varref_rec k v5 T) (open_defs_wrt_varref_rec (S k) v5 defs5)
  | (val_lambda T t) => val_lambda (open_typ_wrt_varref_rec k v5 T) (open_trm_wrt_varref_rec (S k) v5 t)
end
with open_trm_wrt_varref_rec (k:nat) (v_5:varref) (t_5:trm) {struct t_5}: trm :=
  match t_5 with
  | (trm_var v) => trm_var (open_varref_wrt_varref_rec k v_5 v)
  | (trm_val val5) => trm_val (open_val_wrt_varref_rec k v_5 val5)
  | (trm_sel v a) => trm_sel (open_varref_wrt_varref_rec k v_5 v) a
  | (trm_app v1 v2) => trm_app (open_varref_wrt_varref_rec k v_5 v1) (open_varref_wrt_varref_rec k v_5 v2)
  | (trm_let t1 t2) => trm_let (open_trm_wrt_varref_rec k v_5 t1) (open_trm_wrt_varref_rec (S k) v_5 t2)
end.

Definition open_def_wrt_varref v5 d5 := open_def_wrt_varref_rec 0 d5 v5.

Definition open_val_wrt_varref v5 val5 := open_val_wrt_varref_rec 0 val5 v5.

Definition open_defs_wrt_varref v5 defs_6 := open_defs_wrt_varref_rec 0 defs_6 v5.

Definition open_dec_wrt_varref v5 dec5 := open_dec_wrt_varref_rec 0 dec5 v5.

Definition open_varref_wrt_varref v5 v_6 := open_varref_wrt_varref_rec 0 v_6 v5.

Definition open_typ_wrt_varref v5 T_5 := open_typ_wrt_varref_rec 0 T_5 v5.

Definition open_trm_wrt_varref v_5 t_5 := open_trm_wrt_varref_rec 0 t_5 v_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_varref *)
Inductive lc_varref : varref -> Prop :=    (* defn lc_varref *)
 | lc_var_termvar_f : forall (x:termvar),
     (lc_varref (var_termvar_f x)).

(* defns LC_dec_typ *)
Inductive lc_dec : dec -> Prop :=    (* defn lc_dec *)
 | lc_dec_trm : forall (a:trmlabel) (T:typ),
     (lc_typ T) ->
     (lc_dec (dec_trm a T))
 | lc_dec_typ : forall (A:typlabel) (T1 T2:typ),
     (lc_typ T1) ->
     (lc_typ T2) ->
     (lc_dec (dec_typ A T1 T2))
with lc_typ : typ -> Prop :=    (* defn lc_typ *)
 | lc_typ_all : forall (T1 T2:typ),
     (lc_typ T1) ->
      ( forall x , lc_typ  ( open_typ_wrt_varref T2 (var_termvar_f x) )  )  ->
     (lc_typ (typ_all T1 T2))
 | lc_typ_bnd : forall (T:typ),
      ( forall x , lc_typ  ( open_typ_wrt_varref T (var_termvar_f x) )  )  ->
     (lc_typ (typ_bnd T))
 | lc_typ_dec : forall (dec5:dec),
     (lc_dec dec5) ->
     (lc_typ (typ_dec dec5))
 | lc_typ_sel : forall (v:varref) (A:typlabel),
     (lc_varref v) ->
     (lc_typ (typ_sel v A))
 | lc_typ_and : forall (T1 T2:typ),
     (lc_typ T1) ->
     (lc_typ T2) ->
     (lc_typ (typ_and T1 T2))
 | lc_typ_top : 
     (lc_typ typ_top)
 | lc_typ_bot : 
     (lc_typ typ_bot).

(* defns LC_def_defs_val_trm *)
Inductive lc_def : def -> Prop :=    (* defn lc_def *)
 | lc_def_trm : forall (a:trmlabel) (t:trm),
     (lc_trm t) ->
     (lc_def (def_trm a t))
 | lc_def_typ : forall (A:typlabel) (T:typ),
     (lc_typ T) ->
     (lc_def (def_typ A T))
with lc_defs : defs -> Prop :=    (* defn lc_defs *)
 | lc_defs_nil : 
     (lc_defs defs_nil)
 | lc_defs_cons : forall (d:def) (defs5:defs),
     (lc_def d) ->
     (lc_defs defs5) ->
     (lc_defs (defs_cons d defs5))
with lc_val : val -> Prop :=    (* defn lc_val *)
 | lc_val_new : forall (T:typ) (defs5:defs),
     (lc_typ T) ->
      ( forall x , lc_defs  ( open_defs_wrt_varref defs5 (var_termvar_f x) )  )  ->
     (lc_val (val_new T defs5))
 | lc_val_lambda : forall (T:typ) (t:trm),
     (lc_typ T) ->
      ( forall x , lc_trm  ( open_trm_wrt_varref t (var_termvar_f x) )  )  ->
     (lc_val (val_lambda T t))
with lc_trm : trm -> Prop :=    (* defn lc_trm *)
 | lc_trm_var : forall (v:varref),
     (lc_varref v) ->
     (lc_trm (trm_var v))
 | lc_trm_val : forall (val5:val),
     (lc_val val5) ->
     (lc_trm (trm_val val5))
 | lc_trm_sel : forall (v:varref) (a:trmlabel),
     (lc_varref v) ->
     (lc_trm (trm_sel v a))
 | lc_trm_app : forall (v1 v2:varref),
     (lc_varref v1) ->
     (lc_varref v2) ->
     (lc_trm (trm_app v1 v2))
 | lc_trm_let : forall (t1 t2:trm),
     (lc_trm t1) ->
      ( forall x , lc_trm  ( open_trm_wrt_varref t2 (var_termvar_f x) )  )  ->
     (lc_trm (trm_let t1 t2)).
(** free variables *)
Definition fv_varref (v5:varref) : vars :=
  match v5 with
  | (var_termvar_b nat) => {}
  | (var_termvar_f x) => {{x}}
end.

Fixpoint fv_dec (dec5:dec) : vars :=
  match dec5 with
  | (dec_trm a T) => (fv_typ T)
  | (dec_typ A T1 T2) => (fv_typ T1) \u (fv_typ T2)
end
with fv_typ (T_5:typ) : vars :=
  match T_5 with
  | (typ_all T1 T2) => (fv_typ T1) \u (fv_typ T2)
  | (typ_bnd T) => (fv_typ T)
  | (typ_dec dec5) => (fv_dec dec5)
  | (typ_sel v A) => (fv_varref v)
  | (typ_and T1 T2) => (fv_typ T1) \u (fv_typ T2)
  | typ_top => {}
  | typ_bot => {}
end.

Fixpoint fv_def (d5:def) : vars :=
  match d5 with
  | (def_trm a t) => (fv_trm t)
  | (def_typ A T) => (fv_typ T)
end
with fv_defs (defs_6:defs) : vars :=
  match defs_6 with
  | defs_nil => {}
  | (defs_cons d defs5) => (fv_def d) \u (fv_defs defs5)
end
with fv_val (val5:val) : vars :=
  match val5 with
  | (val_new T defs5) => (fv_typ T) \u (fv_defs defs5)
  | (val_lambda T t) => (fv_typ T) \u (fv_trm t)
end
with fv_trm (t_5:trm) : vars :=
  match t_5 with
  | (trm_var v) => (fv_varref v)
  | (trm_val val5) => (fv_val val5)
  | (trm_sel v a) => (fv_varref v)
  | (trm_app v1 v2) => (fv_varref v1) \u (fv_varref v2)
  | (trm_let t1 t2) => (fv_trm t1) \u (fv_trm t2)
end.

(** substitutions *)
Definition subst_varref (v5:varref) (x5:termvar) (v_6:varref) : varref :=
  match v_6 with
  | (var_termvar_b nat) => var_termvar_b nat
  | (var_termvar_f x) => (if eq_var x x5 then v5 else (var_termvar_f x))
end.

Fixpoint subst_dec (v5:varref) (x5:termvar) (dec5:dec) {struct dec5} : dec :=
  match dec5 with
  | (dec_trm a T) => dec_trm a (subst_typ v5 x5 T)
  | (dec_typ A T1 T2) => dec_typ A (subst_typ v5 x5 T1) (subst_typ v5 x5 T2)
end
with subst_typ (v5:varref) (x5:termvar) (T_5:typ) {struct T_5} : typ :=
  match T_5 with
  | (typ_all T1 T2) => typ_all (subst_typ v5 x5 T1) (subst_typ v5 x5 T2)
  | (typ_bnd T) => typ_bnd (subst_typ v5 x5 T)
  | (typ_dec dec5) => typ_dec (subst_dec v5 x5 dec5)
  | (typ_sel v A) => typ_sel (subst_varref v5 x5 v) A
  | (typ_and T1 T2) => typ_and (subst_typ v5 x5 T1) (subst_typ v5 x5 T2)
  | typ_top => typ_top 
  | typ_bot => typ_bot 
end.

Fixpoint subst_def (v5:varref) (x5:termvar) (d5:def) {struct d5} : def :=
  match d5 with
  | (def_trm a t) => def_trm a (subst_trm v5 x5 t)
  | (def_typ A T) => def_typ A (subst_typ v5 x5 T)
end
with subst_defs (v5:varref) (x5:termvar) (defs_6:defs) {struct defs_6} : defs :=
  match defs_6 with
  | defs_nil => defs_nil 
  | (defs_cons d defs5) => defs_cons (subst_def v5 x5 d) (subst_defs v5 x5 defs5)
end
with subst_val (v5:varref) (x5:termvar) (val5:val) {struct val5} : val :=
  match val5 with
  | (val_new T defs5) => val_new (subst_typ v5 x5 T) (subst_defs v5 x5 defs5)
  | (val_lambda T t) => val_lambda (subst_typ v5 x5 T) (subst_trm v5 x5 t)
end
with subst_trm (v_5:varref) (x5:termvar) (t_5:trm) {struct t_5} : trm :=
  match t_5 with
  | (trm_var v) => trm_var (subst_varref v_5 x5 v)
  | (trm_val val5) => trm_val (subst_val v_5 x5 val5)
  | (trm_sel v a) => trm_sel (subst_varref v_5 x5 v) a
  | (trm_app v1 v2) => trm_app (subst_varref v_5 x5 v1) (subst_varref v_5 x5 v2)
  | (trm_let t1 t2) => trm_let (subst_trm v_5 x5 t1) (subst_trm v_5 x5 t2)
end.


Fixpoint defs_has (ds: defs) (d: def) : Prop :=
  match ds with
  | defs_nil => False
  | defs_cons d' ds' =>
      d' = d \/ defs_has ds' d
  end.


(** definitions *)

(* defns Jtyping *)
Inductive ty_trm : ctx -> trm -> typ -> Prop :=    (* defn ty_trm *)
 | ty_var : forall (G:ctx) (x:termvar) (T:typ),
      (binds ( x ) ( T ) ( G ))  ->
     ty_trm G (trm_var (var_termvar_f x)) T
 | ty_all_intro : forall (L:vars) (G:ctx) (T1:typ) (t:trm) (T2:typ),
      ( forall x , x \notin  L  -> ty_trm  ( x ~ T1  ++  G )   ( open_trm_wrt_varref t (var_termvar_f x) )   ( open_typ_wrt_varref T2 (var_termvar_f x) )  )  ->
     ty_trm G (trm_val (val_lambda T1 t)) (typ_all T1 T2)
 | ty_all_elim : forall (G:ctx) (x y:termvar) (T2 T1:typ),
     ty_trm G (trm_var (var_termvar_f x)) (typ_all T1 T2) ->
     ty_trm G (trm_var (var_termvar_f y)) T1 ->
     ty_trm G (trm_app (var_termvar_f x) (var_termvar_f y))  (open_typ_wrt_varref  T2   (var_termvar_f y) ) 
 | ty_new_intro : forall (L:vars) (G:ctx) (T:typ) (defs5:defs),
      ( forall x , x \notin  L  -> ty_defs  ( x ~  (open_typ_wrt_varref  T   (var_termvar_f x) )   ++  G )   ( open_defs_wrt_varref defs5 (var_termvar_f x) )   ( open_typ_wrt_varref T (var_termvar_f x) )  )  ->
      ( forall x , x \notin  L  -> ty_trm G (trm_val (val_new  ( open_typ_wrt_varref T (var_termvar_f x) )  defs5)) (typ_bnd T) ) 
 | ty_new_elim : forall (G:ctx) (x:termvar) (a:trmlabel) (T:typ),
     ty_trm G (trm_var (var_termvar_f x)) (typ_dec (dec_trm a T)) ->
     ty_trm G (trm_sel (var_termvar_f x) a) T
 | ty_let : forall (L:vars) (G:ctx) (t1 t2:trm) (T2 T1:typ),
     ty_trm G t1 T1 ->
      ( forall x , x \notin  L  -> ty_trm  ( x ~ T1  ++  G )   ( open_trm_wrt_varref t2 (var_termvar_f x) )  T2 )  ->
     ty_trm G (trm_let t1 t2) T2
 | ty_rec_intro : forall (L:vars) (G:ctx) (x:termvar) (T:typ),
      ( forall z , z \notin  L  -> ty_trm G (trm_var (var_termvar_f x))  ( open_typ_wrt_varref T (var_termvar_f z) )  )  ->
     ty_trm G (trm_var (var_termvar_f x)) (typ_bnd T)
 | ty_rec_elim : forall (G:ctx) (x:termvar) (T:typ),
     ty_trm G (trm_var (var_termvar_f x)) (typ_bnd T) ->
     ty_trm G (trm_var (var_termvar_f x))  (open_typ_wrt_varref  T   (var_termvar_f x) ) 
 | ty_and_intro : forall (G:ctx) (x:termvar) (T1 T2:typ),
     ty_trm G (trm_var (var_termvar_f x)) T1 ->
     ty_trm G (trm_var (var_termvar_f x)) T2 ->
     ty_trm G (trm_var (var_termvar_f x)) (typ_and T1 T2)
 | ty_sub : forall (G:ctx) (t:trm) (T2 T1:typ),
     ty_trm G t T1 ->
     subtyp G T1 T2 ->
     ty_trm G t T2
with ty_def : ctx -> def -> typ -> Prop :=    (* defn ty_def *)
 | ty_def_trm : forall (G:ctx) (a:trmlabel) (t:trm) (T:typ),
     ty_trm G t T ->
     ty_def G (def_trm a t) (typ_dec (dec_trm a T))
 | ty_def_typ : forall (G:ctx) (A:typlabel) (T:typ),
     lc_typ T ->
     ty_def G (def_typ A T) (typ_dec (dec_typ A T T))
with ty_defs : ctx -> defs -> typ -> Prop :=    (* defn ty_defs *)
 | ty_defs_one : forall (G:ctx) (d:def) (T:typ),
     ty_def G d T ->
     ty_defs G (defs_cons d defs_nil) T
 | ty_defs_cons : forall (G:ctx) (d:def) (defs5:defs) (T1 T2:typ),
     ty_def G d T1 ->
     ty_defs G defs5 T2 ->
     ty_defs G (defs_cons d defs5) (typ_and T1 T2)
with subtyp : ctx -> typ -> typ -> Prop :=    (* defn subtyp *)
 | subtyp_top : forall (G:ctx) (T:typ),
     lc_typ T ->
     subtyp G T typ_top
 | subtyp_bot : forall (G:ctx) (T:typ),
     lc_typ T ->
     subtyp G typ_bot T
 | subtyp_refl : forall (G:ctx) (T:typ),
     lc_typ T ->
     subtyp G T T
 | subtyp_trans : forall (G:ctx) (T1 T3 T2:typ),
     subtyp G T1 T2 ->
     subtyp G T2 T3 ->
     subtyp G T1 T3
 | subtyp_and11 : forall (G:ctx) (T1 T2:typ),
     lc_typ T2 ->
     lc_typ T1 ->
     subtyp G (typ_and T1 T2) T1
 | subtyp_and12 : forall (G:ctx) (T1 T2:typ),
     lc_typ T1 ->
     lc_typ T2 ->
     subtyp G (typ_and T1 T2) T2
 | subtyp_and2 : forall (G:ctx) (T1 T2 T3:typ),
     subtyp G T1 T2 ->
     subtyp G T1 T3 ->
     subtyp G T1 (typ_and T2 T3)
 | subtyp_fld : forall (G:ctx) (a:trmlabel) (T1 T2:typ),
     subtyp G T1 T2 ->
     subtyp G (typ_dec (dec_trm a T1)) (typ_dec (dec_trm a T2))
 | subtyp_typ : forall (G:ctx) (A:typlabel) (T2 T3 T1 T4:typ),
     subtyp G T1 T2 ->
     subtyp G T3 T4 ->
     subtyp G (typ_dec (dec_typ A T2 T3)) (typ_dec (dec_typ A T1 T4))
 | subtyp_sel1 : forall (G:ctx) (x:termvar) (A:typlabel) (T2 T1:typ),
     ty_trm G (trm_var (var_termvar_f x)) (typ_dec (dec_typ A T1 T2)) ->
     subtyp G (typ_sel (var_termvar_f x) A) T2
 | subtyp_sel2 : forall (G:ctx) (T1:typ) (x:termvar) (A:typlabel) (T2:typ),
     ty_trm G (trm_var (var_termvar_f x)) (typ_dec (dec_typ A T1 T2)) ->
     subtyp G T1 (typ_sel (var_termvar_f x) A)
 | subtyp_forall : forall (L:vars) (G:ctx) (T1 T2 T3 T4:typ),
     subtyp G T3 T1 ->
      ( forall x , x \notin  L  -> subtyp  ( x ~ T1  ++  G )   ( open_typ_wrt_varref T2 (var_termvar_f x) )   ( open_typ_wrt_varref T4 (var_termvar_f x) )  )  ->
     subtyp G (typ_all T1 T2) (typ_all T3 T4).

(* defns Jop *)
Inductive red : stack -> trm -> stack -> trm -> Prop :=    (* defn red *)
 | red_sel : forall (s:stack) (x:termvar) (a:trmlabel) (t:trm) (T:typ) (defs5:defs),
      (binds ( x ) ( (trm_val (val_new T defs5)) ) ( s ))  ->
      (defs_has   (open_defs_wrt_varref  defs5   (var_termvar_f x) )    (def_trm a t) )  ->
     red s (trm_sel (var_termvar_f x) a) s t
 | red_app : forall (s:stack) (x y:termvar) (t:trm) (T1:typ),
      (binds ( x ) ( (trm_val (val_lambda T1 t)) ) ( s ))  ->
     red s (trm_app (var_termvar_f x) (var_termvar_f y)) s  (open_trm_wrt_varref  t   (var_termvar_f y) ) 
 | red_let_val : forall (L:vars) (s:stack) (val5:val) (t:trm),
     lc_trm (trm_let (trm_val val5) t) ->
     lc_val val5 ->
      ( forall x , x \notin  L  -> red s (trm_let (trm_val val5) t)  ( x ~ (trm_val val5)  ++  s )   ( open_trm_wrt_varref t (var_termvar_f x) )  ) 
 | red_let_var : forall (s:stack) (y:termvar) (t:trm),
     lc_trm (trm_let (trm_var (var_termvar_f y)) t) ->
     red s (trm_let (trm_var (var_termvar_f y)) t) s  (open_trm_wrt_varref  t   (var_termvar_f y) ) 
 | red_let_tgt : forall (s1:stack) (t1 t3:trm) (s2:stack) (t2:trm),
     lc_trm (trm_let t1 t3) ->
     red s1 t1 s2 t2 ->
     red s1 (trm_let t1 t3) s2 (trm_let t2 t3).


(** infrastructure *)
Hint Constructors ty_trm ty_def ty_defs subtyp red lc_varref lc_dec lc_typ lc_def lc_defs lc_val lc_trm.

