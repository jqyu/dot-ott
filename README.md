# DOT in Ott

To run, ensure that the following are installed, then run `./build.sh`

## [metalib](https://github.com/jqyu/metalib)

Ensure that you have [Coq](https://coq.inria.fr/download) installed.

```bash
cd Metalib
make
make install
```

Metalib was modified in one place to fix a broken tactic.

## [lngen](https://github.com/jqyu/lngen)

Ensure that you have [stack](https://docs.haskellstack.org/en/stable/README/) installed.

```bash
stack install
```

Lngen was only modified to replace `Require Export Metatheory` with `Require Export Metalib.Metatheory`
as per the current naming conventions in [metalib](https://github.com/plclub/metalib).

## [ott](https://github.com/jqyu/ott)

```bash
make world
ln -s $(pwd)/bin/ott /user/local/bin/
```

Ott was modified to properly handle non-recursive rules referencing metavariables.

# Remaining Work

lngen does not know how to generate the correct code for multiple bind statements,
which means that the production rule
```
val :: 'val_' ::=
  | nu ( x : T ) defs :: :: new (+ bind x in defs+)
```
is currently incorrect since `x` should also be bound in `T`. Adding a second `(+ bind x in T +)` clause
will cause Ott to generate the correct code, but raises a warning saying that lngen does not support this.
Indeed, lngen will fail when encountering a production rule with 2 binds. The main consequence of that judgements that look like
```
( G , x : T ) |- defs : T
------------------------------------- :: new_intro
G |- nu ( x : T ) defs : mu ( x : T )
```
will incorrectly translate, since x is not bound to T, as
```coq
 | ty_new_intro : forall (L:vars) (G:ctx) (T:typ) (defs5:defs),
      ( forall x , x \notin  L  -> ty_defs  ( x ~  ( open_typ_wrt_varref T (var_termvar_f x) )   ++  G )   ( open_defs_wrt_varref defs5 (var_termvar_f x) )   ( open_typ_wrt_varref T (var_termvar_f x) )  )  ->
      ( forall x , x \notin  L  -> ty_trm G (trm_val (val_new  ( open_typ_wrt_varref T (var_termvar_f x) )  defs5)) (typ_bnd T) ) 
```
note the unnecessary second cofinite quantification, which does not occur if we add `(+ bind x in T +)`.

lngen will sometimes generate incorrect code code by silently failing on naming conflicts,
for example in the production rule
```
v1 v2 :: :: app
```
changing this rule to be
```
vx vy :: :: app
```
while adding the appropriate aliases to `varref` will cause lngen to generate incorrect code.
