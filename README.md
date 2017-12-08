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
