#!/bin/bash
set -e

LIB=./lib
SRC=./src

cd $LIB
mkdir -p $SRC

LIBS="https://github.com/mattam82/Coq-Equations/archive/8.4.zip,Coq-Equations-8.4.zip \
      http://www.cis.upenn.edu/~plclub/metalib/dists/metalib-20090714.zip,metalib-20090714.zip \
      http://adam.chlipala.net/cpdt/cpdtlib.tgz,cpdtlib.tgz \
      http://coq.inria.fr/distrib/8.2/contribs/files/GraphBasics.tar.gz,GraphBasics.tgz \
      http://compcert.inria.fr/release/compcert-1.9.tgz,compcert-1.9.tgz"

prep_Coq-Equations-8.4() {
    unzip -qqo $SRC/$1
    patch -p1 < ../patch/equations.patch
    make -C Coq-Equations-8.4 >> log
}

prep_metalib-20090714() {
    unzip -qqo $SRC/$1
    patch -p1 < ../patch/metalib.patch
    make -C metalib-20090714 >> log
}

prep_cpdtlib() {
    tar xzf $SRC/$1
    patch -p1 < ../patch/cpdtlib.patch
}

prep_GraphBasics() {
    tar xzf $SRC/$1
    patch -p1 < ../patch/graphbasics.patch
}

prep_compcert-1.9() {
    TMP=$(mktemp -dp.)
    tar xzf $SRC/$1
    cp compcert-1.9/common/{AST,Errors,Memdata,Memory,Memtype,Values}.v \
       compcert-1.9/lib/{Axioms,Coqlib,Floats,Integers,Intv,Iteration,Lattice,Maps,Ordered}.v \
       compcert-1.9/backend/Kildall.v \
       $TMP
    rm -r compcert-1.9
    mv $TMP compcert-1.9
    patch -p1 < ../patch/compcert.patch
}

echo "Downloading sources..."
for p in $LIBS; do
  u=${p%,*}; f=${p#*,}
  echo -n "$SRC/$f"
  if [ -f $SRC/$f ]; then
      echo " exists, skipping..."
  else
      echo; curl -L# "$u" -o $SRC/$f
  fi
done

echo "Extracting and patching..."
for p in $LIBS; do
  f=${p#*,}
  eval prep_${f%.*} $f
done

echo "Done!"
