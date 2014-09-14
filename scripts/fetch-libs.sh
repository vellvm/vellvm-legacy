#!/bin/bash
set -e

LIB=./lib
SRC=./src
if [[ $OSTYPE =~ "darwin" ]]; then
  MKTEMP=gmktemp
else
  MKTEMP=mktemp
fi

mkdir -p $LIB
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
}

prep_metalib-20090714() {
    unzip -qqo $SRC/$1
    patch -p1 < ../patch/metalib.patch
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
    TMP=$($MKTEMP -dp.)
    tar xzf $SRC/$1
    cp compcert-1.9/common/{AST,Errors,Memdata,Memory,Memtype,Values}.v \
       compcert-1.9/lib/{Axioms,Coqlib,Floats,Integers,Intv,Iteration,Lattice,Maps,Ordered}.v \
       compcert-1.9/backend/Kildall.v \
       $TMP
    rm -r compcert-1.9
    mv $TMP compcert-1.9
    patch -p1 < ../patch/compcert.patch
}

for p in $LIBS; do
  u=${p%,*}; f=${p#*,}
  echo -n "Downloading $SRC/$f"
  if [ -f $SRC/$f ]; then
      echo " ... archive exists, skipping"
  else
      echo; curl -L# "$u" -o $SRC/$f
  fi

  d=${f%.*}
  echo -n "Extracting to $d"
  if [ -d $d ]; then
      echo " ... target dir exists, skipping"
  else
      eval prep_$d $f      
  fi
done

echo "Done!"
