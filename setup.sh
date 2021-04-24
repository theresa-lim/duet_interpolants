#!/bin/bash
# This script will install dependencies then build ComPACT

if [ $(id -u) != "0" ]; then
echo "You must be the superuser to run this script" >&2
exit 1
fi

if [ $SUDO_USER ]; then
    real_user=$SUDO_USER
else
    real_user=$(whoami)
fi

apt-get update

echo "installing essential dependencies ..."
apt-get -y install curl build-essential autoconf git-all

echo "Installing opam ..."
sudo -u $real_user sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)

echo "Installing dependencies opam, GMP, MPFR, NTL, Java, Python ..."
apt-get -y install opam libgmp-dev libmpfr-dev libntl-dev default-jre python

echo "Installing opam dependencies, this is going to take long ..."
sudo -u $real_user opam remote add sv git://github.com/zkincaid/sv-opam.git#modern
sudo -u $real_user opam install -y dune ocamlgraph batteries ppx_deriving z3 apron ounit menhir cil OCRS ntl

echo "Building ComPACT ... "
./configure && make

echo "Setup completed!"
