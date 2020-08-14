# installs dependencies for Delphinium

# cryptominisat
sudo apt-get install build-essential cmake
sudo apt-get install zlib1g-dev libboost-program-options-dev libm4ri-dev libsqlite3-dev help2man
git clone https://github.com/msoos/cryptominisat.git
pushd cryptominisat
mkdir build
pushd build
cmake ..
make
sudo make install
sudo ldconfig
popd
if [ -z $(which cryptominisat5) ]
then echo "Error installing cryptominisat" ; exit 1
fi
popd

# stp
sudo apt-get install cmake bison flex libboost-all-dev python perl minisat
git clone https://github.com/stp/stp
pushd stp
mkdir build
pushd build
cmake -DENABLE_PYTHON_INTERFACE=ON ..
make
sudo make install
popd
if ! python -c "import stp" >/dev/null 2>&1
then echo "Error installing stp" ; exit 1
fi
popd

# z3
git clone https://github.com/Z3Prover/z3.git
pushd z3
python scripts/mk_make.py --python
pushd build
make
sudo make install
popd
if ! python -c "import z3" >/dev/null 2>&1
then echo "Error installing z3" ; exit 1
fi
popd
