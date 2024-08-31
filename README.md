# isabelle export tool

This depends on a hacked version of Isabelle, and a hacked version of
Poly/ML.

## Build instructions

First, ensure you have `patchelf` using
```
sudo apt install patchelf
```
or equivalent. Then, run the following:
```
git clone https://github.com/digama0/isabelle
cd isabelle
git checkout prooftrace
./Admin/init
./bin/isabelle component_polyml -N polyml-exportSmall
./bin/isabelle build -o prooftrace_enabled=true -b HOL   # build HOL session with proofs
cd ..

git clone https://github.com/digama0/isabelle-rs
cd isabelle-rs
cargo run --release -- HOL  # read the proofs
cd ..
```
