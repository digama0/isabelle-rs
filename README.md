# isabelle export tool

This depends on a hacked version of Isabelle, and a hacked version of
Poly/ML.

## Build instructions

Run the following:
```
git clone https://github.com/digama0/isabelle
cd isabelle
git checkout prooftrace
./Admin/init
./bin/isabelle component_polyml -N polyml-exportSmall
cd ..

git clone https://github.com/digama0/isabelle-rs
cd isabelle-rs
cargo build --release
cd ..
```

Now add the following to `~/.isabelle/etc/settings`:
```
ML_SYSTEM=polyml-exportSmall
POLYML_HOME="$ISABELLE_HOME/polyml-exportSmall"
ML_HOME="$POLYML_HOME/$ML_PLATFORM"
ML_SOURCES="$POLYML_HOME/src"
```

Finally we can test the export on a session:
```
./bin/isabelle build -o prooftrace_enabled=true -b HOL   # build HOL session with proofs
cd ../isabelle-rs
cargo run --release -- HOL  # read the proofs
```
