#!/bin/sh
# Comparadores de EXP-005 (manifiesto v0.5, §23.3): Rust, Go, Dafny y Kani.
# rustc/cargo y go vienen de los paquetes de Ubuntu; Dafny y rustup se descargan con su hash.
set -eu
OPT="$HOME/.local/opt"
mkdir -p "$OPT"
sudo apt-get install -y rustc cargo rustfmt golang-go  # probado: rustc 1.93.1, rustfmt 1.8.0, go 1.26.8

# Dafny 4.11.0 (incluye su Z3).
cd "$OPT"
curl -sSL -o dafny.zip https://github.com/dafny-lang/dafny/releases/download/v4.11.0/dafny-4.11.0-x64-ubuntu-22.04.zip
echo "a46a9ff7cdd720f7955854c78e95df13f4cfe6b80691b05f8654fe19e8267179  dafny.zip" | sha256sum -c
python3 -c "import zipfile; zipfile.ZipFile('dafny.zip').extractall('.')"
chmod +x dafny/dafny dafny/z3/bin/*

# Kani 0.68.0: rustup (hash publicado) + kani-verifier + su toolchain nightly fijada.
u=https://static.rust-lang.org/rustup/dist/x86_64-unknown-linux-gnu/rustup-init
curl -sSfO "$u"; curl -sSf "$u.sha256" | awk '{print $1"  rustup-init"}' | sha256sum -c
chmod +x rustup-init && ./rustup-init -y --no-modify-path --default-toolchain none --profile minimal
/usr/bin/cargo install --locked kani-verifier --version 0.68.0 --root "$OPT/kani-cli"
PATH="$OPT/kani-cli/bin:$HOME/.cargo/bin:$PATH" kani setup
