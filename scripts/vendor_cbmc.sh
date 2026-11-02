#!/bin/sh
# Descarga CBMC 6.11.0 (paquete oficial de diffblue/cbmc para Ubuntu 24.04 x86_64) en
# .vendor/, comprobando su SHA-256, y extrae los binarios sin instalar el paquete.
# Lo usa la condición B de EXP-003 y el oráculo formal de C.
set -eu

VERSION=6.11.0
SHA256=b3721aa541038384d7801ea3aeabbcddc3e8845ac8f1cbff637cf8dec7481ac8
URL=https://github.com/diffblue/cbmc/releases/download/cbmc-$VERSION/ubuntu-24.04-cbmc-$VERSION-Linux.deb

ROOT=$(cd "$(dirname "$0")/.." && pwd)
DEST="$ROOT/.vendor/cbmc-$VERSION"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

curl -sSfL -o "$TMP/cbmc.deb" "$URL"
echo "$SHA256  $TMP/cbmc.deb" | sha256sum -c -
mkdir -p "$DEST"
if command -v dpkg-deb >/dev/null 2>&1; then
    dpkg-deb -x "$TMP/cbmc.deb" "$DEST"
else
    (cd "$TMP" && ar x cbmc.deb && tar -xf data.tar.* -C "$DEST")
fi
"$DEST/usr/bin/cbmc" --version
