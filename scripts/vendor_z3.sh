#!/bin/sh
# Descarga Z3 5.1.0.0 (wheel oficial de PyPI) en .vendor/, comprobando su SHA-256.
# Solo hace falta si `import z3` no funciona en el Python del sistema.
set -eu

VERSION=5.1.0.0
SHA256=dfad9e309d7010b1ff6bdb33f21570a1603ef4727373221c7117a74448f0cfef
URL=https://files.pythonhosted.org/packages/34/de/30329041d9a2dda11308576a80b5db17060e4b03a7ba7f550437fb38dd6b/z3_solver-5.1.0.0-py3-none-manylinux_2_27_x86_64.whl

ROOT=$(cd "$(dirname "$0")/.." && pwd)
DEST="$ROOT/.vendor/z3-$VERSION"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

curl -sSfL -o "$TMP/z3.whl" "$URL"
echo "$SHA256  $TMP/z3.whl" | sha256sum -c -
mkdir -p "$DEST"
python3 -I -m zipfile -e "$TMP/z3.whl" "$DEST"
python3 -I -c "import sys; sys.path.insert(0, '$DEST'); import z3; print('Z3', z3.get_version_string(), 'en', '$DEST')"
