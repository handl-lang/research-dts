#!/usr/bin/env bash
# Install Quarto and (optionally) TinyTeX in the user's home, no root needed.
#
# Usage:
#   bash /home/luis/GitHub/luisfuturist/dts/tools/install_quarto.sh [VERSION] [tinytex]
#
# Examples:
#   bash /home/luis/GitHub/luisfuturist/dts/tools/install_quarto.sh
#   bash /home/luis/GitHub/luisfuturist/dts/tools/install_quarto.sh 1.5.57 no

set -euo pipefail

QUARTO_VERSION="${1:-1.6.40}"
INSTALL_TINYTeX="${2:-yes}"

USER_HOME="$HOME"
QUARTO_URL="https://github.com/quarto-dev/quarto-cli/releases/download/v${QUARTO_VERSION}/quarto-${QUARTO_VERSION}-linux-amd64.tar.gz"
QUARTO_DIR="${USER_HOME}/.local/lib/quarto-${QUARTO_VERSION}"
BIN_DIR="${USER_HOME}/.local/bin"
QUARTO_LINK="${BIN_DIR}/quarto"

echo "==> Installing Quarto ${QUARTO_VERSION} into ${USER_HOME}/.local"

mkdir -p "${USER_HOME}/.local/lib" "${BIN_DIR}"

if [[ -d "${QUARTO_DIR}" ]]; then
    echo "    Found existing ${QUARTO_DIR}; removing it."
    rm -rf "${QUARTO_DIR}"
fi

echo "==> Downloading ${QUARTO_URL}"
wget -q --show-progress -O - "${QUARTO_URL}" | tar xzf - -C "${USER_HOME}/.local/lib"

# Quarto tarballs extract to a directory named after the version, e.g. quarto-1.6.40
echo "==> Linking quarto into ${BIN_DIR}"
rm -f "${QUARTO_LINK}"
ln -s "${QUARTO_DIR}/bin/quarto" "${QUARTO_LINK}"

# Ensure ~/.local/bin is on PATH in ~/.bashrc
if ! grep -q "${BIN_DIR}" "${USER_HOME}/.bashrc" 2>/dev/null; then
    echo "" >> "${USER_HOME}/.bashrc"
    echo "# Added by tools/install_quarto.sh" >> "${USER_HOME}/.bashrc"
    echo "export PATH=\"${BIN_DIR}:\$PATH\"" >> "${USER_HOME}/.bashrc"
    echo "==> Added ${BIN_DIR} to PATH in ~/.bashrc"
else
    echo "==> ${BIN_DIR} already in PATH in ~/.bashrc"
fi

echo "==> Updating PATH for the current shell"
export PATH="${BIN_DIR}:${PATH}"

echo "==> Verifying quarto"
quarto --version
quarto check

if [[ "${INSTALL_TINYTeX}" == "yes" ]]; then
    echo "==> Installing TinyTeX (user-space TeX Live)"
    quarto install tinytex
    echo "==> TinyTeX installed"
else
    echo "==> Skipping TinyTeX install (pass 'yes' as second arg to install)"
fi

echo ""
echo "Done. Start a new shell or run:"
echo "  export PATH=\"${BIN_DIR}:\$PATH\""
echo ""
echo "Then build the paper with:"
echo "  cd /home/luis/GitHub/luisfuturist/dts/paper"
echo "  quarto render PAPER.md --to pdf"
echo "  mv PAPER.pdf paper.pdf"
