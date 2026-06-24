{ pkgs ? import (fetchTarball "https://github.com/NixOS/nixpkgs/archive/3e41b24abd260e8f71dbe2f5737d24122f972158.tar.gz") {} }:

pkgs.mkShell rec {
  nativeBuildInputs = with pkgs.buildPackages; [
    (haskell.packages.ghc984.ghcWithPackages (pkgs: with pkgs; [ cabal-install haskell-language-server ]))
    watchexec
  ];

  shellHook = ''
  '';
}
