{pkgs ? import <nixpkgs> {}}: let
  coq-primitives = pkgs.ocamlPackages.buildDunePackage {
    pname = "coq-primitive";
    version = "8.20.0";
    src = builtins.fetchurl {
      url = "https://github.com/peregrine-project/rocq-primitive/releases/download/8.20.0/coq-primitive-8.20.0.tar.gz";
      sha256 = "sha256:0982m5ybnayf4c8gy89xmxlgk72y9za2b0ysb7fk4gg2bsf1bhp3";
    };
  };
  rocq-picinae = pkgs.ocamlPackages.buildDunePackage {
    pname = "rocq-picinae";
    version = "0.0.0";
    src = pkgs.fetchFromGitHub {
      owner = "CharlesAverill";
      repo = "Picinae";
      rev = "7eb1f4a1e74a8a9801d07e59ba01cadaa3cd1073";
      hash = "sha256-9ua3SsclZK0BgZIc9oXatBs29P0m92OMfVaGvOgJpQQ=";
    };
    nativeBuildInputs = [pkgs.coq_8_20];
  };
  packages = with pkgs; [
    coq_8_20
    dune
    pkgsCross.aarch64-multiplatform.stdenv.cc
    lief
  ];
  coq-libs = [
    rocq-picinae
    coq-primitives
  ];
  ocaml-libs = with pkgs.ocamlPackages; [
    findlib
    ctypes
    ctypes-foreign
    cmdliner
  ];
in
  pkgs.mkShell {
    packages = packages ++ ocaml-libs ++ coq-libs;
    shellHook = "export COQPATH=${rocq-picinae}/lib/ocaml/5.4.1/site-lib/coq/user-contrib:$COQPATH";
  }
