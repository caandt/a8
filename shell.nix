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
  a64pkgs = pkgs.pkgsCross.aarch64-multiplatform;
  a64-cc = pkgs.symlinkJoin {
    name = "a64-cc";
    paths = [a64pkgs.stdenv.cc.bintools a64pkgs.stdenv.cc];
    nativeBuildInputs = [pkgs.makeWrapper];
    postBuild = ''
      for bin in aarch64-unknown-linux-gnu-gcc aarch64-unknown-linux-gnu-g++; do
        wrapProgram $out/bin/$bin \
          --add-flags "-L${a64pkgs.glibc.static}/lib" \
          --add-flags "-B${a64pkgs.glibc.static}/lib" \
          --add-flags "-I${a64pkgs.glibc.static}/include"
      done
    '';
  };
  packages = with pkgs; [
    ocaml
    coq_8_20
    dune
    a64-cc
    lief
    perf
  ];
  coq-libs = with pkgs.coqPackages_8_20; [
    rocq-picinae
    coq-record-update
    stdpp
    coqutil
  ];
  ocaml-libs = with pkgs.ocamlPackages; [
    coq-primitives
    findlib
    ctypes
    ctypes-foreign
    cmdliner
    ppx_deriving
    ppx_import
    parmap
    utop
  ];
in
  pkgs.mkShell {
    packages = packages ++ ocaml-libs ++ coq-libs;
    shellHook = "export COQPATH=${rocq-picinae}/lib/ocaml/5.4.1/site-lib/coq/user-contrib:$COQPATH";
  }
