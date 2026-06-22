{pkgs ? import <nixpkgs> {}}:
pkgs.mkShell {
  packages =  let
    prims = pkgs.ocamlPackages.buildDunePackage {
      pname = "coq-primitive";
      version = "8.20.0";
      src = builtins.fetchurl {
        url = "https://github.com/peregrine-project/rocq-primitive/releases/download/8.20.0/coq-primitive-8.20.0.tar.gz";
        sha256 = "sha256:0982m5ybnayf4c8gy89xmxlgk72y9za2b0ysb7fk4gg2bsf1bhp3";
      };
    };
  in
  with pkgs; [
    dune
    coq_8_20
    prims
    ocamlPackages.findlib
  ];
}
