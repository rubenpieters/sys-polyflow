{ pkgs ? import <nixpkgs>{} } :

with pkgs;

let
  pkg = agda.mkDerivation(self: {
    name = "proofs";
    src = ./.;
    buildDepends = [ pkgs.AgdaStdlib (pkgs.haskellPackages.ghcWithPackages (p: [p.ieee])) ];
    postBuild = "agda --compile Alg.agda --no-main";
  });
in
  pkg.env;