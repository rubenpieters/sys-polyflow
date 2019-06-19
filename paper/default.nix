{ pkgs ? import <nixpkgs>{} } :

with pkgs;

stdenv.mkDerivation {
  name = "paper";
  buildInputs = [ (texlive.combine {
                    inherit (texlive)
                      scheme-small

                      # Add other LaTeX libraries (packages) here as needed, e.g:
		      mathpartir

                      # build tools
                      latexmk
                      ;
                  })

                ];
  src = ./.;
  buildPhase = "make";
}
