{
  description = "Probabilistic music composition with dependent types";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-22.11";

  outputs = { self, nixpkgs }:
    defaultPackage.x86_64-linux =
      with import nixpkgs { };
      stdenv.mkDerivation {
        name = "melocule";
        src = self;
        buildInputs = [ chez gnumake gmp gsl blas ];
        buildPhase = ''
          bash -c "$(curl -fsSL https://raw.githubusercontent.com/stefan-hoeck/idris2-pack/main/install.bash)"
          make
        '';
  };
}
