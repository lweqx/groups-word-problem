{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  };

  outputs =
    { nixpkgs, ... }:
    let
      lib = nixpkgs.lib;
      forAllSystems = lib.genAttrs lib.systems.flakeExposed;
    in
    {
      devShells = forAllSystems (
        system:
        let
          pkgs = import nixpkgs { inherit system; };

          emacsConfiguration = pkgs.runCommand "emacs-config" { } ''
            mkdir -p $out
            ln -s ${./emacs-config.el} $out/init.el
          '';

          proof-general = (pkgs.emacsPackagesFor pkgs.emacs).emacsWithPackages (
            epkgs: with epkgs; [
              epkgs.evil
              epkgs.proof-general
            ]
          );

          inherit (pkgs) rocqPackages coqPackages;
        in
        {
          default = pkgs.mkShell {
            packages = [
              (pkgs.runCommand "emacs" { nativeBuildInputs = [ pkgs.makeWrapper ]; } ''
                makeWrapper ${proof-general}/bin/emacs $out/bin/proof-general --add-flags '--init-directory ${emacsConfiguration}'
              '')

              rocqPackages.rocq-core
              rocqPackages.stdlib
              coqPackages.mathcomp
              (pkgs.callPackage ./coq-library-undecidability.nix { })
            ];
          };
        }
      );

      packages = forAllSystems (
        system:
        let
          pkgs = import nixpkgs { inherit system; };
        in
        {
          coq-library-undecidability = pkgs.callPackage ./coq-library-undecidability.nix { };
        }
      );

      formatter = forAllSystems (
        system:
        let
          pkgs = import nixpkgs { inherit system; };
        in
        pkgs.nixfmt-tree
      );
    };
}
