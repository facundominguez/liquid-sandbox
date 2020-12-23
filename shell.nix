{pkgs ? import ./nixpkgs.nix {}}:

with pkgs;

mkShell {
  # Set UTF-8 local so that run-tests can parse GHC's unicode output.
  LANG="C.UTF-8";

  buildInputs = [
    less
    git
    z3
    which
    # Needed to get correct locale for tests with encoding
    glibcLocales
    cacert
  ];

}
