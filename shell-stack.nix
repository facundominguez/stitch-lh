{ pkgs ?  import ./nixpkgs.nix {}
, ghc ? pkgs.haskell.compiler.ghc8102
}:

with pkgs;

haskell.lib.buildStackProject ({
  name = "stitch-lh";
  buildInputs = [ git z3 gmp libffi ];
  ghc = ghc;
  LANG = "en_US.utf8";
})
