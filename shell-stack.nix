{ pkgs ?  import ./nixpkgs.nix {}
, ghc ? pkgs.haskell.compiler.ghc8102
}:

with pkgs;

haskell.lib.buildStackProject ({
  name = "inline-java";
  buildInputs = [ git z3 ];
  ghc = ghc;
  LANG = "en_US.utf8";
})
