This is an example project using Liquid Haskell.

Build with 
```
stack --nix build
```

The only interesting stuff right now is a comparison of the
implementations of a simple expression language implemented twice.
One of the implementations uses Liquid Haskell
([TypedLanguageLH](examples/src/TypedLanguageLH.hs)) and the other
implementation uses GADTs
([TypedLanguageGADTs](examples/src/TypedLanguageGADTs.hs)).
