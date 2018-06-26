{ package ? "kpf", compiler ? "ghc842" }:
(import ./default.nix {
  inherit package compiler;
}).kpf
