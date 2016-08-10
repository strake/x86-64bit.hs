# Version 0.1.3

-   jmpq instruction support (George Stelle)
-   support near conditional jumps
-   support automatic decision between short and near conditional jumps for backward references
-   support alternative condition names
-   make possible to use labels as relative immediate values (not used yet)
-   bugfix
    -   fail if a short jump is out of range

# Version 0.1.2

-   Windows operating system support (Balázs Kőműves)
-   GHC 7.10 support
-   TODO.md file added

# Version 0.1.1.1

-   change dependencies to reflect that the package compiles only with ghc 8
-   add 'tested-with: GHC == 8.0.1' to the cabal file

# Version 0.1.1

-   examples moved into the library
-   more Haddock comments
-   add cabal test suit
-   bugfixes
    -   fix code generation for alignments
    -   smaller code is generated now for 'add rax, 100' and similar instrcutions

