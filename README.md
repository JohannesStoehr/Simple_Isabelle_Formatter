# Simple Formatter for Isabelle

This Java script reads all `.thy` files meant for [Isabelle](https://isabelle.in.tum.de) in the project directory and creates a formatted ("clean") version of these files.

### Overview of formatting to expect:
- Add spaces:
  - Around every operator
  - Before every group of opening brackets and after every group of closing brackets
  - Around quoted strings
  - A few other places
- Break lines for every `if then else` and `case of` statement and normalize their positioning
- Break lines for every `apply`, `using`, `unfolding`, `by`, `assumes` and `shows`
- Remove the simplest versions of unnecessary brackets
- Add `and`s between assumptions of proofs
- Break long lines of `using` and `unfolding` into multiple lines
- Add a reminder that `apply auto` is usually bad style (see: https://proofcraft.org/blog/isabelle-style.html)
- Add empty lines before proofs
- Cap the amount of empty lines
- Indent lines (apply-style proofs currently not supported)
- To be continued

The script is currently limited since it does not build an abstract syntax tree (AST) of the Isabelle files. It only does some basic string manipulation, which limits it to simple formatting tasks. However, it is still useful for cleaning up Isabelle files.

Requires at least Java 21 to run.
