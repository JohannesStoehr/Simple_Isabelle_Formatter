# Simple Formatter for Isabelle

This Java script reads all `.thy` files in the project directory and creates a formatted ("clean") version of these files.

### Overview of formatting to expect:
- Add spaces around every operator
- Add spaces before every group of opening brackets and after every group of closing brackets
- Add spaces around quoted strings
- Add some other spaces
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

Requires at least Java 21 to run.
