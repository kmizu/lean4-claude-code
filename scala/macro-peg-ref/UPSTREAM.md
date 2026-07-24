# Vendored reference implementation: kmizu/macro_peg

## Source

- Project: https://github.com/kmizu/macro_peg
- Vendored from a local sibling checkout at `/home/mizushima/repo/macro_peg` during this
  vendoring operation, but its permanent home is the GitHub repository above.
- Frozen commit: `528e964120e9ff06ef71ee6103b285d939a18526`

## License

The upstream project is BSD-licensed. Full text, copied verbatim from its `LICENSE` file:

```
Copyright (c) 2010-2015, Kota Mizushima.
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, 
are permitted provided that the following conditions are met:

Redistributions of source code must retain the above copyright notice, this list 
of conditions and the following disclaimer. 
Redistributions in binary form must reproduce the above copyright notice, this 
list of conditions and the following disclaimer in the documentation and/or other 
materials provided with the distribution. 
Neither the name of the Kota Mizushima nor the names of its contributors may be 
used to endorse or promote products derived from this software without specific 
prior written permission. 
THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND 
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED 
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. 
IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, 
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, 
BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, 
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE 
OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED 
OF THE POSSIBILITY OF SUCH DAMAGE.
```

## Vendored files

All files below live under `src/main/scala/com/github/kmizu/macro_peg/` in this
subproject, preserving the upstream package path `com.github.kmizu.macro_peg`.
Each was copied byte-for-byte (verified via `md5sum`) from the frozen commit above —
no reformatting, no fixes, no added scaladoc.

From `src/main/scala/com/github/kmizu/macro_peg/` upstream:

- `Ast.scala`
- `Diagnostic.scala`
- `EvaluationException.scala`
- `EvaluationResult.scala`
- `EvaluationStrategy.scala`
- `Evaluator.scala`
- `GrammarValidator.scala`
- `MacroExpander.scala`

From `src/test/scala/com/github/kmizu/macro_peg/` upstream (test-support DSL, relocated
into `src/main/scala` here since this subproject has no test sources of its own yet):

- `GrammarDsl.scala` — a small, dependency-free AST-construction DSL used by upstream's
  own test suite. Its only import is `com.github.kmizu.macro_peg.Ast._`, which is
  already vendored above; it needs nothing else.

All 9 files were checked for same-package references (not just `import` statements,
since Scala doesn't require an import for same-package symbols) to `Parser.scala`,
`InlineMacroParsers.scala`, `Interpreter.scala`, `TypeChecker.scala`, `Runner.scala`,
or the `codegen`/`combinator`/`ir`/`ruby` subpackages — none were found. This set of
9 files is self-contained.

## Why vendor verbatim

These files are vendored verbatim to give this project's differential harness an
independent oracle to compare against, without depending on the reference repo being
present at a fixed path at build time.

## Do not edit

Do not edit these files directly. If the reference implementation needs to be
re-vendored (e.g. upstream fixes a bug relevant to the comparison), re-run the
vendoring process against a possibly newer commit and update the frozen commit SHA
in this file.

## Adaptations for this project's Scala 3.7.4 toolchain

None. All 8 core files plus `GrammarDsl.scala` compiled against this project's
Scala 3.7.4 toolchain with no source changes required.
