# Abstract source

`abstract.pdf` is the working extended abstract, currently five body pages plus references. Rebuild it with `make abstract` using `latexmk`, `acmart`, the Libertinus fonts and JetBrains Mono (Regular and SemiBold). The build uses LuaLaTeX and the anonymous review class option.

`make figures` rebuilds the standalone TikZ diagrams. Their text, mathematics and code use the same fonts as the document. These require TikZ/PGF, amsmath, fontspec and unicode-math. Only the Lua renderings are included.

Language keywords use JetBrains Mono SemiBold and other code uses Regular, with ligatures disabled. Register names use the code face in programs, prose and wire labels. States, gates and semantic maps use the math face. A label such as `v: x` names the register and its input state.

Shaded boxes mark source prefixes. Inserted green return gates lie outside those boxes, before the drop markers. Triangles mark allocation and ground marks end a source register's scope. Blue and gold distinguish basis slices and measurement records, purple marks fixed certificates, teal marks allocation states, and brown follows a borrowed register.
