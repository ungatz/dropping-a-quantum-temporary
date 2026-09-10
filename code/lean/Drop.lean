import Drop.Gram
import Drop.Marginal
import Drop.Local
import Drop.Boundary
import Drop.Robust

import Drop.SimpleTensor
import Drop.Circuit.Output
import Drop.Source.Language
import Drop.Source.Gates
import Drop.Source.Safety
import Drop.Source.Reflection
import Drop.Dilation.Dilation
import Drop.Dilation.Bridge
import Drop.Dilation.Program
import Drop.Calculus.Syntax
import Drop.Calculus.Typing
import Drop.Calculus.Machine
import Drop.Calculus.Reflection

/-!
# Dropping a quantum temporary

Importing this file builds the whole library.

The first five modules are the linear-algebra core of the criterion. The rest
mechanise the criterion itself, from the syntax of the calculus to the
theorem: a typed program is weakenable exactly when its drop is safe.
-/
