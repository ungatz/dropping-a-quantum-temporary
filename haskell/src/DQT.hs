-- |
-- Module      : DQT
--
-- One file to open to see the whole theory layer in the order it should be
-- read, with the compiler checking the order is real: each group below uses
-- only the groups above it.  Importing individual modules is equally good.
module DQT
  ( -- * Arithmetic
    module DQT.Algebra.Scalar
  , module DQT.Algebra.Linear
    -- * The calculus
  , module DQT.Calculus.Syntax
  , module DQT.Calculus.Gates
  , module DQT.Calculus.Typing
  , module DQT.Calculus.Metatheory
    -- * The two semantics
  , module DQT.Calculus.Machine
  , module DQT.Calculus.Elaborate
    -- * The criterion
  , module DQT.Criterion.Split
  , module DQT.Criterion.Gram
  , module DQT.Criterion
  , module DQT.Criterion.Witness
    -- * What a safe drop hands back
  , module DQT.Many.Release
    -- * What a continuation can see
  , module DQT.Criterion.Context
    -- * Scale
  , module DQT.Many.Multi
    -- * Measurement
  , module DQT.Lifted
  , module DQT.Lifted.Programs
  , module DQT.Residual
  , module DQT.Corpus.Classical
    -- * The catalogue, the producer rules, and rendering
  , module DQT.Corpus.Examples
  , module DQT.Corpus.Producer
  , module DQT.Report
    -- * The two implementations, compared
  , module DQT.Bridge
  ) where

import DQT.Bridge
import DQT.Corpus.Classical
import DQT.Criterion.Context
import DQT.Criterion
import DQT.Calculus.Elaborate
import DQT.Corpus.Examples
import DQT.Calculus.Gates
import DQT.Criterion.Gram
import DQT.Algebra.Linear
import DQT.Lifted
import DQT.Lifted.Programs
import DQT.Calculus.Machine
import DQT.Calculus.Metatheory
import DQT.Many.Multi
import DQT.Corpus.Producer
import DQT.Many.Release
import DQT.Report
import DQT.Residual
import DQT.Algebra.Scalar
import DQT.Criterion.Split
import DQT.Calculus.Syntax
import DQT.Calculus.Typing
import DQT.Criterion.Witness
