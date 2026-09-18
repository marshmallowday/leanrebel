/-
# Analytic ReBeL proof surface

This opt-in root keeps analytic imports in the architecture-owned Analysis
surface. All declarations retain the GameTheory.ReBeL namespace and reuse
canonical Protocol execution and information, rather than a parallel model.
-/

import GameTheory.Analysis.ReBeL.LocalRegret
import GameTheory.Analysis.ReBeL.Examples.LocalRegret
import GameTheory.Analysis.ReBeL.ChronologicalLocality
import GameTheory.Analysis.ReBeL.Examples.ChronologicalLocality
import GameTheory.Analysis.ReBeL.PolicyPatching
import GameTheory.Analysis.ReBeL.RootDecomposition
import GameTheory.Analysis.ReBeL.Examples.RootDecomposition
import GameTheory.Analysis.ReBeL.RegretMatching
import GameTheory.Analysis.ReBeL.CFRTrace
import GameTheory.Analysis.ReBeL.PayoffBounds
import GameTheory.Analysis.ReBeL.RootRegretBounds
import GameTheory.Analysis.ReBeL.WeightedAverage
import GameTheory.Analysis.ReBeL.OwnReachAverage
import GameTheory.Analysis.ReBeL.OutcomeReach
import GameTheory.Analysis.ReBeL.IndependentRealization
import GameTheory.Analysis.ReBeL.UnilateralAverage
import GameTheory.Analysis.ReBeL.AverageNash
import GameTheory.Analysis.ReBeL.CFRNash
