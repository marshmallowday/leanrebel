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
import GameTheory.Analysis.ReBeL.Examples.CFRNash
import GameTheory.Analysis.ReBeL.RationalArithmetic
import GameTheory.Analysis.ReBeL.RationalEvaluation
import GameTheory.Analysis.ReBeL.RationalReach
import GameTheory.Analysis.ReBeL.RationalCounterfactual
import GameTheory.Analysis.ReBeL.RationalIteration
import GameTheory.Analysis.ReBeL.RationalAverage
import GameTheory.Analysis.ReBeL.Examples.RationalCodec
import GameTheory.Analysis.ReBeL.Examples.RationalInformation
import GameTheory.Analysis.ReBeL.Examples.RationalPrimitives
import GameTheory.Analysis.ReBeL.Examples.RationalChance
import GameTheory.Analysis.ReBeL.Examples.RationalExecution
import GameTheory.Analysis.ReBeL.Examples.RationalReach
import GameTheory.Analysis.ReBeL.Examples.RationalSites
import GameTheory.Analysis.ReBeL.Examples.RationalCounterfactual
import GameTheory.Analysis.ReBeL.Examples.RationalProjection
import GameTheory.Analysis.ReBeL.RationalMatching
import GameTheory.Analysis.ReBeL.Examples.RationalRegret
import GameTheory.Analysis.ReBeL.Examples.RationalIteration
import GameTheory.Analysis.ReBeL.RationalAverageEquiv
import GameTheory.Analysis.ReBeL.Examples.RationalAverage
import GameTheory.Analysis.ReBeL.EquilibriumValue
import GameTheory.Analysis.ReBeL.Examples.EquilibriumValue
import GameTheory.Analysis.ReBeL.TypeValue
import GameTheory.Analysis.ReBeL.ValueGeometry
import GameTheory.Analysis.ReBeL.ContinuationConsistency
import GameTheory.Analysis.ReBeL.ContinuationRealization
