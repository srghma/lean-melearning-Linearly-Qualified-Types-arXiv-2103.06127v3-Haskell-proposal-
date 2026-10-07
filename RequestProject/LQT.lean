module

-- Chapter 2: Background — Linear Haskell
public import RequestProject.LQT.Ch2_Background.Multiplicities

-- Chapter 3: Working with linear constraints (examples)
public import RequestProject.LQT.Ch3_LinearConstraints.ExampleSetting
public import RequestProject.LQT.Ch3_LinearConstraints.MinimalExamples
public import RequestProject.LQT.Ch3_LinearConstraints.Linearly

-- Chapter 5: A qualified type system for linear constraints
public import RequestProject.LQT.Ch5_QualifiedTypeSystem.SimpleConstraints
public import RequestProject.LQT.Ch5_QualifiedTypeSystem.Entailment
public import RequestProject.LQT.Ch5_QualifiedTypeSystem.EntailmentLemmas
public import RequestProject.LQT.Ch5_QualifiedTypeSystem.LeveledDomains
public import RequestProject.LQT.Ch5_QualifiedTypeSystem.Syntax
public import RequestProject.LQT.Ch5_QualifiedTypeSystem.Typing
public import RequestProject.LQT.Ch5_QualifiedTypeSystem.TypingInv
public import RequestProject.LQT.Ch5_QualifiedTypeSystem.LinearFunctions

-- Chapter 6: Constraint inference
public import RequestProject.LQT.Ch6_ConstraintInference.Wanted
public import RequestProject.LQT.Ch6_ConstraintInference.WantedLemmas
public import RequestProject.LQT.Ch6_ConstraintInference.WantedExamples
public import RequestProject.LQT.Ch6_ConstraintInference.Generation
public import RequestProject.LQT.Ch6_ConstraintInference.GenerationInv
public import RequestProject.LQT.Ch6_ConstraintInference.GenLetGen
public import RequestProject.LQT.Ch6_ConstraintInference.Solver
public import RequestProject.LQT.Ch6_ConstraintInference.FreeDomain
public import RequestProject.LQT.Ch6_ConstraintInference.FreeLDomain
public import RequestProject.LQT.Ch6_ConstraintInference.AtomicSolver
public import RequestProject.LQT.Ch6_ConstraintInference.AtomicSolverProps
public import RequestProject.LQT.Ch6_ConstraintInference.SolverIncompleteness

-- Chapter 7: Desugaring
public import RequestProject.LQT.Ch7_Desugaring.CoreCalculus
public import RequestProject.LQT.Ch7_Desugaring.Desugar
public import RequestProject.LQT.Ch7_Desugaring.DesugarTypingAux
public import RequestProject.LQT.Ch7_Desugaring.DesugarTyping

-- Formalization infrastructure (no counterpart in the paper)
public import RequestProject.LQT.Infrastructure.Usage
public import RequestProject.LQT.Infrastructure.UsageVec
public import RequestProject.LQT.Infrastructure.Map

/-!
# Linearly Qualified Types — a formalization (with type polymorphism)

Entry point importing the whole development.  The directories follow the sections of the
paper (`Ch2_Background`, `Ch3_LinearConstraints`, `Ch5_QualifiedTypeSystem`,
`Ch6_ConstraintInference`, `Ch7_Desugaring`); `Infrastructure` holds material with no
counterpart in the paper.  The proofs of Appendix B live next to the lemmas they prove, and the
full descriptions of Appendix A next to the corresponding figures of §7.  See
`RequestProject/LQT/README.md` for an overview of the correspondence with the paper and of the
deviations from it.
-/
