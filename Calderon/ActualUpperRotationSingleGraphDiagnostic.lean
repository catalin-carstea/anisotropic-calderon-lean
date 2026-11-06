import Calderon.ActualReferenceUpperRotationCommutator
import Calderon.SphereSobolevSingleRotationAngleDerivative

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotationProjection SpectralWeightedGraph

/-! Full upfront: EXPANSION-v002.json. Focus only the actual single-input graph
normalization, using typed value transports rather than rewriting the checked graph. -/

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceSharpRadialTraceFamily referenceSharpRadialRotationCommutatorL

lemma referenceSharpRadialRotationCommutatorL_single_graph_diagnostic
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (n : ℕ) (u : harmonicSphereSubspace n) :
    sphereSobolevRotationL (1/2:ℝ) i j
      (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
        (sphereSobolevSingleL (3/2:ℝ) n u)) -
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
        (sphereSobolevSingleL (3/2:ℝ) n (harmonicSphereRotation n i j u))) =
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (referenceSharpRadialRotationCommutatorL g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 i j p (sphereSobolevSingleL (3/2:ℝ) n u)) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "SINGLE_GRAPH_ENTER"
    out.flush
  let T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
    referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p
  let Cop : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
    referenceSharpRadialRotationCommutatorL g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 i j p
  let I : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let J : SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
    sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let f : SphereSobolev (5/2:ℝ) := sphereSobolevSingleL (5/2:ℝ) n u
  have hGraph : sphereSobolevRotationL (1/2:ℝ) i j (T (J f)) -
      I (T (sphereSobolevRotationL (5/2:ℝ) i j f)) = I (Cop (J f)) :=
    referenceSharpRadialRotationCommutatorL_graph_agreement
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hStrong hWeak f
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "SINGLE_GRAPH_SPECIALIZED"
    out.flush
  have hIn : J f = sphereSobolevSingleL (3/2:ℝ) n u :=
    sphereSobolevInclusionL_single (5/2:ℝ) (3/2:ℝ) (by norm_num) n u
  have hSingle (w : harmonicSphereSubspace n) :
      sphereSobolevSingleL ((5/2:ℝ)-1) n w = sphereSobolevSingleL (3/2:ℝ) n w := by
    change besselWeight ((5/2:ℝ)-1) n •
        lp.single (E := fun k : ℕ => harmonicSphereSubspace k) 2 n w =
      besselWeight (3/2:ℝ) n •
        lp.single (E := fun k : ℕ => harmonicSphereSubspace k) 2 n w
    exact congrArg (fun r : ℝ => r •
      lp.single (E := fun k : ℕ => harmonicSphereSubspace k) 2 n w)
      (congrArg (fun s : ℝ => besselWeight s n)
        (show (5/2:ℝ)-1 = (3/2:ℝ) from by norm_num))
  have hRot : sphereSobolevRotationL (5/2:ℝ) i j f =
      sphereSobolevSingleL (3/2:ℝ) n (harmonicSphereRotation n i j u) :=
    (sphereSobolevRotationL_single (5/2:ℝ) i j n u).trans
      (hSingle (harmonicSphereRotation n i j u))
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "SINGLE_GRAPH_INPUT_NORMALIZED"
    out.flush
  have hT := congrArg (fun z : SphereSobolev (3/2:ℝ) => T z) hIn
  have hTRot := congrArg (fun z : SphereSobolev (3/2:ℝ) => T z) hRot
  have hCop := congrArg (fun z : SphereSobolev (3/2:ℝ) => Cop z) hIn
  have hLeftRotation := congrArg (fun z : SphereSobolev (1/2:ℝ) =>
    sphereSobolevRotationL (1/2:ℝ) i j z) hT
  have hLeftInclusion := congrArg (fun z : SphereSobolev (1/2:ℝ) => I z) hTRot
  have hLeft := congrArg₂ (fun z z' : SphereSobolev (-(1/2:ℝ)) => z-z')
    hLeftRotation hLeftInclusion
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "SINGLE_GRAPH_LEFT_TRANSPORTED"
    out.flush
  have hRight := congrArg (fun z : SphereSobolev (1/2:ℝ) => I z) hCop
  exact hLeft.symm.trans (hGraph.trans hRight)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpRadialRotationCommutatorL_single_graph_diagnostic
