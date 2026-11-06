import Calderon.ActualHighSmoothMultiplierForcingJointTopology
import Calderon.ActualHighSmoothMultiplierBoundaryCommutator
import Calderon.NativeThreeHalfNormalDerivativeMultiplierTopology
import Calderon.ActualJointNativeTraceOperatorFamily
import Calderon.NativeCompletedHarmonicLiftTopology
import Calderon.NativeHighSmoothMultiplierCompletedForcingTopology
import Calderon.NativeHighSmoothMultiplierInverseCompletedForcingTopology

/-! Smoothness in norm of the actual high gain on the finite inverse room. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal ContDiff Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  (q : T × R3 → ℝ) (hq : ContDiff ℝ ∞ q) (Kq : Set R3) (hKq : IsCompact Kq)
  (hqz : ∀ t x, x ∉ Kq → q (t,x) = 0)

attribute [local instance_reducible] highStrongNativeH3Group
attribute [local instance_reducible] highStrongNativeH3Space
attribute [local instance] highStrongNativeH3Group
attribute [local instance] highStrongNativeH3Space

@[instance_reducible]
def boundaryTopologyNativeH1Group : NormedAddCommGroup (BallSobolev 1) :=
  TauCeti.Wkp.instNormedAddCommGroup
    (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 1

attribute [local instance] boundaryTopologyNativeH1Group

@[instance_reducible]
def boundaryTopologyNativeH1Space : NormedSpace ℝ (BallSobolev 1) :=
  TauCeti.Wkp.instNormedSpace
    (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 1

attribute [local instance] boundaryTopologyNativeH1Space

section

@[instance_reducible]
def boundaryTopologyNativeH2Group : NormedAddCommGroup (BallSobolev 2) :=
  TauCeti.Wkp.instNormedAddCommGroup
    (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 2

attribute [local instance] boundaryTopologyNativeH2Group

@[instance_reducible]
def boundaryTopologyNativeH2Space : NormedSpace ℝ (BallSobolev 2) :=
  TauCeti.Wkp.instNormedSpace
    (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 2

attribute [local instance] boundaryTopologyNativeH2Space

end

attribute [local irreducible] TauCeti.SobolevStage.instNormedAddCommGroup
attribute [local irreducible] TauCeti.SobolevStage.instNormedSpace

attribute [local irreducible] referenceStrongDriftFamily referenceHarmonicLiftFamily harmonicLiftCompletion
  referenceHighSmoothMultiplierStrongDefectFamily referenceHighSmoothMultiplierCommutatorForcingFamily
  referenceHighSmoothMultiplierBoundaryCommutatorFamily nativeThreeHalfNormalDerivativeMulL

run_cmd do
  let out ← IO.getStdout
  out.putStrLn "BOUNDARY_PHASE BEFORE_DEFECT_THEOREM"
  out.flush

lemma contDiffAt_referenceHighSmoothMultiplierStrongDefect_commonSupport_joint
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (t : T)
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible)
    (hLow : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × T =>
      referenceHighSmoothMultiplierStrongDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF
        (commonSupportCoefficientFamily 3 q hq Kq hKq hqz z.2) z.1) (p,t) := by
  dbg_trace "BOUNDARY_PHASE DEFECT_BODY_ENTER"
  have hInverseCompleted :=
    contDiffAt_referenceHighSmoothMultiplierInverseCompletedForcing_commonSupport_joint
      g L y0 Φ B ε C ρ H a w hData q hq Kq hKq hqz hcalc hF p t hStrong hLow
  dbg_trace "BOUNDARY_PHASE INVERSE_COMPLETED_READY"
  have hResult := (contDiffAt_const (c := nativeStrongDirichletInclusionL 1)).clm_comp
    hInverseCompleted
  dbg_trace "BOUNDARY_PHASE PUBLIC_COMPOSITE_READY"
  dbg_trace "BOUNDARY_PHASE PUBLIC_GRAPH_ENTER"
  apply hResult.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun z => by
    apply ContinuousLinearMap.ext
    intro f
    unfold referenceHighSmoothMultiplierStrongDefectFamily
    calc
      _ = referenceHighSmoothMultiplierStrongDefectFunction
          g L y0 Φ B ε C ρ H a w hData hcalc hF
          (commonSupportCoefficientFamily 3 q hq Kq hKq hqz z.2) z.1 f := rfl
      _ = nativeStrongDirichletInverseInclusionL 1
          (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 z.1.1 z.1.2)
          (referenceHighSmoothMultiplierCommutatorForcingFamily
            g L y0 Φ B ε C ρ H a w hData hcalc
            (commonSupportCoefficientFamily 3 q hq Kq hKq hqz z.2) z.1
            ((referenceHarmonicLiftFamily
              g L y0 Φ B ε C ρ H a w hData hcalc 0 z.1.1 z.1.2)
              (harmonicLiftCompletion hF f))) :=
        referenceHighSmoothMultiplierStrongDefectFunction_apply
          g L y0 Φ B ε C ρ H a w hData hcalc hF
          (commonSupportCoefficientFamily 3 q hq Kq hKq hqz z.2) z.1 f
      _ = _ := rfl)

run_cmd do
  let out ← IO.getStdout
  out.putStrLn "BOUNDARY_PHASE BEFORE_BOUNDARY_THEOREM"
  out.flush

lemma contDiffAt_referenceHighSmoothMultiplierBoundaryCommutator_commonSupport_joint
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (t : T)
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible)
    (hLow : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × T =>
      referenceHighSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 (commonSupportCoefficientFamily 3 q hq Kq hKq hqz z.2) z.1) (p,t) := by
  dbg_trace "BOUNDARY_PHASE BOUNDARY_BODY_ENTER"
  letI : NormedAddCommGroup (BallSobolev 2) := boundaryTopologyNativeH2Group
  letI : NormedSpace ℝ (BallSobolev 2) := boundaryTopologyNativeH2Space
  dbg_trace "BOUNDARY_PHASE BOUNDARY_H2_INSTANCES_READY"
  have hV := contDiffAt_referenceHighSmoothMultiplierStrongDefect_commonSupport_joint
    g L y0 Φ B ε C ρ H a w hData q hq Kq hKq hqz hcalc hF p t hStrong hLow
  dbg_trace "BOUNDARY_PHASE DEFECT_TO_BOUNDARY_READY"
  have hN := (contDiff_nativeThreeHalfNormalDerivativeMulL_commonSupport
    q hq Kq hKq hqz hcalc hF hO hD τ0).contDiffAt.comp (p,t) contDiffAt_snd
  dbg_trace "BOUNDARY_PHASE NORMAL_MULTIPLIER_READY"
  unfold referenceHighSmoothMultiplierBoundaryCommutatorFamily
  dbg_trace "BOUNDARY_PHASE PLUS_FINAL_ENTER"
  exact (contDiffAt_const.clm_comp hV).add hN
  dbg_trace "BOUNDARY_PHASE PLUS_FINAL_RETURNED"

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighSmoothMultiplierStrongDefect_commonSupport_joint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighSmoothMultiplierBoundaryCommutator_commonSupport_joint

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.boundaryTopologyNativeH1Group
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.boundaryTopologyNativeH1Space

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.boundaryTopologyNativeH2Group
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.boundaryTopologyNativeH2Space
