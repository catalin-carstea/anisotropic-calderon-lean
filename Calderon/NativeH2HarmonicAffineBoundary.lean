import Calderon.NativeH2AffineCorrection
import Calderon.NativeZeroBoundaryDifferenceTransportDiagnostic
import Calderon.NativeHarmonicLiftOrderCoherence

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicLiftCompletion NativeHarmonicH1LiftCompletion
  NativeHarmonicLiftOrderCoherence

lemma nativeH2HarmonicAffineCorrection_zero_boundary_difference
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (R : BallSobolev 0 →L[ℝ] StrongDirichletSpace 0)
    (S : BallSobolev 2 →L[ℝ] BallSobolev 0) (f : SphereSobolev (3/2:ℝ)) :
    harmonicFirstOrderLiftCompletion hF (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)-
      TauCeti.Wkp.firstOrder 1
        (nativeH2AffineCorrectionL nativeStrongH2InclusionL R S (harmonicLiftCompletion hF) f) ∈
        TauCeti.w1p0Submodule volume ballOpens 2 := by
  have hJ : ∀ z : StrongDirichletSpace 0, TauCeti.Wkp.firstOrder 1 (nativeStrongH2InclusionL z) =
      (strongDirichletProjectionL 0 z : BallH1) := by
    intro z
    exact (congrArg (fun U : BallSobolev 2 => TauCeti.Wkp.firstOrder 1 U)
      (nativeStrongH2InclusionL_apply z)).trans (strongDirichletProjectionL_apply 0 z).symm
  have hZero := nativeH2AffineCorrection_zero_difference nativeStrongH2InclusionL R S
    (harmonicLiftCompletion hF) hJ f
  have hFirstL : TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 1
      (harmonicLiftCompletion hF f) = TauCeti.Wkp.firstOrder 1 (harmonicLiftCompletion hF f) := rfl
  have hFree := hFirstL.symm.trans (firstOrder_harmonicLiftCompletion hF hO f)
  exact nativeZeroBoundaryDifference_transport _ _ _ hFree hZero

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2HarmonicAffineCorrection_zero_boundary_difference
