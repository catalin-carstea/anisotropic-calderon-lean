import Calderon.NativeH2HarmonicAffineBoundary
import Calderon.NativeZeroBoundaryDifferenceTransportDiagnostic
import Calderon.NativeH2AffineCorrection
import Calderon.NativeSupportedAdjointH2Inverse
import Calderon.NativeAdjointRepresentativeForcingAlignmentDiagnostic
import Calderon.NativeSupportedAdjointStrongForcing
import Calderon.NativeCoefficientWeakHalfLift
import Calderon.NativeHarmonicLiftOrderCoherence
import Calderon.CoefficientMatrixRegularity

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicLiftCompletion NativeHarmonicH1LiftCompletion
  NativeHarmonicLiftOrderCoherence
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! Exact three-half datum, literal formal-adjoint coefficients and same harmonic completion. -/

attribute [local irreducible] nativeCoefficientWeakEnergyL nativeSupportedAdjointStrongL
  nativeZeroCoefficientEnergyL nativeSupportedOriginalZeroEnergyL
  harmonicLiftCompletion harmonicFirstOrderLiftCompletion nativeH2AffineCorrectionL

#eval (do
  let out ← IO.getStdout
  out.putStrLn "NONZERO DECL BEGIN"
  out.flush : IO Unit)

lemma exists_nativeSupportedAdjoint_nonzero_H2_lift
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (F : SmoothCoefficientMatrix 2) (lam Lam : ℝ)
    (hell : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (coefficientMatrixField 2 F) lam Lam)
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x, x ∉ K → beta x = 0)
    (hA : (nativeSupportedOriginalZeroEnergyL (coefficientMatrixField 2 F)
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta).IsInvertible)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) :
    ∃ W : SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2, ∀ f : SphereSobolev (3/2:ℝ),
      harmonicFirstOrderLiftCompletion hF
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)-
          TauCeti.Wkp.firstOrder 1 (W f) ∈ TauCeti.w1p0Submodule volume ballOpens 2 ∧
      ∀ v : BallH1Zero,
        TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
          (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta)
          (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
          (TauCeti.Wkp.firstOrder 1 (W f)) (v : BallH1) = 0 := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "NONZERO PROOF ENTER"
    out.flush
  obtain ⟨R,hR⟩ := exists_nativeSupportedAdjoint_H2_inverse τ0 hcalc hreg
    (coefficientMatrixField 2 F) lam Lam (contDiffOn_coefficientMatrixField_closedBall 2 F) hell
    (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) C beta hbeta K hK hz hA
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "NONZERO INVERSE WITNESS MADE"
    out.flush
  let a := coefficientMatrixField 2 F
  let hp := memLp_coefficientMatrixEnergyIntegrand_of_smooth F
  let c := fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x
  let hc := nativeSupportedAdjointEnergyMemLp a hp C beta hbeta
  let Q := nativeCoefficientWeakEnergyL (fun x => (a x)ᵀ) (-beta) c hc
  let S := nativeSupportedAdjointStrongL hcalc F C beta hbeta K hK hz
  let P := harmonicLiftCompletion hF
  let J := nativeStrongH2InclusionL
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "NONZERO ALIASES MADE"
    out.flush
  have hJ : ∀ z : StrongDirichletSpace 0, TauCeti.Wkp.firstOrder 1 (J z) =
      (strongDirichletProjectionL 0 z : BallH1) := by
    intro z
    exact (congrArg (fun U : BallSobolev 2 => TauCeti.Wkp.firstOrder 1 U)
      (nativeStrongH2InclusionL_apply z)).trans (strongDirichletProjectionL_apply 0 z).symm
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "NONZERO J MADE"
    out.flush
  have hS : ∀ (U : BallSobolev 2) (v : BallH1Zero), Q (TauCeti.Wkp.firstOrder 1 U) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (S U) v := by
    intro U v
    exact (nativeCoefficientWeakEnergyL_apply (fun x => (a x)ᵀ) (-beta) c hc _ v).trans
      (nativeSupportedAdjointStrongL_energy hcalc F C beta hbeta K hK hz U v).symm
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "NONZERO S FORCING MADE"
    out.flush
  have hRQ : ∀ (f : BallSobolev 0) (v : BallH1Zero),
      Q (strongDirichletProjectionL 0 (R f) : BallH1) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f v := by
    intro f v
    exact nativeWeakEnergy_strongRepresentative_forcing (fun x => (a x)ᵀ) (-beta) c hc R hR f v
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "NONZERO R FORCING MADE"
    out.flush
  let W := nativeH2AffineCorrectionL J R S P
  refine ⟨W,?_⟩
  intro f
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "NONZERO W EXISTENTIAL MADE"
    out.flush
  have hBoundary := nativeH2HarmonicAffineCorrection_zero_boundary_difference hF hO R S f
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "NONZERO CONCRETE BOUNDARY MADE"
    out.flush
  refine ⟨hBoundary,?_⟩
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "NONZERO AND PAIR MADE"
    out.flush
  intro v
  exact (nativeCoefficientWeakEnergyL_apply (fun x => (a x)ᵀ) (-beta) c hc
    (TauCeti.Wkp.firstOrder 1 (W f)) v).symm.trans
      (nativeH2AffineCorrection_kernel J R S P hJ Q hS hRQ f v)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "NONZERO BODY COMPLETE"
    out.flush

#eval (do
  let out ← IO.getStdout
  out.putStrLn "NONZERO DECL END"
  out.flush : IO Unit)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_nativeSupportedAdjoint_nonzero_H2_lift
