import Calderon.ActualReferenceRotationSupportedZeroEnergyIdentity
import Calderon.ActualReferenceRotationPrincipalEllipticity
import Calderon.NativeSupportedAdjointStrongInvertibility
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma nativeReferenceRotationAdjointStrongDirichletL_isInvertible
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (nativeSupportedAdjointStrongDirichletL hcalc
      (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j (θ,p)) 0
      (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) ((θ,p),x))
      (SpatialJetFields.contDiff_spatial_slice _
        (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1 (θ,p))
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      ((referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).2 (θ,p))).IsInvertible := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL ROTATED ADJOINT STRONG INVERSE PROOF ENTER"
    out.flush
  let F := referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j (θ,p)
  let beta : R3 → R3 := fun x => coordinateRotationDriftFamily i j
    (conformalReferenceWeightedFramedDrift g L Φ H w) ((θ,p),x)
  have hbeta : ContDiff ℝ ∞ beta := SpatialJetFields.contDiff_spatial_slice _
    (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1 (θ,p)
  have hz : ∀ x, x ∉ closedBall (0 : R3) 3 → beta x = 0 :=
    (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).2 (θ,p)
  obtain ⟨lam,Lam,hUE⟩ := exists_referenceRotationPrincipal_uniformlyElliptic
    g L y0 Φ B ε C ρ H a w hData i j θ p
  have hField := coefficientMatrixField_referenceRotationPrincipalJetsFamily
    g L y0 Φ B ε C ρ H a w hData 2 i j (θ,p)
  have hUEF : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (coefficientMatrixField 2 F) lam Lam :=
    Eq.mp (congrArg (fun A : MatrixField =>
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) A lam Lam) hField.symm) hUE
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL ROTATED ADJOINT STRONG INVERSE UE COMPLETE"
    out.flush
  have hA : (nativeSupportedOriginalZeroEnergyL (coefficientMatrixField 2 F)
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) 0 beta hbeta).IsInvertible :=
    referenceRotationSupportedOriginalZeroEnergyL_isInvertible_of_original
      g L y0 Φ B ε C ρ H a w hData hcalc i j θ p hOriginal
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL ROTATED ADJOINT STRONG INVERSE ORIGINAL INVERSE COMPLETE"
    out.flush
  have hInv := nativeSupportedAdjointStrongDirichletL_isInvertible τ0 hcalc hreg F lam Lam hUEF 0 beta hbeta
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) hz hA
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL ROTATED ADJOINT STRONG INVERSE NATIVE RESULT COMPLETE"
    out.flush
  exact hInv
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ACTUAL ROTATED ADJOINT STRONG INVERSE BODY COMPLETE"
    out.flush

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeReferenceRotationAdjointStrongDirichletL_isInvertible
