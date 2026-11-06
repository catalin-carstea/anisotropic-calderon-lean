import Calderon.NativeSmoothMultiplierForcingEnergy
import Calderon.ActualReferenceSmoothMultiplierWeakDefectEnergy

/-! The forcing of an arbitrary smooth multiplier and its weak-defect graph. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceSmoothMultiplierCommutatorForcingFamily
    (hcalc : FixedSobolevCalculus) (Q : SmoothCoefficientJets 3)
    (p : ℝ × (R3 × ℝ)) :
    BallH1 →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
  nativeBulkMultiplierCommutatorForcingL hcalc
    (referenceCoordinateForcingPrincipalJets g L y0 Φ B ε C ρ H a w hData p)
    (referenceCoordinateForcingDriftJets g L y0 Φ B ε C ρ H a w hData p) Q

attribute [local irreducible] referenceWeakHalfLiftFamily
  referenceSmoothMultiplierWeakDefectFamily referenceCoordinateForcingPrincipalJets
  referenceCoordinateForcingDriftJets nativeBulkMultiplierCommutatorForcingL

theorem referenceSmoothMultiplierWeakDefectFamily_energy_forcing
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(smoothMultiplierDatum Q).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (smoothMultiplierDatum Q).1 x‖ ≤ M)
    (p : ℝ × (R3 × ℝ))
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (1/2 : ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
      (referenceSmoothMultiplierWeakDefectFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 Q hM hm hg p f) (v : BallH1) =
    ⟪referenceSmoothMultiplierCommutatorForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc Q p
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f),
      TauCeti.W1p.value (v : BallH1)⟫_ℝ := by
  let U : BallH1 := referenceWeakHalfLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF p f
  let F : SmoothCoefficientMatrix 2 := referenceCoordinateForcingPrincipalJets
    g L y0 Φ B ε C ρ H a w hData p
  let G : Fin 3 → SmoothCoefficientJets 1 := referenceCoordinateForcingDriftJets
    g L y0 Φ B ε C ρ H a w hData p
  let m : SmoothData := smoothMultiplierDatum Q
  have hA : coefficientMatrixField 2 F = fun x => a (p,x) :=
    coefficientMatrixField_referenceCoordinateForcingPrincipalJets
      g L y0 Φ B ε C ρ H a w hData p
  have hB : nativeSmoothDriftField G =
      fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x) :=
    nativeSmoothDriftField_referenceCoordinateForcingDriftJets
      g L y0 Φ B ε C ρ H a w hData p
  have hFields : nativeSmoothMultiplierEnergyResidual
      (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 m U (v : BallH1) =
      nativeSmoothMultiplierEnergyResidual (coefficientMatrixField 2 F)
        (nativeSmoothDriftField G) 0 m U (v : BallH1) :=
    congrArg₂ (fun A beta => nativeSmoothMultiplierEnergyResidual A beta 0 m U (v : BallH1))
      hA.symm hB.symm
  have hLink : nativeSmoothMultiplierEnergyResidual (coefficientMatrixField 2 F)
      (nativeSmoothDriftField G) 0 m U (v : BallH1) =
      -⟪nativeBulkMultiplierCommutatorForcingL hcalc F G Q U,
        TauCeti.W1p.value (v : BallH1)⟫_ℝ :=
    nativeBulkMultiplierEnergyResidual_eq_neg_forcing hcalc F G Q U v
  have hEnergy := referenceSmoothMultiplierWeakDefectFamily_energy_residual
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q hM hm hg p hWeak f v
  have hNegative := congrArg (fun z : ℝ => -z) (hFields.trans hLink)
  have hCancel : -nativeSmoothMultiplierEnergyResidual
      (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 m U (v : BallH1) =
      ⟪nativeBulkMultiplierCommutatorForcingL hcalc F G Q U,
        TauCeti.W1p.value (v : BallH1)⟫_ℝ :=
    hNegative.trans (neg_neg _)
  exact hEnergy.trans hCancel

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSmoothMultiplierCommutatorForcingFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSmoothMultiplierWeakDefectFamily_energy_forcing
