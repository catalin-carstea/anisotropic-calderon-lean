import Calderon.NativeCoordinateForcingEnergy
import Calderon.ActualReferenceNativeWeakHalfLift

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError

/-! Upfront expansion: EXPANSION-actual-coordinate-forcing-family-joint-v001.md. -/
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceCoordinateForcingPrincipalJets (p : ℝ × (R3 × ℝ)) : SmoothCoefficientMatrix 2 :=
  commonSupportMatrixFamily 2 a
    (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p

def referenceCoordinateForcingDriftJets (p : ℝ × (R3 × ℝ)) (i : Fin 3) : SmoothCoefficientJets 1 :=
  let hc := jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData
  commonSupportCoefficientFamily 1 (fun t => conformalReferenceWeightedFramedDrift g L Φ H w t i)
    (((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff).comp hc.1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun p x hx => by rw [hc.2 p x hx]; rfl) p

theorem coefficientMatrixField_referenceCoordinateForcingPrincipalJets (p : ℝ × (R3 × ℝ)) :
    coefficientMatrixField 2 (referenceCoordinateForcingPrincipalJets g L y0 Φ B ε C ρ H a w hData p) =
      fun x => a (p,x) :=
  coefficientMatrixField_commonSupportMatrixFamily 2 a
    (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).2.2.2.1 p

theorem nativeSmoothDriftField_referenceCoordinateForcingDriftJets (p : ℝ × (R3 × ℝ)) :
    nativeSmoothDriftField (referenceCoordinateForcingDriftJets g L y0 Φ B ε C ρ H a w hData p) =
      fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x) := by
  funext x
  apply PiLp.ext
  intro i
  rw [nativeSmoothDriftField_coordinate]
  dsimp only [referenceCoordinateForcingDriftJets]
  let hc := jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData
  exact coefficientValue_commonSupportCoefficientFamily 1
    (fun t => conformalReferenceWeightedFramedDrift g L Φ H w t i)
    (((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff).comp hc.1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun p x hx => by rw [hc.2 p x hx]; rfl) p x

def referenceCoordinateCommutatorForcingFamily (hcalc : FixedSobolevCalculus)
    (k : Fin 3) (p : ℝ × (R3 × ℝ)) :
    BallH1 →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
  nativeCoordinateCommutatorForcingL hcalc
    (referenceCoordinateForcingPrincipalJets g L y0 Φ B ε C ρ H a w hData p)
    (referenceCoordinateForcingDriftJets g L y0 Φ B ε C ρ H a w hData p) k

theorem referenceEnergy_coordinate_product_difference_forcing
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ))
    (k : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(coordinateSmoothDatum k).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coordinateSmoothDatum k).1 x‖ ≤ M)
    (u : BallH1) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
      (TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2 hM hm hg u)
      (v : BallH1) -
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 u
      (TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2 hM hm hg (v : BallH1)) =
      -⟪referenceCoordinateCommutatorForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc k p u,
        TauCeti.W1p.value (v : BallH1)⟫_ℝ := by
  let F : SmoothCoefficientMatrix 2 := referenceCoordinateForcingPrincipalJets g L y0 Φ B ε C ρ H a w hData p
  let G : Fin 3 → SmoothCoefficientJets 1 := referenceCoordinateForcingDriftJets g L y0 Φ B ε C ρ H a w hData p
  have hA : coefficientMatrixField 2 F = fun x => a (p,x) :=
    coefficientMatrixField_referenceCoordinateForcingPrincipalJets g L y0 Φ B ε C ρ H a w hData p
  have hB : nativeSmoothDriftField G = fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x) :=
    nativeSmoothDriftField_referenceCoordinateForcingDriftJets g L y0 Φ B ε C ρ H a w hData p
  have hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 F x) (nativeSmoothDriftField G x) 0) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
    simpa only [hA,hB] using referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p
  have he := nativeEnergy_coordinate_product_difference_forcing hcalc F G hcoeff k hM hm hg u v
  change _ = -⟪nativeCoordinateCommutatorForcingL hcalc F G k u,TauCeti.W1p.value (v : BallH1)⟫_ℝ
  simpa only [hA,hB] using he

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
