import Calderon.NativeSmoothMultiplierEnergyCancellation
import Calderon.ActualReferenceCoordinateDefectGain

/-! Upfront: day-oct13/general-boundary-multiplier-commutator-author-oct15-v001/
EXPANSION.md. The actual arbitrary smooth multiplier weak defect and its exact
energy graph. This module does not assert that the defect is in H1_0 or H2. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHalfSmoothMultiplier

def smoothMultiplierDatum (Q : SmoothCoefficientJets 3) : SmoothData :=
  ⟨coefficientValue 3 Q, contDiff_coefficientValue 3 Q⟩

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceSmoothMultiplierWeakDefectFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(smoothMultiplierDatum Q).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (smoothMultiplierDatum Q).1 x‖ ≤ M)
    (p : ℝ × (R3 × ℝ)) : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 :=
  let m := smoothMultiplierDatum Q
  (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p).comp
    (nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg) -
  (TauCeti.W1p.contDiffSMulL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
    m.1 m.2 hM hm hg).comp
    (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p)

theorem referenceSmoothMultiplierWeakDefectFamily_energy_residual
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
    -nativeSmoothMultiplierEnergyResidual
      (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
      (smoothMultiplierDatum Q)
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
      (v : BallH1) := by
  let m := smoothMultiplierDatum Q
  let W : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 :=
    referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p
  let T := nativeHalfSmoothMulL hF hO hD τ0 m hM hm hg
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL m.1 m.2 hM hm hg
  have hSv : S (v : BallH1) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
    dsimp only [S]
    rw [TauCeti.W1p.contDiffSMulL_apply]
    exact TauCeti.W1p.contDiffSMul_mem_w1p0Submodule m.2 hM hm hg v.property
  have hu := referenceWeakHalfLiftFamily_weak_energy_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF p hWeak f
      ⟨S (v : BallH1), hSv⟩
  have hu' := referenceWeakHalfLiftFamily_weak_energy_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF p hWeak (T f) v
  have hcancel := nativeEnergy_smooth_multiplier_difference_integral
    (fun x => a (p,x))
    (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
    (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p)
    m hM hm hg (W f) (v : BallH1)
  let E : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
    referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
  have hsub : E (W (T f)-S (W f)) v = E (W (T f)) v-E (S (W f)) v :=
    congrArg (fun ell : StrongDual ℝ BallH1Zero => ell v)
      (map_sub E (W (T f)) (S (W f)))
  have hval (u : BallH1) : E u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => a (p,x))
        (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
        u (v : BallH1) :=
    referenceWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p u v
  simp only [hval] at hsub
  change TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
    (fun x => a (p,x))
    (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
    (W (T f)-S (W f)) (v : BallH1) = _
  linarith

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothMultiplierDatum
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSmoothMultiplierWeakDefectFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSmoothMultiplierWeakDefectFamily_energy_residual
