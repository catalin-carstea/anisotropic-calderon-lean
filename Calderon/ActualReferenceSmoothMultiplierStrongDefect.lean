import Calderon.ActualReferenceSmoothMultiplierZeroTrace
import Calderon.ActualReferenceSmoothMultiplierForcingEnergy
import Calderon.UnitBallValueTraceKernel

/-! Upfront: day-oct13/general-boundary-multiplier-commutator-author-oct15-v001/
EXPANSION-strong-gain-conditional-v006.md and EXPANSION-strong-gain-adopted-v007.md.
The standard trace-kernel property remains an explicit parameter. The actual
zero-boundary membership and SAME strong inverse identity are conclusions. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem referenceSmoothMultiplierWeakDefectFamily_mem_zero
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0)
    (Q : SmoothCoefficientJets 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(smoothMultiplierDatum Q).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (smoothMultiplierDatum Q).1 x‖ ≤ M)
    (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (1/2 : ℝ)) :
    referenceSmoothMultiplierWeakDefectFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 Q hM hm hg p f ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  apply (hKernel _).mp
  exact valueTraceL_referenceSmoothMultiplierWeakDefectFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q hM hm hg p f

def referenceSmoothMultiplierStrongDefectFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] BallSobolev 2 :=
  (strongDirichletSubmodule 0).toSubmodule.subtypeL.comp
    ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).inverse.comp
      ((referenceSmoothMultiplierCommutatorForcingFamily
        g L y0 Φ B ε C ρ H a w hData hcalc Q p).comp
        (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p)))

theorem firstOrder_referenceSmoothMultiplierStrongDefectFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hKernel : UnitBallValueTraceKernel τ0)
    (Q : SmoothCoefficientJets 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(smoothMultiplierDatum Q).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (smoothMultiplierDatum Q).1 x‖ ≤ M)
    (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (1/2 : ℝ)) :
    TauCeti.Wkp.firstOrder 1
      (referenceSmoothMultiplierStrongDefectFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF Q p f) =
    referenceSmoothMultiplierWeakDefectFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 Q hM hm hg p f := by
  let U : BallH1Zero :=
    ⟨referenceSmoothMultiplierWeakDefectFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 Q hM hm hg p f,
      referenceSmoothMultiplierWeakDefectFamily_mem_zero
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q hM hm hg p f⟩
  let F : BallSobolev 0 :=
    referenceSmoothMultiplierCommutatorForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc Q p
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
  have hU := eq_referenceStrongDriftFamily_inverse_projection_of_weak_forcing
    g L y0 Φ B ε C ρ H a w hData hcalc τ0 p.1 p.2 hStrong hWeak F U
    (fun v => referenceSmoothMultiplierWeakDefectFamily_energy_forcing
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q hM hm hg p hWeak f v)
  have hv := congrArg (fun u : BallH1Zero => (u : BallH1)) hU
  exact hv.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSmoothMultiplierWeakDefectFamily_mem_zero
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSmoothMultiplierStrongDefectFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.firstOrder_referenceSmoothMultiplierStrongDefectFamily
