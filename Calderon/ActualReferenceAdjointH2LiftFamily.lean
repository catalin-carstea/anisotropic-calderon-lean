import Calderon.ActualReferenceAdjointStrongInverse
import Calderon.NativeH2AffineStrongKernel
import Calderon.NativeH2HarmonicAffineBoundary

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceAdjointH2LiftFamily (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) : SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2 :=
  nativeH2AffineCorrectionL nativeStrongH2InclusionL
    (referenceAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc p).inverse
    (referenceAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc p)
    (harmonicLiftCompletion hF)

lemma contDiffOn_referenceAdjointH2LiftFamily_invertibleLocus
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiffOn ℝ ∞ (referenceAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  have hInv := contDiffOn_referenceAdjointStrongInverse_invertibleLocus g L y0 Φ B ε C ρ H a w hData
    hcalc hreg hF hO hD τ0
  have hS : ContDiffOn ℝ ∞
      (referenceAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc)
      (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
    (contDiff_referenceAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc).contDiffOn
  unfold referenceAdjointH2LiftFamily nativeH2AffineCorrectionL
  exact (contDiffOn_const.sub (contDiffOn_const.clm_comp (hInv.clm_comp hS))).clm_comp contDiffOn_const

lemma referenceAdjointH2LiftFamily_zero_boundary_difference
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (3/2:ℝ)) :
    harmonicFirstOrderLiftCompletion hF (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)-
      TauCeti.Wkp.firstOrder 1 (referenceAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) ∈
      TauCeti.w1p0Submodule volume ballOpens 2 :=
  nativeH2HarmonicAffineCorrection_zero_boundary_difference hF hO
    (referenceAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc p).inverse
    (referenceAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc p) f

lemma referenceAdjointH2LiftFamily_strong_kernel
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    referenceAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc p
      (referenceAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) = 0 := by
  let S := referenceAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc p
  let A := referenceAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc p
  have hi := referenceAdjointStrongDirichletFamily_isInvertible g L y0 Φ B ε C ρ H a w hData
    τ0 hcalc hreg p hOriginal
  have hRight : ∀ y : BallSobolev 0, S (nativeStrongH2InclusionL (A.inverse y))=y := by
    intro y
    exact congrArg (fun T : BallSobolev 0 →L[ℝ] BallSobolev 0 => T y) hi.self_comp_inverse
  exact nativeH2AffineCorrection_strong_kernel nativeStrongH2InclusionL A.inverse S
    (harmonicLiftCompletion hF) hRight f

lemma referenceAdjointH2LiftFamily_homogeneous_weak_energy
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (a (p,x))ᵀ) (fun x => -conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
      (fun x => -nativeSupportedDriftDivergence (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x)
      (TauCeti.Wkp.firstOrder 1 (referenceAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)) (v : BallH1) = 0 := by
  have hE := referenceAdjointOrdinaryStrongFamily_energy g L y0 Φ B ε C ρ H a w hData hcalc p
    (referenceAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) v
  have hK := referenceAdjointH2LiftFamily_strong_kernel g L y0 Φ B ε C ρ H a w hData
    τ0 hcalc hreg hF p hOriginal f
  have hZero := congrArg (fun y : BallSobolev 0 => TauCeti.PDE.dirichletForcing
    (mu := (volume : Measure R3)) (Omega := ballOpens) y v) hK
  have hz : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (0 : BallSobolev 0) v=0 := by rw [TauCeti.PDE.dirichletForcing_apply,inner_zero_left]
  exact hE.symm.trans (hZero.trans hz)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointH2LiftFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceAdjointH2LiftFamily_invertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointH2LiftFamily_zero_boundary_difference
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointH2LiftFamily_strong_kernel
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointH2LiftFamily_homogeneous_weak_energy
