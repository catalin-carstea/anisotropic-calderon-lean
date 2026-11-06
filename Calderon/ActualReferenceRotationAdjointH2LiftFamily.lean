import Calderon.ActualReferenceRotationAdjointStrongInverse
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

def referenceRotationAdjointH2LiftFamily (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) : SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2 :=
  nativeH2AffineCorrectionL nativeStrongH2InclusionL
    (referenceRotationAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).inverse
    (referenceRotationAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t)
    (harmonicLiftCompletion hF)

lemma contDiffOn_referenceRotationAdjointH2LiftFamily_invertibleLocus
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j : Fin 3) :
    ContDiffOn ℝ ∞ (referenceRotationAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j)
      (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  have hInv := contDiffOn_referenceRotationAdjointStrongInverse_originalLocus g L y0 Φ B ε C ρ H a w hData
    hcalc hreg hF hO hD τ0 i j
  have hS : ContDiffOn ℝ ∞
      (referenceRotationAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j)
      (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
    (contDiff_referenceRotationAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j).contDiffOn
  unfold referenceRotationAdjointH2LiftFamily nativeH2AffineCorrectionL
  exact (contDiffOn_const.sub (contDiffOn_const.clm_comp (hInv.clm_comp hS))).clm_comp contDiffOn_const

lemma referenceRotationAdjointH2LiftFamily_zero_boundary_difference
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (f : SphereSobolev (3/2:ℝ)) :
    harmonicFirstOrderLiftCompletion hF (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)-
      TauCeti.Wkp.firstOrder 1 (referenceRotationAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f) ∈
      TauCeti.w1p0Submodule volume ballOpens 2 :=
  nativeH2HarmonicAffineCorrection_zero_boundary_difference hF hO
    (referenceRotationAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).inverse
    (referenceRotationAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t) f

lemma referenceRotationAdjointH2LiftFamily_strong_kernel
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    referenceRotationAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t
      (referenceRotationAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f) = 0 := by
  let S := referenceRotationAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t
  let A := referenceRotationAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t
  have hi := referenceRotationAdjointStrongDirichletFamily_isInvertible_of_original g L y0 Φ B ε C ρ H a w hData
    τ0 hcalc hreg i j t.1 t.2 hOriginal
  have hRight : ∀ y : BallSobolev 0, S (nativeStrongH2InclusionL (A.inverse y))=y := by
    intro y
    exact congrArg (fun T : BallSobolev 0 →L[ℝ] BallSobolev 0 => T y) hi.self_comp_inverse
  exact nativeH2AffineCorrection_strong_kernel nativeStrongH2InclusionL A.inverse S
    (harmonicLiftCompletion hF) hRight f

lemma referenceRotationAdjointH2LiftFamily_homogeneous_weak_energy
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ) (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
      (fun x => -nativeSupportedDriftDivergence (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x)
      (TauCeti.Wkp.firstOrder 1 (referenceRotationAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f)) (v : BallH1) = 0 := by
  have hE := referenceRotationAdjointOrdinaryStrongFamily_energy g L y0 Φ B ε C ρ H a w hData i j hcalc t
    (referenceRotationAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f) v
  have hK := referenceRotationAdjointH2LiftFamily_strong_kernel g L y0 Φ B ε C ρ H a w hData
    τ0 hcalc hreg hF i j t hOriginal f
  have hZero := congrArg (fun y : BallSobolev 0 => TauCeti.PDE.dirichletForcing
    (mu := (volume : Measure R3)) (Omega := ballOpens) y v) hK
  have hz : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (0 : BallSobolev 0) v=0 := by rw [TauCeti.PDE.dirichletForcing_apply,inner_zero_left]
  exact hE.symm.trans (hZero.trans hz)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointH2LiftFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceRotationAdjointH2LiftFamily_invertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointH2LiftFamily_zero_boundary_difference
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointH2LiftFamily_strong_kernel
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointH2LiftFamily_homogeneous_weak_energy
