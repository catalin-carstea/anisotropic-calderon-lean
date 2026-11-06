import Calderon.ActualReferenceTwoAngleAdjointStrongInverse
import Calderon.NativeH2AffineStrongKernel
import Calderon.NativeH2HarmonicAffineBoundary

/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-adjoint-H2-lift-v047.md. -/
set_option autoImplicit false
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

def referenceTwoAngleAdjointH2LiftFamily (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) : SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2 :=
  nativeH2AffineCorrectionL nativeStrongH2InclusionL
    (referenceTwoAngleAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).inverse
    (referenceTwoAngleAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t)
    (harmonicLiftCompletion hF)

lemma contDiffOn_referenceTwoAngleAdjointH2LiftFamily_invertibleLocus
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3) :
    ContDiffOn ℝ ∞ (referenceTwoAngleAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l)
      (Set.univ ×ˢ (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)) := by
  have hInv := contDiffOn_referenceTwoAngleAdjointStrongInverse_originalLocus g L y0 Φ B ε C ρ H a w hData
    hcalc hreg hF hO hD τ0 i j k l
  have hS : ContDiffOn ℝ ∞
      (referenceTwoAngleAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l)
      (Set.univ ×ˢ (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)) :=
    (contDiff_referenceTwoAngleAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l).contDiffOn
  unfold referenceTwoAngleAdjointH2LiftFamily nativeH2AffineCorrectionL
  exact (contDiffOn_const.sub (contDiffOn_const.clm_comp (hInv.clm_comp hS))).clm_comp contDiffOn_const

lemma referenceTwoAngleAdjointH2LiftFamily_zero_boundary_difference
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (f : SphereSobolev (3/2:ℝ)) :
    harmonicFirstOrderLiftCompletion hF (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)-
      TauCeti.Wkp.firstOrder 1 (referenceTwoAngleAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t f) ∈
      TauCeti.w1p0Submodule volume ballOpens 2 :=
  nativeH2HarmonicAffineCorrection_zero_boundary_difference hF hO
    (referenceTwoAngleAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).inverse
    (referenceTwoAngleAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t) f

lemma referenceTwoAngleAdjointH2LiftFamily_strong_kernel
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    referenceTwoAngleAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
      (referenceTwoAngleAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t f) = 0 := by
  let S := referenceTwoAngleAdjointOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
  let A := referenceTwoAngleAdjointStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
  have hi := referenceTwoAngleAdjointStrongDirichletFamily_isInvertible_of_original g L y0 Φ B ε C ρ H a w hData
    τ0 hcalc hreg i j k l t.1 t.2.1 t.2.2 hOriginal
  have hRight : ∀ y : BallSobolev 0, S (nativeStrongH2InclusionL (A.inverse y))=y := by
    intro y
    exact congrArg (fun T : BallSobolev 0 →L[ℝ] BallSobolev 0 => T y) hi.self_comp_inverse
  exact nativeH2AffineCorrection_strong_kernel nativeStrongH2InclusionL A.inverse S
    (harmonicLiftCompletion hF) hRight f

lemma referenceTwoAngleAdjointH2LiftFamily_homogeneous_weak_energy
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (referenceTwoAnglePrincipalFamily a i j k l (t,x))ᵀ) (fun x => -referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
      (fun x => -nativeSupportedDriftDivergence (fun y => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,y)) x)
      (TauCeti.Wkp.firstOrder 1 (referenceTwoAngleAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t f)) (v : BallH1) = 0 := by
  have hE := referenceTwoAngleAdjointOrdinaryStrongFamily_energy g L y0 Φ B ε C ρ H a w hData i j k l hcalc t
    (referenceTwoAngleAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t f) v
  have hK := referenceTwoAngleAdjointH2LiftFamily_strong_kernel g L y0 Φ B ε C ρ H a w hData
    τ0 hcalc hreg hF i j k l t hOriginal f
  have hZero := congrArg (fun y : BallSobolev 0 => TauCeti.PDE.dirichletForcing
    (mu := (volume : Measure R3)) (Omega := ballOpens) y v) hK
  have hz : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (0 : BallSobolev 0) v=0 := by rw [TauCeti.PDE.dirichletForcing_apply,inner_zero_left]
  exact hE.symm.trans (hZero.trans hz)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointH2LiftFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceTwoAngleAdjointH2LiftFamily_invertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointH2LiftFamily_zero_boundary_difference
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointH2LiftFamily_strong_kernel
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointH2LiftFamily_homogeneous_weak_energy
