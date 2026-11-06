import Calderon.NativeCoefficientStrongDriftEnergy
import Calderon.ActualReferenceTwoAngleStrongEnergy
import Calderon.ActualReferenceTwoAngleStrongBoundaryTrace
import Calderon.ActualReferenceTwoAngleHarmonicLiftTopology
import Calderon.ActualReferenceTwoAngleNativeWeakLiftCovariance
import Calderon.ActualReferenceRotationStrongIdentification

/-! Two-angle strong/weak identification, by the energy identity and native uniqueness. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeHarmonicH1LiftCompletion NativeHarmonicLiftOrderCoherence
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma firstOrder_referenceTwoAngleHarmonicLiftFamily_eq_nativeWeakHalfLift
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible)
    (hStrong : (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    TauCeti.Wkp.firstOrder 1 (referenceTwoAngleHarmonicLiftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t (harmonicLiftCompletion hF f)) =
    referenceTwoAngleNativeWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hF i j k l t
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) := by
  let f0 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f
  let U : BallH1 := TauCeti.Wkp.firstOrder 1 (referenceTwoAngleHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l t (harmonicLiftCompletion hF f))
  let V : BallH1 := referenceTwoAngleNativeWeakHalfLiftFamily
    g L y0 Φ B ε C ρ H a w hData hF i j k l t f0
  let E0 : BallH1 := harmonicFirstOrderLiftCompletion hF f0
  have hU : E0-U ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    referenceTwoAngleHarmonicLiftFamily_half_boundary_difference
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO i j k l t hStrong f
  have hV : E0-V ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    referenceTwoAngleNativeWeakHalfLiftFamily_affine_difference
      g L y0 Φ B ε C ρ H a w hData hF i j k l t f0
  have hz : U-V ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    sub_mem_nativeZero_of_common_difference E0 U V hU hV
  exact eq_of_native_weak_solution_of_isInvertible
    (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
    (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
    (referenceTwoAngleNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j k l t)
    (referenceTwoAngleNativeZeroEnergy_isInvertible_of_original
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t hOriginal) U V hz
    (fun v => referenceTwoAngleHarmonicLiftFamily_weak_energy
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t hStrong (harmonicLiftCompletion hF f) v)
    (fun v => referenceTwoAngleNativeWeakHalfLiftFamily_weak_solution
      g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t hOriginal f0 v)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.firstOrder_referenceTwoAngleHarmonicLiftFamily_eq_nativeWeakHalfLift
