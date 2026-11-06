import Calderon.ActualReferenceTwoAngleStrongEnergy
import Calderon.ActualReferenceTwoAngleHarmonicLiftTopology
import Calderon.ActualReferenceRotationStrongIdentification
import Calderon.NativeHalfTraceRightInverse

/-! Upfront: high-degree-rotation-author-oct15-v001/
PARTITION-two-angle-H2-Green-boundary-v096.md. Exact existing pointwise claims. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open NativeFullSharpHalfTrace NativeHalfTraceRightInverse
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeHarmonicH1LiftCompletion NativeHarmonicLiftOrderCoherence
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceTwoAngleHarmonicLiftFamily_weak_energy
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hi : (referenceTwoAngleStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible)
    (E : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
      (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
      0 (TauCeti.Wkp.firstOrder 1
        (referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t E)) (v : BallH1) = 0 := by
  have he := referenceTwoAngleOrdinaryStrongFamily_energy g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
    (referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t E) v
  rw [referenceTwoAngleHarmonicLiftFamily_kernel g L y0 Φ B ε C ρ H a w hData hcalc i j k l t hi E] at he
  simpa only [TauCeti.PDE.dirichletForcing_apply,TauCeti.Wkp.value_zero,inner_zero_left] using he.symm

lemma referenceTwoAngleHarmonicLiftFamily_boundary_difference
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hi : (referenceTwoAngleStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible)
    (E : BallSobolev 2) :
    TauCeti.Wkp.firstOrder 1
      (E-referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t E) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  let c : StrongDirichletSpace 0 :=
    (referenceTwoAngleStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).inverse
      (referenceTwoAngleOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t E)
  have he : referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t E =
      E-(c : BallSobolev 2) := by
    change guardedHarmonicLiftFamily _ _ _ t E = _
    rw [guardedHarmonicLiftFamily_eq _ _ _ t hi,harmonicLiftL_apply]
    rfl
  have hm : E-referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t E ∈
      strongDirichletSubmodule 0 := by
    rw [he,sub_sub_cancel]
    exact c.property
  exact (mem_strongDirichletSubmodule 0 _).mp hm

lemma referenceTwoAngleHarmonicLiftFamily_half_boundary_difference
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hi : (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible)
    (f : SphereSobolev (3/2 : ℝ)) :
    harmonicFirstOrderLiftCompletion hF (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) -
      TauCeti.Wkp.firstOrder 1 (referenceTwoAngleHarmonicLiftFamily
        g L y0 Φ B ε C ρ H a w hData hcalc i j k l t (harmonicLiftCompletion hF f)) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  have hd := referenceTwoAngleHarmonicLiftFamily_boundary_difference
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l t hi (harmonicLiftCompletion hF f)
  change TauCeti.Wkp.firstOrderL 1 (harmonicLiftCompletion hF f -
    referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
      (harmonicLiftCompletion hF f)) ∈ _ at hd
  rw [map_sub,firstOrder_harmonicLiftCompletion hF hO] at hd
  exact hd

lemma nativeHalfTraceL_firstOrder_referenceTwoAngleHarmonicLiftFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hStrong : (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    nativeHalfTraceL hF hO hD τ0 (TauCeti.Wkp.firstOrder 1
      (referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t
        (harmonicLiftCompletion hF f))) =
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f := by
  let f0 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f
  let U : BallH1 := TauCeti.Wkp.firstOrder 1 (referenceTwoAngleHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l t (harmonicLiftCompletion hF f))
  let E0 : BallH1 := harmonicFirstOrderLiftCompletion hF f0
  have hz : E0-U ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    referenceTwoAngleHarmonicLiftFamily_half_boundary_difference
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO i j k l t hStrong f
  let c : BallH1Zero := ⟨E0-U,hz⟩
  have ht := nativeHalfTraceL_zeroDirichlet hF hO hD τ0 c
  change nativeHalfTraceL hF hO hD τ0 (E0-U)=0 at ht
  have hsub : nativeHalfTraceL hF hO hD τ0 E0 - nativeHalfTraceL hF hO hD τ0 U = 0 := by
    simpa only [map_sub] using ht
  exact (sub_eq_zero.mp hsub).symm.trans
    (nativeHalfTraceL_harmonicFirstOrderLiftCompletion hF hO hD τ0 f0)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleHarmonicLiftFamily_weak_energy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleHarmonicLiftFamily_boundary_difference
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleHarmonicLiftFamily_half_boundary_difference
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHalfTraceL_firstOrder_referenceTwoAngleHarmonicLiftFamily
