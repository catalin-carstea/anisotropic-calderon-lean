import Calderon.NativeWeakLiftUniquenessAlgebra
import Calderon.ActualReferenceWeakDirichletEvaluation
import Calderon.CompactParameterReferenceWeakDriftCoercivity
import Calderon.CoerciveFunctionalInverseEquality
import Calderon.NativeHarmonicH1LiftTraceCompatibility
import Calderon.NativeZeroValueTrace

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion
  NativeHarmonicH1LiftTraceCompatibility SpectralCoreRegularity
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma isCoercive_referenceWeakDirichletEnergyFamily
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ)) (lam : ℝ)
    (hs : UnitBallSmallDriftData (fun z => a (p,z))
      (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) lam) :
    IsCoercive (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p) := by
  refine ⟨3*lam/40,hs.2.1,?_⟩
  intro v
  rw [referenceWeakDirichletEnergyFamily_apply]
  exact hs.2.2.1 v

lemma isInvertible_referenceWeakDirichletEnergyFamily
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ)) (lam : ℝ)
    (hs : UnitBallSmallDriftData (fun z => a (p,z))
      (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) lam) :
    (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible :=
  (isInvertible_and_inverse_eq_functionalInverse _
    (isCoercive_referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p lam hs)).1

def referenceWeakHalfLiftFamily (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 :=
  ((ContinuousLinearMap.id ℝ BallH1) -
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL.comp
      ((functionalInverse (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)).comp
        (referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p))).comp
    (harmonicFirstOrderLiftCompletion hF)

lemma referenceWeakHalfLiftFamily_apply (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (1/2:ℝ)) :
    referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f =
      harmonicFirstOrderLiftCompletion hF f -
        (functionalInverse (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)
          (referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
            (harmonicFirstOrderLiftCompletion hF f)) : BallH1) := rfl

lemma referenceWeakHalfLiftFamily_weak_energy
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (lam : ℝ)
    (hs : UnitBallSmallDriftData (fun z => a (p,z))
      (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) lam)
    (f : SphereSobolev (1/2:ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun z => a (p,z)) (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) 0
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) (v : BallH1) = 0 := by
  let E : BallH1 := harmonicFirstOrderLiftCompletion hF f
  let R : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
    referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
  let A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
    referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
  let c : BallH1Zero := functionalInverse A (R E)
  have hA : IsCoercive A :=
    isCoercive_referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p lam hs
  have hAc : A c v = R E v := apply_functionalInverse A hA (R E) v
  have hrest : A c v = R (c : BallH1) v :=
    referenceWeakDirichletEnergyFamily_apply_reference g L y0 Φ B ε C ρ H a w hData hcalc p c v
  have hRc : R (c : BallH1) v = R E v := hrest.symm.trans hAc
  have hsub : R (E-(c : BallH1)) v = R E v-R (c : BallH1) v :=
    congrArg (fun ell : StrongDual ℝ BallH1Zero => ell v) (map_sub R E (c : BallH1))
  have hz : R (E-(c : BallH1)) v = 0 :=
    hsub.trans ((congrArg (fun t : ℝ => R E v-t) hRc).trans (sub_self (R E v)))
  have hlift : referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f =
      E-(c : BallH1) :=
    referenceWeakHalfLiftFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc hF p f
  have hRlift : R (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) v =
      R (E-(c : BallH1)) v := congrArg (fun U : BallH1 => R U v) hlift
  exact (referenceWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p
    (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) v).symm.trans
      (hRlift.trans hz)

lemma sphereHarmonicCoordinate_valueTraceL_referenceWeakHalfLiftFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (f : SphereSobolev (1/2:ℝ)) (k : ℕ) :
    sphereHarmonicCoordinate hO hD k
      (τ0.valueTraceL (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)) =
        sphereSobolevCoefficientL (1/2:ℝ) k f := by
  rw [referenceWeakHalfLiftFamily_apply,map_sub,valueTraceL_zeroDirichlet,sub_zero]
  exact sphereHarmonicCoordinate_valueTraceL_harmonicFirstOrderLiftCompletion hF hO hD τ0 k f

lemma eq_referenceWeakHalfLiftFamily_of_weak_energy
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (lam : ℝ)
    (hs : UnitBallSmallDriftData (fun z => a (p,z))
      (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) lam)
    (f : SphereSobolev (1/2:ℝ)) (U : BallH1)
    (hzero : harmonicFirstOrderLiftCompletion hF f-U ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2)
    (hweak : ∀ v : BallH1Zero,
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun z => a (p,z)) (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) 0 U (v : BallH1) = 0) :
    U = referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f := by
  have he := eq_sub_functionalInverse_of_restriction
    (referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)
    (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)
    (isCoercive_referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p lam hs)
    (referenceWeakDirichletEnergyFamily_apply_reference g L y0 Φ B ε C ρ H a w hData hcalc p)
    (harmonicFirstOrderLiftCompletion hF f) U hzero
    (fun v => (referenceWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p U v).trans (hweak v))
  exact he.trans
    (referenceWeakHalfLiftFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc hF p f).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
