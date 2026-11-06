import Calderon.ActualReferenceRotationStrongEnergy
import Calderon.ActualReferenceOrthogonalStrongWeakCoherence
import Calderon.NativeOrthogonalWeakSolution

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation
  NativeHarmonicLiftCompletion NativeHarmonicH1LiftCompletion NativeHarmonicLiftOrderCoherence
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
lemma sub_mem_nativeZero_of_common_difference (E U V : BallH1)
    (hU : E-U ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2)
    (hV : E-V ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2) :
    U-V ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  have he : U-V = (E-V)-(E-U) := by abel
  rw [he]
  exact (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).sub_mem hV hU

lemma nativeEnergyFormH1_eq_of_coefficients
    (a1 a2 : MatrixField) (b1 b2 : R3 → R3) (c1 c2 : R3 → ℝ)
    (ha : a1 = a2) (hb : b1 = b2) (hc : c1 = c2) (U V : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a1 b1 c1 U V =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a2 b2 c2 U V := by
  cases ha
  cases hb
  cases hc
  rfl

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


lemma referenceRotationHarmonicLiftFamily_half_boundary_difference
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hi : (referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    harmonicFirstOrderLiftCompletion hF (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) -
      TauCeti.Wkp.firstOrder 1 (referenceRotationHarmonicLiftFamily
        g L y0 Φ B ε C ρ H a w hData hcalc i j t (harmonicLiftCompletion hF f)) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  have hd := referenceRotationHarmonicLiftFamily_boundary_difference
    g L y0 Φ B ε C ρ H a w hData hcalc i j t hi (harmonicLiftCompletion hF f)
  change TauCeti.Wkp.firstOrderL 1 (harmonicLiftCompletion hF f -
    referenceRotationHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t
      (harmonicLiftCompletion hF f)) ∈ _ at hd
  rw [map_sub,firstOrder_harmonicLiftCompletion hF hO] at hd
  exact hd

lemma referenceOrthogonalStrongHarmonicLift_half_boundary_difference
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (τ0 : UnitBallValueTrace) (e : R3 ≃ₗᵢ[ℝ] R3) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    harmonicFirstOrderLiftCompletion hF (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) -
      TauCeti.Wkp.firstOrder 1 (referenceOrthogonalStrongHarmonicLift
        g L y0 Φ B ε C ρ H a w hData hcalc hF e p f) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  have hco := firstOrder_referenceOrthogonalStrongHarmonicLift_eq_nativeWeakHalfLift
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO τ0 e p hStrong hWeak f
  have hDiff := nativeWeakHalfLift_affine_difference
    (orthogonalPrincipalCoefficient e (fun z => a (p,z)))
    (orthogonalDriftCoefficient e (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)))
    ((0 : R3 → ℝ) ∘ e)
    (referenceOrthogonalNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData e p) hF
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)
  have hEq := congrArg (fun U : BallH1 =>
    harmonicFirstOrderLiftCompletion hF (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)-U ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2) hco
  exact Eq.mpr hEq hDiff

lemma referenceRotationHarmonicLiftFamily_orthogonal_weak_energy
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hRot : (referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j (θ,p)).IsInvertible)
    (E : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (orthogonalPrincipalCoefficient (coordinateRotationIsometry i j θ) (fun z => a (p,z)))
      (orthogonalDriftCoefficient (coordinateRotationIsometry i j θ)
        (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)))
      ((0 : R3 → ℝ) ∘ (coordinateRotationIsometry i j θ))
      (TauCeti.Wkp.firstOrder 1 (referenceRotationHarmonicLiftFamily
        g L y0 Φ B ε C ρ H a w hData hcalc i j (θ,p) E)) (v : BallH1) = 0 := by
  let e := coordinateRotationIsometry i j θ
  have hA : (fun x => coordinateRotationPrincipalFamily i j a ((θ,p),x)) =
      orthogonalPrincipalCoefficient e (fun x => a (p,x)) :=
    funext (coordinateRotationPrincipalFamily_eq_orthogonal i j a θ p)
  have hB : (fun x => coordinateRotationDriftFamily i j
      (conformalReferenceWeightedFramedDrift g L Φ H w) ((θ,p),x)) =
      orthogonalDriftCoefficient e (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) :=
    funext (coordinateRotationDriftFamily_eq_orthogonal i j _ θ p)
  have hC : (0 : R3 → ℝ) = ((0 : R3 → ℝ) ∘ e) := by
    funext x
    rfl
  have hScalar := nativeEnergyFormH1_eq_of_coefficients _ _ _ _ _ _ hA hB hC
    (TauCeti.Wkp.firstOrder 1 (referenceRotationHarmonicLiftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j (θ,p) E)) (v : BallH1)
  exact hScalar.symm.trans (referenceRotationHarmonicLiftFamily_weak_energy
    g L y0 Φ B ε C ρ H a w hData hcalc i j (θ,p) hRot E v)

lemma referenceRotationHarmonicLiftFamily_eq_orthogonalStrongLift
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (τ0 : UnitBallValueTrace) (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (hRot : (referenceRotationStrongDirichletFamily g L y0 Φ B ε C ρ H a w hData hcalc i j (θ,p)).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    referenceRotationHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j (θ,p)
      (harmonicLiftCompletion hF f) =
    referenceOrthogonalStrongHarmonicLift g L y0 Φ B ε C ρ H a w hData
      hcalc hF (coordinateRotationIsometry i j θ) p f := by
  let e := coordinateRotationIsometry i j θ
  let U : BallSobolev 2 := referenceRotationHarmonicLiftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j (θ,p) (harmonicLiftCompletion hF f)
  let V : BallSobolev 2 := referenceOrthogonalStrongHarmonicLift
    g L y0 Φ B ε C ρ H a w hData hcalc hF e p f
  let E : BallH1 := harmonicFirstOrderLiftCompletion hF
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f)
  have hU : E-TauCeti.Wkp.firstOrder 1 U ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    referenceRotationHarmonicLiftFamily_half_boundary_difference
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO i j (θ,p) hRot f
  have hV : E-TauCeti.Wkp.firstOrder 1 V ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 :=
    referenceOrthogonalStrongHarmonicLift_half_boundary_difference
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO τ0 e p hStrong hWeak f
  have hz := sub_mem_nativeZero_of_common_difference E
    (TauCeti.Wkp.firstOrder 1 U) (TauCeti.Wkp.firstOrder 1 V) hU hV
  have hEq := eq_of_native_weak_solution_of_isInvertible
    (orthogonalPrincipalCoefficient e (fun x => a (p,x)))
    (orthogonalDriftCoefficient e (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)))
    ((0 : R3 → ℝ) ∘ e)
    (referenceOrthogonalNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData e p)
    (referenceOrthogonalNativeEnergy_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc e p hWeak)
    (TauCeti.Wkp.firstOrder 1 U) (TauCeti.Wkp.firstOrder 1 V) hz
    (fun z => referenceRotationHarmonicLiftFamily_orthogonal_weak_energy
      g L y0 Φ B ε C ρ H a w hData hcalc i j θ p hRot (harmonicLiftCompletion hF f) z)
    (fun z => referenceOrthogonalStrongHarmonicLift_weak_solution
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO τ0 e p hStrong hWeak f z)
  exact nativeH2_firstOrder_injective hEq

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationHarmonicLiftFamily_half_boundary_difference
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationHarmonicLiftFamily_eq_orthogonalStrongLift

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sub_mem_nativeZero_of_common_difference

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeEnergyFormH1_eq_of_coefficients

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceOrthogonalStrongHarmonicLift_half_boundary_difference

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationHarmonicLiftFamily_orthogonal_weak_energy
