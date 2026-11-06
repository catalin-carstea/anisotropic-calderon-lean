import Calderon.ActualReferenceFullWeakEnergy
import Calderon.ActualReferenceWeakHalfLift
import Calderon.SphereSobolevDualRiesz
import Calderon.NativeSmoothSharpTraceCompletion

/-! Actual normalized weak conormal endpoint. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion
  NativePolynomialBulkMoments NativeSmoothSharpTraceCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceWeakConormalEndpointFunctionalFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2:ℝ) →L[ℝ] StrongDual ℝ (SphereSobolev (1/2:ℝ)) :=
  sphereSurfaceMass⁻¹ •
    (((ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) BallH1 ℝ).flip
      (harmonicFirstOrderLiftCompletion hF)).comp
      ((referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).comp (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p)))

lemma referenceWeakConormalEndpointFunctionalFamily_apply
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ))
    (f z : SphereSobolev (1/2:ℝ)) :
    referenceWeakConormalEndpointFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f z = sphereSurfaceMass⁻¹ *
      referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) (harmonicFirstOrderLiftCompletion hF z) := rfl

def referenceWeakConormalEndpointFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (sphereSobolevDualRieszL (1/2:ℝ)).comp (referenceWeakConormalEndpointFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p)

lemma sphereSobolevDualPairing_referenceWeakConormalEndpointFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ))
    (f z : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) z (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) =
      sphereSurfaceMass⁻¹ * referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) (harmonicFirstOrderLiftCompletion hF z) :=
  (sphereSobolevDualPairing_dualRiesz (1/2:ℝ) (referenceWeakConormalEndpointFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) z).trans
    (referenceWeakConormalEndpointFunctionalFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc hF p f z)

lemma sphereSobolevCoefficientL_referenceWeakConormalEndpointFamily_inner
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ))
    (f : SphereSobolev (1/2:ℝ)) (k : ℕ) (z : harmonicSphereSubspace k) :
    ⟪sphereSobolevCoefficientL (-(1/2:ℝ)) k (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f),z⟫_ℝ =
      sphereSurfaceMass⁻¹ * referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
        (harmonicFirstOrderLiftCompletion hF (sphereSobolevSingleL (1/2:ℝ) k z)) :=
  (sphereSobolevCoefficientL_dualRiesz_inner (1/2:ℝ) (referenceWeakConormalEndpointFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) k z).trans
    (referenceWeakConormalEndpointFunctionalFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc hF p f
      (sphereSobolevSingleL (1/2:ℝ) k z))

lemma referenceWeakConormalEndpointFamily_energy
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ))
    (f z : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) z (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) =
      sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1
        (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
        (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) (harmonicFirstOrderLiftCompletion hF z) :=
  (sphereSobolevDualPairing_referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f z).trans
    (congrArg (fun t : ℝ => sphereSurfaceMass⁻¹*t)
      (referenceFullWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p
        (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) (harmonicFirstOrderLiftCompletion hF z)))

lemma norm_referenceWeakConormalEndpointFamily_le
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ)) :
    ‖referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p‖ ≤
      sphereSurfaceMass⁻¹ * ‖harmonicFirstOrderLiftCompletion hF‖ * ‖referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p‖ * ‖referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p‖ := by
  let Q : BallH1 →L[ℝ] StrongDual ℝ BallH1 := referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
  let V : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 := referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p
  let P : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 := harmonicFirstOrderLiftCompletion hF
  have hm : 0 ≤ sphereSurfaceMass⁻¹ := inv_nonneg.mpr sphereSurfaceMass_pos.le
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖sphereSobolevDualRieszL (1/2:ℝ) (referenceWeakConormalEndpointFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)‖ ≤ _
  rw [norm_sphereSobolevDualRieszL_apply]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  have he : referenceWeakConormalEndpointFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f z = sphereSurfaceMass⁻¹ * Q (V f) (P z) :=
    referenceWeakConormalEndpointFunctionalFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc hF p f z
  have hb : ‖Q (V f) (P z)‖ ≤ (‖Q‖*(‖V‖*‖f‖))*(‖P‖*‖z‖) := by
    calc
      _ ≤ ‖Q (V f)‖*‖P z‖ := (Q (V f)).le_opNorm (P z)
      _ ≤ (‖Q‖*‖V f‖)*(‖P‖*‖z‖) :=
        mul_le_mul (Q.le_opNorm (V f)) (P.le_opNorm z) (norm_nonneg _) (by positivity)
      _ ≤ _ := by gcongr; exact V.le_opNorm f
  have hn : ‖referenceWeakConormalEndpointFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f z‖ ≤
      sphereSurfaceMass⁻¹*((‖Q‖*(‖V‖*‖f‖))*(‖P‖*‖z‖)) := by
    calc
      _ = ‖sphereSurfaceMass⁻¹ * Q (V f) (P z)‖ := congrArg norm he
      _ = sphereSurfaceMass⁻¹ * ‖Q (V f) (P z)‖ := by
        have hscalar (t : ℝ) : ‖sphereSurfaceMass⁻¹ * t‖ = sphereSurfaceMass⁻¹ * ‖t‖ := by
          rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hm]
        exact hscalar (Q (V f) (P z))
      _ ≤ _ := mul_le_mul_of_nonneg_left hb hm
  change ‖referenceWeakConormalEndpointFunctionalFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f z‖ ≤
    (sphereSurfaceMass⁻¹ * ‖P‖ * ‖Q‖ * ‖V‖) * ‖f‖ * ‖z‖
  exact hn.trans_eq (by ring)

lemma referenceWeakConormalEndpointFamily_test_zero_add
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (lam : ℝ)
    (hs : UnitBallSmallDriftData (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) lam)
    (f z : SphereSobolev (1/2:ℝ)) (v : BallH1Zero) :
    sphereSurfaceMass⁻¹ * referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) (harmonicFirstOrderLiftCompletion hF z+(v : BallH1)) =
      sphereSobolevDualPairing (1/2:ℝ) z (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) := by
  let ell : StrongDual ℝ BallH1 := referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
  have hz : ell (v : BallH1) = 0 :=
    (referenceFullWeakEnergyFamily_apply_zero g L y0 Φ B ε C ρ H a w hData hcalc p (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) v).trans
      ((referenceWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) v).trans
        (referenceWeakHalfLiftFamily_weak_energy g L y0 Φ B ε C ρ H a w hData hcalc hF p lam hs f v))
  have ha : ell (harmonicFirstOrderLiftCompletion hF z+(v : BallH1)) = ell (harmonicFirstOrderLiftCompletion hF z) :=
    (map_add ell (harmonicFirstOrderLiftCompletion hF z) (v : BallH1)).trans
      ((congrArg (fun t : ℝ => ell (harmonicFirstOrderLiftCompletion hF z)+t) hz).trans (add_zero _))
  exact (congrArg (fun t : ℝ => sphereSurfaceMass⁻¹*t) ha).trans
    (sphereSobolevDualPairing_referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f z).symm

lemma referenceWeakConormalEndpointFamily_coefficient_pairing
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ))
    (f z : SphereSobolev (1/2:ℝ)) :
    (∑' k : ℕ, ⟪sphereSobolevCoefficientL (1/2:ℝ) k z,
      sphereSobolevCoefficientL (-(1/2:ℝ)) k
        (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)⟫_ℝ) =
      sphereSurfaceMass⁻¹ * referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
        (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
        (harmonicFirstOrderLiftCompletion hF z) :=
  (sphereSobolevDualPairing_eq_tsum (1/2:ℝ) z
    (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)).symm.trans
      (sphereSobolevDualPairing_referenceWeakConormalEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF p f z)

lemma referenceWeakConormalEndpointFamily_extension_independent
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (lam : ℝ)
    (hs : UnitBallSmallDriftData (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) lam)
    (f z : SphereSobolev (1/2:ℝ)) (V : BallH1)
    (hzero : V - harmonicFirstOrderLiftCompletion hF z ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2) :
    sphereSurfaceMass⁻¹ * referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
      (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) V =
      sphereSobolevDualPairing (1/2:ℝ) z
        (referenceWeakConormalEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) := by
  let v : BallH1Zero := ⟨V - harmonicFirstOrderLiftCompletion hF z, hzero⟩
  have hV : harmonicFirstOrderLiftCompletion hF z + (v : BallH1) = V := by
    change harmonicFirstOrderLiftCompletion hF z +
      (V - harmonicFirstOrderLiftCompletion hF z) = V
    abel
  calc
    _ = sphereSurfaceMass⁻¹ * referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
        (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f)
        (harmonicFirstOrderLiftCompletion hF z + (v : BallH1)) :=
      congrArg (fun U : BallH1 => sphereSurfaceMass⁻¹ *
        referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p
          (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f) U) hV.symm
    _ = _ := referenceWeakConormalEndpointFamily_test_zero_add
      g L y0 Φ B ε C ρ H a w hData hcalc hF p lam hs f z v

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakConormalEndpointFunctionalFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakConormalEndpointFunctionalFamily_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakConormalEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceWeakConormalEndpointFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevCoefficientL_referenceWeakConormalEndpointFamily_inner
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakConormalEndpointFamily_energy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_referenceWeakConormalEndpointFamily_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakConormalEndpointFamily_test_zero_add
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakConormalEndpointFamily_coefficient_pairing
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakConormalEndpointFamily_extension_independent
