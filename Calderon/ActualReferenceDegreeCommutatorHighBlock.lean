import Calderon.SphereSobolevSingleOrderEqualityDiagnostic
import Calderon.SphereSobolevShiftedPhysicalDegree
import Calderon.ActualReferenceRadialRotationCommutatorMidpointCasimirBlock
import Calderon.ActualReferenceRadialEndpointOpenLocus
set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic
/-! Raw [N,Λ] high graph, physical coefficient degree m−n, actual lower/upper radial endpoint pair. -/
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)


def referenceRadialDegreeCommutatorHighL (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (sphereSobolevShiftedDegreeL (1/2:ℝ)).comp (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) -
    (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp (sphereSobolevShiftedDegreeL (3/2:ℝ))

attribute [local irreducible] referenceSharpRadialTraceFamily referenceLowerRadialEndpointFamily
  sphereSobolevShiftedDegreeL sphereSobolevSingleL sphereSobolevCoefficientL sphereSobolevInclusionL

lemma referenceRadialDegreeCommutatorHighL_physical_harmonic_block
    (p : ℝ × (R3 × ℝ)) (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (m n : ℕ) (u : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p (sphereSobolevSingleL (3/2:ℝ) n u)) =
    ((m:ℝ)-(n:ℝ)) • referenceSharpRadialHarmonicBlockL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p m n u := by
  let X := referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p (sphereSobolevSingleL (3/2:ℝ) n u)
  let K := sphereSobolevCoefficientL (1/2:ℝ) m X
  have hHalf : (1/2:ℝ)-1=-(1/2:ℝ) := by norm_num
  have hThree : (3/2:ℝ)-1=(1/2:ℝ) := by norm_num
  have hOrder : sphereSobolevCoefficientL (-(1/2:ℝ)) m (sphereSobolevShiftedDegreeL (1/2:ℝ) X) =
      sphereSobolevCoefficientL ((1/2:ℝ)-1) m (sphereSobolevShiftedDegreeL (1/2:ℝ) X) :=
    congrArg (fun s : ℝ => sphereSobolevCoefficientL s m (sphereSobolevShiftedDegreeL (1/2:ℝ) X)) hHalf.symm
  have hFirst : sphereSobolevCoefficientL (-(1/2:ℝ)) m (sphereSobolevShiftedDegreeL (1/2:ℝ) X) = (m:ℝ) • K :=
    hOrder.trans (sphereSobolevCoefficientL_shiftedDegree (1/2:ℝ) m X)
  have hSingleOrder : sphereSobolevSingleL ((3/2:ℝ)-1) n u = sphereSobolevSingleL (1/2:ℝ) n u :=
    sphereSobolevSingleL_eq_of_order_eq ((3/2:ℝ)-1) (1/2:ℝ) hThree n u
  have hNInput : sphereSobolevShiftedDegreeL (3/2:ℝ) (sphereSobolevSingleL (3/2:ℝ) n u) =
      (n:ℝ) • sphereSobolevSingleL (1/2:ℝ) n u :=
    (sphereSobolevShiftedDegreeL_single (3/2:ℝ) n u).trans
      (congrArg (fun z : SphereSobolev (1/2:ℝ) => (n:ℝ) • z) hSingleOrder)
  have hCompat := congrArg
    (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T (sphereSobolevSingleL (3/2:ℝ) n u))
    (referenceSharpRadialTraceFamily_lower_compatibility_on_locus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp)
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_single] at hCompat
  have hLower : sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p (sphereSobolevSingleL (1/2:ℝ) n u)) = K :=
    (congrArg (sphereSobolevCoefficientL (-(1/2:ℝ)) m) hCompat.symm).trans
      (sphereSobolevCoefficientL_inclusion (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) X m)
  have hSecond : sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p (sphereSobolevShiftedDegreeL (3/2:ℝ) (sphereSobolevSingleL (3/2:ℝ) n u))) = (n:ℝ) • K := by
    have hValue := (congrArg (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) hNInput).trans
      ((referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).map_smul (n:ℝ) (sphereSobolevSingleL (1/2:ℝ) n u))
    exact (congrArg (sphereSobolevCoefficientL (-(1/2:ℝ)) m) hValue).trans
      (((sphereSobolevCoefficientL (-(1/2:ℝ)) m).map_smul (n:ℝ) _).trans
        (congrArg (fun z : harmonicSphereSubspace m => (n:ℝ) • z) hLower))
  have hRaw : referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p (sphereSobolevSingleL (3/2:ℝ) n u) =
      sphereSobolevShiftedDegreeL (1/2:ℝ) X -
        referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p (sphereSobolevShiftedDegreeL (3/2:ℝ) (sphereSobolevSingleL (3/2:ℝ) n u)) := rfl
  calc
    _ = (m:ℝ) • K - (n:ℝ) • K :=
      (congrArg (sphereSobolevCoefficientL (-(1/2:ℝ)) m) hRaw).trans
        (((sphereSobolevCoefficientL (-(1/2:ℝ)) m).map_sub _ _).trans
          (congrArg₂ (fun z w : harmonicSphereSubspace m => z-w) hFirst hSecond))
    _ = ((m:ℝ)-(n:ℝ)) • K := (sub_smul _ _ K).symm
    _ = _ := rfl
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialDegreeCommutatorHighL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialDegreeCommutatorHighL_physical_harmonic_block
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
