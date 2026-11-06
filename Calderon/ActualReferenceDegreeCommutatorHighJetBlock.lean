import Calderon.ActualReferenceDegreeCommutatorHighBlock
import Calderon.ActualReferenceRadialEndpointInvertibleTopology
import Calderon.PhysicalLinearIdentityJetTransport
set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal ContDiff InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic RotationCasimirJetTransport
/-! Full upfront: EXPANSION-v001.json. Raw actual degree graph differentiated
from ORIGINAL compatibility, not assumed as a jet identity. -/
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)


attribute [local irreducible] referenceSharpRadialTraceFamily referenceLowerRadialEndpointFamily
  sphereSobolevShiftedDegreeL sphereSobolevSingleL sphereSobolevCoefficientL

lemma contDiffAt_referenceRadialDegreeCommutatorHighL
    (p : ℝ × (R3 × ℝ)) (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) p := by
  have hSharp := contDiffAt_referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp.1
  have hLower := contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp.2.2 hp.2.1
  unfold referenceRadialDegreeCommutatorHighL
  exact (contDiffAt_const.clm_comp hSharp).sub (hLower.clm_comp contDiffAt_const)

lemma referenceRadialDegreeCommutatorHighL_physical_harmonic_jet_block
    (p : ℝ × (R3 × ℝ)) (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (m n : ℕ) (u : harmonicSphereSubspace n) (k : ℕ) (d : Fin k → ℝ × (R3 × ℝ)) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m
      ((iteratedFDeriv ℝ k (referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) p d) (sphereSobolevSingleL (3/2:ℝ) n u)) =
    ((m:ℝ)-(n:ℝ)) • sphereSobolevCoefficientL (1/2:ℝ) m
      ((iteratedFDeriv ℝ k (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) p d) (sphereSobolevSingleL (3/2:ℝ) n u)) := by
  apply ext_inner_right ℝ
  intro v
  let Lop : (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) →L[ℝ] ℝ :=
    (innerSLFlip ℝ v).comp ((sphereSobolevCoefficientL (-(1/2:ℝ)) m).comp
      (ContinuousLinearMap.apply ℝ (SphereSobolev (-(1/2:ℝ))) (sphereSobolevSingleL (3/2:ℝ) n u)))
  let Rop : (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) →L[ℝ] ℝ :=
    ((m:ℝ)-(n:ℝ)) • ((innerSLFlip ℝ v).comp ((sphereSobolevCoefficientL (1/2:ℝ) m).comp
      (ContinuousLinearMap.apply ℝ (SphereSobolev (1/2:ℝ)) (sphereSobolevSingleL (3/2:ℝ) n u))))
  have hIdentity : ∀ q ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0, Lop (referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q) = Rop (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q) := by
    intro q hq
    have hBlock := referenceRadialDegreeCommutatorHighL_physical_harmonic_block g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q hq m n u
    have hInner := congrArg (fun z : harmonicSphereSubspace m => ⟪z,v⟫_ℝ) hBlock
    exact hInner.trans (real_inner_smul_left (referenceSharpRadialHarmonicBlockL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q m n u) v ((m:ℝ)-(n:ℝ)))
  have hJet := iteratedFDeriv_linear_scalar_identity
    (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    p hp (referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) Lop Rop
    (contDiffAt_referenceRadialDegreeCommutatorHighL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp)
    (contDiffAt_referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp.1) hIdentity k d
  exact hJet.trans (real_inner_smul_left
    (sphereSobolevCoefficientL (1/2:ℝ) m
      ((iteratedFDeriv ℝ k (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) p d) (sphereSobolevSingleL (3/2:ℝ) n u)))
        v ((m:ℝ)-(n:ℝ))).symm
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceRadialDegreeCommutatorHighL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialDegreeCommutatorHighL_physical_harmonic_jet_block
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
